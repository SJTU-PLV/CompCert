(** * The semantics of relocatable program using only the symbol table *)

(** The key feature of this semantics: it uses mappings from the ids
    of global symbols to memory locations in deciding their memory
    addresses. These mappings are caculated by using the symbol table.
    *)

Require Import Coqlib Maps AST Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgram Globalenvs.
Require Import Locations Stacklayout Conventions.
Require Import Linking Errors.
Require Import LocalLib.
Require Import RelocProgGlobalenvs RelocProgSemanticsArchi.

Remark in_norepet_unique_r:
  forall T (gl: list (ident * T)) id g,
  In (id, g) gl -> list_norepet (map fst gl) ->
  exists gl1 gl2, gl = gl1 ++ (id, g) :: gl2 /\ ~In id (map fst gl2).
Proof.
  induction gl as [|[id1 g1] gl]; simpl; intros.
  contradiction.
  inv H0. destruct H.
  inv H. exists nil, gl. auto.
  exploit IHgl; eauto. intros (gl1 & gl2 & X & Y).
  exists ((id1, g1) :: gl1), gl2; split;auto. rewrite X; auto.
Qed.

Section WITH_INSTR_SIZE.
  Variable instr_size : instruction -> Z.
  Let exec_instr:= exec_instr instr_size.
  
(** Small step semantics *)

(* I think it is almost the same in all architectures*)

Inductive step (ge: Genv.t) : state -> trace -> state -> Prop :=
| exec_step_internal:
    forall b ofs i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_ext_funct ge (Vptr b ofs) = None ->
      Genv.find_instr ge (Vptr b ofs) = Some i ->
      exec_instr ge i rs m = Next rs' m' ->
      step ge (State rs m) E0 (State rs' m')
| exec_step_builtin:
    forall b ofs ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_ext_funct ge (Vptr b ofs) = None ->
      Genv.find_instr ge (Vptr b ofs) = Some (Pbuiltin ef args res)  ->
      eval_builtin_args preg ge rs (rs RSP) m args vargs ->
      external_call ef (Genv.genv_senv ge) vargs m t vres m' ->
      rs' = nextinstr_nf (Ptrofs.repr (instr_size (Pbuiltin ef args res)))
                         (set_res res vres
                                  (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
        step ge (State rs m) t (State rs' m')
| exec_step_external:
    forall b ofs ef args res rs m t rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_ext_funct ge (Vptr b ofs) = Some ef ->
      forall ra (LOADRA: Mem.loadv Mptr m (rs RSP) = Some ra)
        (RA_NOT_VUNDEF: ra <> Vundef)
        (ARGS: extcall_arguments (rs # RSP <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr)))) m (ef_sig ef) args),
        external_call ef (Genv.genv_senv ge) args m t res m' ->
          rs' = (set_pair (loc_external_result (ef_sig ef)) res
                          (undef_caller_save_regs rs))
                  #PC <- ra
                  #RA <- Vundef
                  #RSP <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr))) ->
        step ge (State rs m) t (State rs' m').

(** Initialization of the global environment *)
Definition gen_global (id:ident) (e:symbentry) : (block*ptrofs) :=
  match e.(symbentry_secindex) with
  | secindex_normal sec =>
    (Global sec, Ptrofs.repr e.(symbentry_value))
  | _ =>
    (Global id, Ptrofs.zero)
  end.

Definition gen_symb_map (symbtbl: symbtable) : PTree.t (block * ptrofs) :=
  PTree.map gen_global symbtbl.


Definition acc_instr_map r (i:instruction) :=
  let '(ofs, map) := r in
  let map' := fun o => if Ptrofs.eq_dec ofs o then Some i else (map o) in
  let ofs' := Ptrofs.add ofs (Ptrofs.repr (instr_size i)) in
  (ofs', map').

Definition gen_instr_map (c:code) :=
  let '(_, map) := fold_left acc_instr_map c (Ptrofs.zero, fun o => None) in
  map.

Definition acc_code_map {D: Type} r (id:ident) (sec:RelocProg.section instruction D) :=
  match sec with
  | sec_text c =>
    NMap.set _ (Global id) (gen_instr_map c) r
  | _ => r
  end.

Definition gen_code_map {D: Type} (sectbl: RelocProg.sectable instruction D) :=
  PTree.fold acc_code_map sectbl (NMap.init _ (fun o => None)).

Definition acc_extfuns (idg: ident * gdef) extfuns :=
  let '(id, gdef) := idg in
  match gdef with
  | Gfun (External ef) => NMap.set  _ (Global id) (Some ef) extfuns
  | _ => extfuns
  end.

Definition gen_extfuns (idgs: list (ident * gdef)) :=
  fold_right acc_extfuns (NMap.init _ None) idgs.

Lemma PTree_Properteis_of_list_get_extfuns : forall defs i f,
    list_norepet (map fst defs) ->
    (PTree_Properties.of_list defs) ! i = (Some (Gfun (External f))) ->
    (gen_extfuns defs) (Global i) = Some f.
Proof.
  induction defs as [|def defs].
  - cbn. intros. rewrite PTree.gempty in H0. congruence.
  - intros i f NORPT OF. destruct def as (id, def).
    inv NORPT.
    destruct (ident_eq id i).
    + subst. erewrite PTree_Properties_of_list_cons in OF; auto.
      inv OF. cbn. rewrite NMap.gss. auto.
    + erewrite PTree_Properties_of_list_tail in OF; eauto.
      cbn. repeat (destr; eauto; subst).
      erewrite NMap.gso;auto.
      unfold not. intros. inv H;congruence.
Qed.

Definition globalenv {D: Type} (p: RelocProg.program fundef unit instruction D) : Genv.t :=
  let symbmap := gen_symb_map (prog_symbtable p) in
  let imap := gen_code_map (prog_sectable p) in
  let extfuns := gen_extfuns p.(prog_defs) in
  Genv.mkgenv symbmap extfuns imap p.(prog_senv).

Lemma gen_instr_map_inv_aux: forall n c ofs i ofs1 m1,
    length c = n ->
    fold_left acc_instr_map c
              (Ptrofs.zero, fun _ : ptrofs => None) = (ofs1,m1) ->
    m1 ofs = Some i ->
    In i c.
Proof.
  induction n;intros.
  rewrite length_zero_iff_nil in H. subst.
  simpl in H0. inv H0.  inv H1.
  
  exploit LocalLib.length_S_inv;eauto.
  intros (l' & a1 & A1 & B1). subst.
  clear H.
  rewrite fold_left_app in H0. simpl in H0.
  destruct ((fold_left acc_instr_map l'
            (Ptrofs.zero, fun _ : ptrofs => None))) eqn: FOLD.
  unfold acc_instr_map in H0 at 1. inv H0.
  destr_in H1.
  + inv H1. apply in_app.
    right. constructor. auto.
  +  apply in_app. left. eapply IHn;eauto.
Qed.

Lemma gen_instr_map_inv: forall c ofs i,
    gen_instr_map c ofs = Some i ->
    In i c.
Proof.
  unfold gen_instr_map. intros.
  destruct (fold_left acc_instr_map c (Ptrofs.zero, fun _ : ptrofs => None)) eqn: FOLD.
  eapply gen_instr_map_inv_aux;eauto.
Qed.


(* code map = code *)
Lemma gen_code_map_inv: forall D (sectbl : RelocProg.sectable instruction D) b ofs i,
    (gen_code_map sectbl) b ofs = Some i ->
    (exists id c, b = Global id /\ sectbl ! id = Some (sec_text c) /\ In i c).
Proof.
  unfold gen_code_map. intros.
  rewrite PTree.fold_spec in H.
  assert (exists id c, b = Global id /\ In (id, sec_text c) (PTree.elements sectbl) /\ In i c).
  { set (l:= (PTree.elements sectbl)) in *.
    generalize H.
    generalize l i ofs b.
    clear H l i ofs b. clear sectbl.
    intro l.
    assert (LEN: exists n, length l = n).
    { induction l. exists O. auto.
      destruct IHl.
      eexists. simpl. auto. }

    destruct LEN. generalize x l H.
    clear H x l.
    induction x;intros.
    rewrite length_zero_iff_nil in H. subst.
    simpl in H0. rewrite NMap.gi in H0. inv H0.

    exploit LocalLib.length_S_inv;eauto.
    intros (l' & a1 & A1 & B1). subst.
    clear H.
    rewrite fold_left_app in H0.
    simpl in H0. destruct a1. simpl in *.
    destruct (eq_block (Global p) b);subst.
    - destruct s;simpl in H0.
      + rewrite NMap.gss in H0.
        exists p, code. split;eauto.
        rewrite in_app_iff. split. right. constructor.
        auto. eapply gen_instr_map_inv. eauto.
      + eapply IHx in H0;eauto.
        destruct H0 as (id & c & P1 & P2 & P3).
        inv P1. exists id,c.
        split;auto. split;auto.
        apply in_app.
        left. auto.
      + eapply IHx in H0;eauto.
        destruct H0 as (id & c & P1 & P2 & P3).
        inv P1. exists id,c.
        split;auto. split;auto.
        apply in_app.
        left. auto.
    - destruct s;simpl in H0.
      + rewrite NMap.gso in H0;auto.
        eapply IHx in H0;eauto.
        destruct H0 as (id & c & P1 & P2 & P3).
        inv P1. exists id,c.
        split;auto. split;auto.
        apply in_app.
        left. auto.
      + eapply IHx in H0;eauto.
        destruct H0 as (id & c & P1 & P2 & P3).
        inv P1. exists id,c.
        split;auto. split;auto.
        apply in_app.
        left. auto.
      + eapply IHx in H0;eauto.
        destruct H0 as (id & c & P1 & P2 & P3).
        inv P1. exists id,c.
        split;auto. split;auto.
        apply in_app.
        left. auto.   }
  destruct H0 as (id & c & P1 & P2 & P3).
  exists id,c. split;auto. split;auto.
  apply PTree.elements_complete.
  auto.
Qed.

        
(** Initialization of memory *)
Section WITHGE1.

Variable ge:Genv.t.

Definition store_init_data (m: mem) (b: block) (p: Z) (id: init_data) : option mem :=
  match id with
  | Init_int8 n => Mem.store Mint8unsigned m b p (Vint n)
  | Init_int16 n => Mem.store Mint16unsigned m b p (Vint n)
  | Init_int32 n => Mem.store Mint32 m b p (Vint n)
  | Init_int64 n => Mem.store Mint64 m b p (Vlong n)
  | Init_float32 n => Mem.store Mfloat32 m b p (Vsingle n)
  | Init_float64 n => Mem.store Mfloat64 m b p (Vfloat n)
  | Init_addrof gloc ofs => Mem.store Mptr m b p (Genv.symbol_address ge gloc ofs)
  (* store zero to common data, which simplify the relocbingenproof, but make symbtablegenproof harder *)
  | Init_space n => store_zeros m b p (Z.max n 0)
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

Definition alloc_external_comm_symbol (r: option mem) (id: ident) (e:symbentry): option mem :=
  match r with
  | None => None
  | Some m =>
  match symbentry_type e with
  | symb_notype => None
  (* impossible *)
  (* match symbentry_secindex e with *)
    (* | secindex_undef => *)
    (*   let (m1, b) := Mem.alloc_glob id m 0 0 in Some m1 *)
    (* | _ => None *)
    (* end *)
  | symb_func =>
    match symbentry_secindex e with
    | secindex_undef =>
      let (m1, b) := Mem.alloc_glob id m 0 1 in
      Mem.drop_perm m1 b 0 1 Nonempty
    | secindex_comm =>
      None (**r Impossible *)
    | secindex_normal _ => Some m
    end
  | symb_data =>
    match symbentry_secindex e with
    | secindex_undef =>
      let sz := symbentry_size e in
      let (m1, b) := Mem.alloc_glob id m 0 sz in
      match store_zeros m1 b 0 sz with
      | None => None
      | Some m2 =>
        Mem.drop_perm m2 b 0 sz Nonempty
      end        
    | secindex_comm =>
      let sz := symbentry_size e in
      let (m1, b) := Mem.alloc_glob id m 0 sz in
      match store_zeros m1 b 0 sz with
      | None => None
      | Some m2 =>
       (* writable for common symbol *)
        Mem.drop_perm m2 b 0 sz Writable
      end        
    | secindex_normal _ => Some m
    end
  end
end.

Definition alloc_external_symbols (m: mem) (t: symbtable) : option mem :=
  PTree.fold alloc_external_comm_symbol t (Some m).


Definition alloc_section (r: option mem) (id: ident) (sec: section) : option mem :=
  match r with
  | None => None
  | Some m =>
    let sz := sec_size instr_size sec in
    match sec with
      | sec_rwdata init =>
        let '(m1, b) := Mem.alloc_glob id m 0 sz in
        match store_zeros m1 b 0 sz with
        | None => None
        | Some m2 =>
          match store_init_data_list m2 b 0 init with
          | None => None
          | Some m3 => Mem.drop_perm m3 b 0 sz Writable
          end       
        end
      | sec_rodata init =>
        let '(m1, b) := Mem.alloc_glob id m 0 sz in
        match store_zeros m1 b 0 sz with
        | None => None
        | Some m2 =>
          match store_init_data_list m2 b 0 init with
          | None => None
          | Some m3 => Mem.drop_perm m3 b 0 sz Readable
          end
        end
      | sec_text code =>        
        let (m1, b) := Mem.alloc_glob id m 0 sz in
        Mem.drop_perm m1 b 0 sz Nonempty
    end
  end.

Definition alloc_sections (sectbl: sectable) (m:mem) :option mem :=
  PTree.fold alloc_section sectbl (Some m).

(** init data to bytes *)
Definition bytes_of_init_data (i: init_data): list memval :=
  match i with
  | Init_int8 n => inj_bytes (encode_int 1%nat (Int.unsigned n))
  | Init_int16 n => inj_bytes (encode_int 2%nat (Int.unsigned n))
  | Init_int32 n => inj_bytes (encode_int 4%nat (Int.unsigned n))
  | Init_int64 n => inj_bytes (encode_int 8%nat (Int64.unsigned n))
  | Init_float32 n => inj_bytes (encode_int 4%nat (Int.unsigned (Float32.to_bits n)))
  | Init_float64 n => inj_bytes (encode_int 8%nat (Int64.unsigned (Float.to_bits n)))
  | Init_space n => list_repeat (Z.to_nat n) (Byte Byte.zero)
  | Init_addrof id ofs =>
      match Genv.find_symbol ge id with
      | Some (b,ofs') => inj_value (if Archi.ptr64 then Q64 else Q32) (Vptr b (Ptrofs.add ofs ofs'))
      | None   => list_repeat (if Archi.ptr64 then 8%nat else 4%nat) Undef
      end
  end.

Fixpoint bytes_of_init_data_list (il: list init_data): list memval :=
  match il with
  | nil => nil
  | i :: il => bytes_of_init_data i ++ bytes_of_init_data_list il
  end.

(** load_store_init_data *)
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
      (exists b' ofs', Genv.find_symbol ge symb = Some (b',ofs') /\ Mem.load Mptr m b p = Some(Vptr b' (Ptrofs.add ofs ofs')))
      /\ load_store_init_data m b (p + size_chunk Mptr) il'
  | Init_space n :: il' =>
      Globalenvs.Genv.read_as_zero m b p n
      /\ load_store_init_data m b (p + Z.max n 0) il'
  end.


End WITHGE1.


(** globals_initialized *)
Definition globals_initialized (ge: Genv.t) (prog: program) (m:mem):=
  forall id b,
    b = Global id ->
    match prog.(prog_sectable) ! id with
    | Some sec =>
      match sec with
      | sec_text code =>
        Mem.perm m b 0 Cur Nonempty /\
        let sz := code_size instr_size code in
        (forall ofs k p, Mem.perm m b ofs k p -> 0 <= ofs < sz /\ p = Nonempty)
      | sec_rodata data =>        
        let sz := (init_data_list_size data) in
        Mem.range_perm m b 0 sz Cur Readable /\ (forall ofs k p, Mem.perm m b ofs k p -> 0 <= ofs < sz /\ perm_order Readable p)
        /\ load_store_init_data ge m b 0 data
        /\ Mem.loadbytes m b 0 sz = Some (bytes_of_init_data_list ge data)
      | sec_rwdata data =>
        let sz := (init_data_list_size data) in
        Mem.range_perm m b 0 sz Cur Writable /\ (forall ofs k p, Mem.perm m b ofs k p -> 0 <= ofs < sz /\ perm_order Writable p)
        /\ load_store_init_data ge m b 0 data
        /\ Mem.loadbytes m b 0 sz = Some (bytes_of_init_data_list ge data)
      end
    | None =>
      (* common symbol or external function *)
      match prog.(prog_symbtable) ! id with
      | Some e =>
        match e.(symbentry_type),e.(symbentry_secindex) with
        | symb_func,secindex_undef =>
          Mem.perm m b 0 Cur Nonempty /\
          (forall ofs k p, Mem.perm m b ofs k p -> ofs = 0 /\ p = Nonempty)
        | symb_data,secindex_comm =>
          let sz := e.(symbentry_size) in
          let data := Init_space sz :: nil in
          Mem.range_perm m b 0 sz Cur Writable /\ (forall ofs k p, Mem.perm m b ofs k p -> 0 <= ofs < sz /\ perm_order Writable p)
          /\ load_store_init_data ge m b 0 data
          /\ Mem.loadbytes m b 0 sz = Some (bytes_of_init_data_list ge data)
        | symb_data,secindex_undef =>
          Mem.perm m b 0 Cur Nonempty /\
          (forall ofs k p, Mem.perm m b ofs k p -> ofs = 0 /\ p = Nonempty)
        | _,_ => False
        end
      | _ => False
      end
    end.

Definition init_mem (p: program) :=
  let ge := globalenv p in
  match alloc_sections ge p.(prog_sectable) Mem.empty with
  | Some m1 =>
    alloc_external_symbols m1 p.(prog_symbtable)
  | None => None
  end.

(** Properties about init_mem *)
Lemma init_mem_characterization_gen:
  forall p m,
  init_mem p = Some m ->
  globals_initialized (globalenv p) p m.
Proof.
  Admitted.


Lemma store_init_data_nextblock : forall v ge m b ofs m',
  store_init_data ge m b ofs v = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  intros. destruct v; simpl in *; try now (eapply Mem.nextblock_store; eauto).
  eapply Genv.store_zeros_nextblock.
  eauto.
Qed.
    
Lemma store_init_data_list_nextblock : forall l ge m b ofs m',
  store_init_data_list ge m b ofs l = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction l; intros.
  - inv H. auto.
  - inv H. destr_match_in H1; inv H1.
    exploit store_init_data_nextblock; eauto.
    exploit IHl; eauto. intros. congruence.
Qed.

Lemma store_init_data_list_support: forall l ge m b ofs m',
    store_init_data_list ge m b ofs l = Some m' ->
    Mem.support m' = Mem.support m.
Proof.
  induction l;intros.
  - inv H. auto.
  - inv H. destr_match_in H1;inv H1.
    transitivity (Mem.support m0). eapply IHl. eauto.
    destruct a;simpl in EQ;try (eapply Mem.support_store;eauto;fail).
    eapply Genv.store_zeros_support. eauto.
Qed.

Lemma store_init_data_stack : forall v ge (m m' : mem) (b : block) (ofs : Z),
       store_init_data ge m b ofs v = Some  m' -> Mem.stack (Mem.support m') = Mem.stack (Mem.support m).
Proof.
  intros v ge0 m m' b ofs H. destruct v; simpl in *;try (f_equal;now eapply Mem.support_store; eauto).
  eapply Genv.store_zeros_stack.
  eauto.
Qed.

Lemma store_init_data_list_stack : forall l ge (m m' : mem) (b : block) (ofs : Z),
       store_init_data_list ge m b ofs l = Some m' -> Mem.stack (Mem.support m') = Mem.stack (Mem.support m).
Proof.
  induction l; intros.
  - simpl in H. inv H. auto.
  - simpl in H. destr_match_in H; inv H.
    exploit store_init_data_stack; eauto.
    exploit IHl; eauto.
    intros. congruence.
Qed.

Lemma alloc_section_stack: forall ge id sec m m',
    alloc_section ge (Some m) id sec = Some m' ->
    Mem.stack (Mem.support m) = Mem.stack (Mem.support m').
Proof.
  unfold alloc_section. intros.
  repeat destr_in H.
  exploit Mem.support_drop;eauto.
  exploit Mem.support_alloc_glob;eauto. intros.
  rewrite H0. rewrite H. auto.
  exploit Mem.support_drop;eauto.
  exploit Mem.support_alloc_glob;eauto. intros.
  exploit Genv.store_zeros_stack;eauto. intros (?&?).
  exploit store_init_data_list_stack;eauto. intros.
  rewrite H0. rewrite H4. rewrite H2.
  rewrite H. auto.
  exploit Mem.support_drop;eauto.
  exploit Mem.support_alloc_glob;eauto. intros.
  exploit Genv.store_zeros_stack;eauto. intros (?&?).
  exploit store_init_data_list_stack;eauto. intros.
  rewrite H0. rewrite H4. rewrite H2.
  rewrite H. auto.
Qed.  

Definition alloc_property_aux (m: mem) (optm': option mem):=
  forall m', optm' = Some m' ->
        Mem.stack (Mem.support m) = Mem.stack (Mem.support m').

Lemma alloc_sections_stack_aux: forall ge defs m,
     alloc_property_aux m
            (fold_left
    (fun (a : option mem) (p : positive * section) =>
     alloc_section ge a (fst p) (snd p))
    defs (Some m)).
Proof.
  intros. eapply Bounds.fold_left_preserves.
  unfold alloc_property_aux. intros.
  destruct a.
  eapply alloc_section_stack in H0. rewrite <- H0.
  eapply H. auto.
  simpl in H0. inv H0.
  unfold alloc_property_aux. intros. inv H. auto.
Qed.
  
Lemma alloc_sections_stack: forall ge sectbl m m',
    alloc_sections ge sectbl m = Some m' ->
    Mem.stack (Mem.support m) = Mem.stack (Mem.support m').
Proof.
  
  unfold alloc_sections. intros ge sectbl m m'.
  rewrite PTree.fold_spec. intros.
  exploit alloc_sections_stack_aux;eauto.
Qed.

Lemma alloc_external_symbol_stack: forall id e m m',
    alloc_external_comm_symbol(Some m) id e = Some m' ->
    Mem.stack (Mem.support m) = Mem.stack (Mem.support m').
Proof.
  unfold alloc_external_comm_symbol.
  intros. repeat destr_in H.
  exploit Mem.support_drop;eauto.
  exploit Mem.support_alloc_glob;eauto. intros.
  rewrite H0. rewrite H. auto.
  exploit Mem.support_drop;eauto.
  exploit Mem.support_alloc_glob;eauto. intros.
  exploit Genv.store_zeros_stack;eauto. intros (?&?).
  rewrite H0. rewrite H2. rewrite H. auto.
  exploit Mem.support_drop;eauto.
  exploit Mem.support_alloc_glob;eauto. intros.
  exploit Genv.store_zeros_stack;eauto. intros (?&?).
  rewrite H0. rewrite H2. rewrite H. auto.
  (* exploit Mem.support_drop;eauto. *)
  (* exploit Mem.support_alloc_glob;eauto. intros. *)
  (* exploit Genv.store_zeros_stack;eauto. intros (?&?). *)
  (* rewrite H0. rewrite H2. rewrite H. auto. *)
  (* exploit Mem.support_drop;eauto. *)
  (* exploit Mem.support_alloc_glob;eauto. intros. *)
  (* exploit Genv.store_zeros_stack;eauto. intros (?&?). *)
  (* rewrite H0. rewrite H2. rewrite H. auto. *)
Qed.



Lemma alloc_external_symbols_stack: forall symbtbl m m',
    alloc_external_symbols m symbtbl = Some m' ->
    Mem.stack (Mem.support m) = Mem.stack (Mem.support m').
Proof.
  unfold alloc_external_symbols. intros.
  rewrite PTree.fold_spec in H.
  assert (alloc_property_aux m (fold_left
        (fun (a : option mem) (p : positive * symbentry) =>
         alloc_external_comm_symbol a (fst p) (snd p))
        (PTree.elements symbtbl) (Some m))).
  eapply Bounds.fold_left_preserves.
  unfold alloc_property_aux.
  intros.
  destruct a.
  eapply alloc_external_symbol_stack in H1.
  rewrite <- H1.  eapply H0. auto.
  simpl in H1. congruence.
  unfold alloc_property_aux.
  intros. inv H0;auto.
  unfold alloc_property_aux in H0.
  eapply H0. auto.
Qed.


Lemma init_mem_stack:
  forall p m,
    init_mem p = Some m ->
    Mem.stack (Mem.support m) = Node None nil nil None.
Proof.
  intros. unfold init_mem in H.
  repeat destr_in H.
  erewrite <- alloc_external_symbols_stack; eauto.
  erewrite <- alloc_sections_stack; eauto.
  simpl. auto.
Qed.



Section INITDATA.

Variable ge: Genv.t.

Remark store_init_data_perm:
  forall k prm b' q i b m p m',
  store_init_data ge m b p i = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  intros. 
  assert (forall chunk v,
          Mem.store chunk m b p v = Some m' ->
          (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm)).
    intros; split; eauto with mem.
    destruct i; simpl in H; eauto.
  eapply Genv.store_zeros_perm.
  eauto.
Qed.

Remark store_init_data_list_perm:
  forall k prm b' q idl b m p m',
  store_init_data_list ge m b p idl = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  induction idl as [ | i1 idl]; simpl; intros.
- inv H; tauto.
- destruct (store_init_data ge m b p i1) as [m1|] eqn:S1; try discriminate.
  transitivity (Mem.perm m1 b' q k prm). 
  eapply store_init_data_perm; eauto.
  eapply IHidl; eauto.
Qed.

Lemma store_init_data_exists:
  forall m b p i,
    Mem.range_perm m b p (p + init_data_size i) Cur Writable ->
    (* Mem.stack_access (Mem.stack m) b p (p + init_data_size i)  -> *)
    (Genv.init_data_alignment i | p) ->
    (* (forall id ofs, i = Init_addrof id ofs -> exists b, find_symbol ge id = Some b) -> *)
    exists m', store_init_data ge m b p i = Some m'.
Proof.
  intros. 
  assert (DFL: forall chunk v,
          init_data_size i = size_chunk chunk ->
          Genv.init_data_alignment i = align_chunk chunk ->
          exists m', Mem.store chunk m b p v = Some m').
  { intros. destruct (Mem.valid_access_store m chunk b p v) as (m' & STORE).
    split. rewrite <- H1; auto.
    rewrite  <- H2. auto.
    exists m'; auto. }
  destruct i; eauto.
  simpl. eapply Genv.store_zeros_exists.
  simpl in H. auto.
Qed.

(* SACC
Lemma store_init_data_stack_access:
  forall m b p i1 m1,
    store_init_data ge m b p i1 = Some m1 ->
    forall b' lo hi,
      stack_access (Mem.stack m1) b' lo hi <-> stack_access (Mem.stack m) b' lo hi.
Proof.
  unfold store_init_data.
  destruct i1; intros; try now (eapply Mem.store_stack_access ; eauto).
  inv H; tauto.
Qed.
*)

Lemma store_init_data_list_exists:
  forall b il m p,
  Mem.range_perm m b p (p + init_data_list_size il) Cur Writable ->
  (* stack_access (Mem.stack m) b p (p + init_data_list_size il) -> *)
  Genv.init_data_list_aligned p il ->
  (* (forall id ofs, In (Init_addrof id ofs) il -> exists b, find_symbol ge id = Some b) -> *)
  exists m', store_init_data_list ge m b p il = Some m'.
Proof.
  induction il as [ | i1 il ]; simpl; intros.
- exists m; auto.
- destruct H0. 
  destruct (@store_init_data_exists m b p i1) as (m1 & S1); eauto.
  red; intros. apply H. generalize (init_data_list_size_pos il); lia.
  (* generalize (init_data_list_size_pos il); omega. *)
  rewrite S1.
  apply IHil; eauto.
  red; intros. erewrite <- store_init_data_perm by eauto. apply H. generalize (init_data_size_pos i1); lia.
Qed.

End INITDATA.


Section STORE_INIT_DATA_PRESERVED.
  Variable ge1: Genv.t.
  Variable ge2: Genv.t.

  Hypothesis symbols_preserved:
    forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

  Lemma store_init_data_pres: forall d m b ofs,
      store_init_data ge1 m b ofs d = store_init_data ge2 m b ofs d.
  Proof.
    destruct d;simpl;auto.
    intros.
    assert (EQ: forall id ofs, Genv.symbol_address ge2 id ofs = Genv.symbol_address ge1 id ofs).
    { unfold Genv.symbol_address; simpl; intros. rewrite symbols_preserved;auto. }
    rewrite EQ.
    auto.
  Qed.

  Lemma store_init_data_list_pres: forall l m b ofs,
      store_init_data_list ge1 m b ofs l = store_init_data_list ge2 m b ofs l.
  Proof.
    induction l;auto.
    intros. simpl. rewrite store_init_data_pres.
    destr.
  Qed.
  
End STORE_INIT_DATA_PRESERVED.



Definition well_formed_symbtbl (sectbl:sectable) symbtbl:=
  forall id e,
    symbtbl ! id = Some e ->
    match symbentry_secindex e with
    | secindex_normal i =>        
      symbentry_type e <> symb_notype /\  exists sec,sectbl ! i = Some sec
    | secindex_comm =>
      symbentry_type e = symb_data
    | secindex_undef =>
      symbentry_type e <> symb_notype
    end.

Lemma alloc_sections_valid_aux: forall l b m m' ge,
    fold_left
      (fun (a : option mem)
         (p : positive * RelocProg.section instruction init_data)
       => alloc_section ge a (fst p) (snd p)) l (Some m) = Some m' ->
      sup_In b m.(Mem.support) ->
      sup_In b m'.(Mem.support).
Proof.
  induction l;intros.
  simpl in H. inv H. auto.
  simpl in H. destruct a.
  destruct s.
  - simpl in *.
    destruct Mem.alloc_glob eqn:ALLOC in H.
    apply Mem.support_alloc_glob in ALLOC.
    destruct (Mem.drop_perm) eqn:FOLD in H.
    eapply IHl;eauto.
    eapply Mem.drop_perm_valid_block_1;eauto.
    unfold Mem.valid_block.
    rewrite ALLOC.
    apply Mem.sup_incr_glob_in. right. auto.
    clear IHl.
    induction l;simpl in H.
    inv H.  apply IHl. auto.
  - simpl in *.
    destruct Mem.alloc_glob eqn:ALLOC in H.
    destr_in H. destr_in H.
    apply Mem.support_alloc_glob in ALLOC.
    destruct (Mem.drop_perm) eqn:FOLD in H.
    eapply IHl;eauto.
    eapply Mem.drop_perm_valid_block_1;eauto.
    unfold Mem.valid_block.
    
    eapply store_init_data_list_support in Heqo0.
    rewrite Heqo0.
    eapply Genv.store_zeros_support in Heqo. rewrite Heqo.
    rewrite ALLOC.
    apply Mem.sup_incr_glob_in. right. auto.
    clear IHl.
    induction l;simpl in H.
    inv H.  apply IHl. auto.
    clear IHl.
    induction l;simpl in H.
    inv H.  apply IHl. auto.
        clear IHl.
    induction l;simpl in H.
    inv H.  apply IHl. auto.

  - simpl in *.
    destruct Mem.alloc_glob eqn:ALLOC in H.
    destr_in H. destr_in H.
    apply Mem.support_alloc_glob in ALLOC.
    destruct (Mem.drop_perm) eqn:FOLD in H.
    eapply IHl;eauto.
    eapply Mem.drop_perm_valid_block_1;eauto.
    unfold Mem.valid_block.
    
    eapply store_init_data_list_support in Heqo0.
    rewrite Heqo0.
    eapply Genv.store_zeros_support in Heqo. rewrite Heqo.
    rewrite ALLOC.
    apply Mem.sup_incr_glob_in. right. auto.
    clear IHl.
    induction l;simpl in H.
    inv H.  apply IHl. auto.
    clear IHl.
    induction l;simpl in H.
    inv H.  apply IHl. auto.
        clear IHl.
    induction l;simpl in H.
    inv H.  apply IHl. auto.
Qed.


Lemma alloc_sections_valid: forall id sec sectbl m m' ge,
      sectbl ! id = Some sec ->
      alloc_sections ge sectbl m = Some m' ->     
      sup_In (Global id) m'.(Mem.support).
Proof.
  unfold alloc_sections.
  intros id sec sectbl m m' ge A1 A2 .
  rewrite PTree.fold_spec in A2.
  apply PTree.elements_correct in A1.
  generalize (PTree.elements_keys_norepet sectbl).
  intros NOREP.
  exploit in_norepet_unique_r;eauto.
  intros (gl1 & gl2 & P1 & P2).
  unfold section in *. rewrite P1 in *.
  rewrite fold_left_app in A2.
  simpl in A2.
   unfold ident in *.
  destruct ((alloc_section ge
            (fold_left
               (fun (a : option mem)
                  (p : positive *
                       RelocProg.section instruction init_data) =>
                alloc_section ge a (fst p) (snd p)) gl1 
               (Some m)) id sec)) eqn:FOLD.
  - 
    exploit alloc_sections_valid_aux;eauto.
    unfold alloc_section in FOLD at 1. destr_in FOLD.
    destruct sec.
    + simpl in *.
      destruct Mem.alloc_glob eqn:ALLOC in FOLD.
      apply Mem.support_alloc_glob in ALLOC.
      generalize (Mem.sup_incr_glob_in1 id (Mem.support m1)).
      rewrite <- ALLOC.
      intros.
      exploit Mem.drop_perm_valid_block_1;eauto.
    + simpl in *.     
      destruct Mem.alloc_glob eqn:ALLOC in FOLD.
      repeat destr_in FOLD.
      apply Mem.support_alloc_glob in ALLOC.      
      generalize (Mem.sup_incr_glob_in1 id (Mem.support m1)).
      rewrite <- ALLOC.
      exploit Genv.store_zeros_support;eauto.
      exploit store_init_data_list_support;eauto.
      intros. rewrite <- H1 in *.
      rewrite <- H in *.
      exploit Mem.drop_perm_valid_block_1;eauto.
    + simpl in *.     
      destruct Mem.alloc_glob eqn:ALLOC in FOLD.
      repeat destr_in FOLD.
      apply Mem.support_alloc_glob in ALLOC.      
      generalize (Mem.sup_incr_glob_in1 id (Mem.support m1)).
      rewrite <- ALLOC.
      exploit Genv.store_zeros_support;eauto.
      exploit store_init_data_list_support;eauto.
      intros. rewrite <- H1 in *.
      rewrite <- H in *.
      exploit Mem.drop_perm_valid_block_1;eauto.
  - clear A1 NOREP P1 P2.
    induction gl2.
    simpl in A2. inv A2.
    apply IHgl2. auto.
Qed.

Lemma alloc_external_symbols_valid_aux2: forall l,
        fold_left
          (fun (a : option mem) (p : positive * symbentry) =>
             alloc_external_comm_symbol a (fst p) (snd p)) l None =
        None.
Proof.
  induction l;simpl;auto.
Qed.

Lemma alloc_external_symbols_valid_aux: forall l m m' b,
    fold_left
      (fun (a : option mem) (p : positive * symbentry) =>
         alloc_external_comm_symbol a (fst p) (snd p)) l (Some m) =
    Some m' ->
    sup_In b (Mem.support m) ->
    sup_In b (Mem.support m').
Proof.
  induction l;intros.
  simpl in H. inv H. auto.
  simpl in H.
  destruct (symbentry_type (snd a)).
  - destruct (symbentry_secindex (snd a)).
    + eapply IHl;eauto.
    + rewrite alloc_external_symbols_valid_aux2 in H. inv H.
    + destruct Mem.alloc_glob eqn:ALLOC in H.
      destruct Mem.drop_perm eqn:DROP in H.
      eapply IHl;eauto.
      eapply Mem.drop_perm_valid_block_1;eauto.
      unfold Mem.valid_block. apply Mem.support_alloc_glob in ALLOC.
      rewrite ALLOC. eapply Mem.sup_incr_glob_in.
      right. auto.
      rewrite alloc_external_symbols_valid_aux2 in H. inv H.
  - destruct (symbentry_secindex (snd a)).
    + eapply IHl;eauto.
    + destruct Mem.alloc_glob eqn:ALLOC in H.
      destruct store_zeros eqn:STORE in H.
      destruct Mem.drop_perm eqn:DROP in H.
      eapply IHl;eauto.
      eapply Mem.drop_perm_valid_block_1;eauto.
      unfold Mem.valid_block.
      erewrite Genv.store_zeros_support.
      apply Mem.support_alloc_glob in ALLOC.
      rewrite ALLOC. eapply Mem.sup_incr_glob_in.
      right. auto.  eauto.
      rewrite alloc_external_symbols_valid_aux2 in H. inv H.
      rewrite alloc_external_symbols_valid_aux2 in H. inv H.
    + destruct Mem.alloc_glob eqn:ALLOC in H.
      destruct store_zeros eqn:STORE in H.
      destruct Mem.drop_perm eqn:DROP in H.
      eapply IHl;eauto.
      eapply Mem.drop_perm_valid_block_1;eauto.
      unfold Mem.valid_block.
      erewrite Genv.store_zeros_support.
      apply Mem.support_alloc_glob in ALLOC.
      rewrite ALLOC. eapply Mem.sup_incr_glob_in.
      right. auto.  eauto.
      rewrite alloc_external_symbols_valid_aux2 in H. inv H.
      rewrite alloc_external_symbols_valid_aux2 in H. inv H.
  - rewrite alloc_external_symbols_valid_aux2 in H. inv H.
Qed.            
    
Lemma alloc_external_symbols_valid: forall id e symbtbl m m',
    symbtbl ! id = Some e ->
    alloc_external_symbols m symbtbl = Some m' ->
    match symbentry_secindex e with
    | secindex_normal i =>
      sup_In (Global i) m.(Mem.support) ->
      sup_In (Global i) m'.(Mem.support)
    | secindex_comm =>
      symbentry_type e = symb_data ->
      sup_In (Global id) m'.(Mem.support)
    | secindex_undef =>
      symbentry_type e <> symb_notype ->
      sup_In (Global id) m'.(Mem.support)
    end.
Proof.
  unfold alloc_external_symbols.
  intros id e symbtbl m m' A1 A2.
  rewrite PTree.fold_spec in A2.
  apply PTree.elements_correct in A1.
  generalize (PTree.elements_keys_norepet symbtbl).
  intros NOREP.
  exploit in_norepet_unique_r;eauto.
  intros (gl1 & gl2 & P1 & P2).
  rewrite P1 in *.
  rewrite fold_left_app in A2.
  simpl in A2.
  unfold ident in *.
  destruct (fold_left
               (fun (a : option mem) (p : positive * symbentry) =>
                alloc_external_comm_symbol a (fst p) (snd p)) gl1
               (Some m)) eqn:FOLD.
  simpl in A2.
  - destruct (symbentry_secindex e).
    + destruct (symbentry_type e).
      * intros.
        exploit alloc_external_symbols_valid_aux.
        eapply FOLD. eauto. intros.
        exploit alloc_external_symbols_valid_aux.
        eapply A2. eauto. auto.
      * intros.
        exploit alloc_external_symbols_valid_aux.
        eapply FOLD. eauto. intros.
        exploit alloc_external_symbols_valid_aux.
        eapply A2. eauto. auto.
      * clear A1 P1 P2 NOREP.
        induction gl2.
        simpl in A2. inv A2.
        simpl in A2. apply IHgl2. auto.
    + intros.
      destruct (symbentry_type e);try congruence.
      destruct Mem.alloc_glob eqn:ALLOC in A2.
      destruct store_zeros eqn:STORE in A2.
      * destruct Mem.drop_perm eqn:DROP in A2.
        -- exploit alloc_external_symbols_valid_aux.
           apply A2. eapply Mem.drop_perm_valid_block_1;eauto.
           unfold Mem.valid_block.
           erewrite  Genv.store_zeros_support;eauto.
           apply Mem.support_alloc_glob in ALLOC.
           rewrite ALLOC.
           erewrite Mem.sup_incr_glob_in. left.
           eauto. auto.
        -- clear A1 P1 P2 NOREP.
           induction gl2.
           simpl in A2. inv A2.
           simpl in A2. apply IHgl2. auto.
      * clear A1 P1 P2 NOREP.
        induction gl2.
        simpl in A2. inv A2.
        simpl in A2. apply IHgl2. auto.
    + intros.
      destruct (symbentry_type e);try congruence.
      * destruct Mem.alloc_glob eqn:ALLOC in A2.
        destruct Mem.drop_perm eqn:DROP in A2.
        -- exploit alloc_external_symbols_valid_aux.
           apply A2. eapply Mem.drop_perm_valid_block_1;eauto.
           unfold Mem.valid_block.
           apply Mem.support_alloc_glob in ALLOC.
           rewrite ALLOC.
           erewrite Mem.sup_incr_glob_in. left.
           eauto. auto.
        -- clear A1 P1 P2 NOREP.
           induction gl2.
           simpl in A2. inv A2.
           simpl in A2. apply IHgl2. auto.
      * destruct Mem.alloc_glob eqn:ALLOC in A2.
        destruct store_zeros eqn:STORE in A2.
        -- destruct Mem.drop_perm eqn:DROP in A2.
           ++ exploit alloc_external_symbols_valid_aux.
              apply A2. eapply Mem.drop_perm_valid_block_1;eauto.
              unfold Mem.valid_block.
              erewrite  Genv.store_zeros_support;eauto.
              apply Mem.support_alloc_glob in ALLOC.
              rewrite ALLOC.
              erewrite Mem.sup_incr_glob_in. left.
              eauto. auto.
           ++ clear A1 P1 P2 NOREP.
              induction gl2.
              simpl in A2. inv A2.
              simpl in A2. apply IHgl2. auto.
        --
          clear A1 P1 P2 NOREP.
          induction gl2.
          simpl in A2. inv A2.
          simpl in A2. apply IHgl2. auto.
  - clear A1 P1 P2 NOREP.
    induction gl2.
    simpl in A2. inv A2.
    simpl in A2. apply IHgl2. auto.
Qed.

Lemma find_symbol_not_fresh: forall p id b m ofs,
    well_formed_symbtbl p.(prog_sectable) p.(prog_symbtable) ->
    init_mem p = Some m ->
    Genv.find_symbol (globalenv p) id = Some (b,ofs) ->
    Mem.valid_block m b.
Proof.
  unfold init_mem, globalenv, Genv.find_symbol, gen_symb_map.
  simpl. intros p id b m ofs MATCH INIT GENV.
  destr_in INIT.
  rewrite PTree.gmap in GENV. unfold option_map in GENV.
  destr_in GENV. inv GENV.
  unfold gen_global in H0.

  unfold well_formed_symbtbl in MATCH.
  generalize (MATCH _ _ Heqo0). intros A.  
  unfold Mem.valid_block.
  destr_in A.
  - destruct A as (P1 & sec & P2).
    eapply alloc_sections_valid in Heqo;eauto.
    eapply alloc_external_symbols_valid in INIT;eauto.
    rewrite Heqs0 in INIT. inv H0. eauto.
  - eapply alloc_external_symbols_valid in INIT;eauto.
    rewrite Heqs0,A in INIT.
    inv H0. auto.
  - eapply alloc_external_symbols_valid in INIT;eauto.
    rewrite Heqs0 in INIT.
    inv H0. auto.
Qed.

  
Inductive initial_state_gen {D: Type} (p: RelocProg.program fundef unit instruction D) (rs: regset) m: state -> Prop :=
| initial_state_gen_intro:
    forall m1 m2 stk
      (MALLOC: Mem.alloc m 0 (max_stacksize + align (size_chunk Mptr) 8) = (m1,stk))
      (MST: Mem.storev Mptr m1 (Vptr stk (Ptrofs.repr (max_stacksize + align (size_chunk Mptr) 8 - size_chunk Mptr))) Vnullptr = Some m2),
      let ge := (globalenv p) in
      let rs0 :=
          rs # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
           # RA <- Vnullptr
           # RSP <- (Vptr stk (Ptrofs.sub (Ptrofs.repr (max_stacksize + align (size_chunk Mptr) 8)) (Ptrofs.repr (size_chunk Mptr)))) in
      initial_state_gen p rs m (State rs0 m2).


Inductive initial_state (prog: program) (rs: regset) (s: state): Prop :=
| initial_state_intro: forall m,
    init_mem prog = Some m ->
    initial_state_gen prog rs m s ->
    initial_state prog rs s.

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vnullptr ->
      rs#RAX = Vint r ->
      final_state (State rs m) r.

(* Local Existing Instance mem_accessors_default. *)

Definition semantics (p: program) (rs: regset) :=
  Semantics_gen step (initial_state p rs) final_state (globalenv p) (Genv.genv_senv (globalenv p)).

(** Determinacy of the [Asm] semantics. *)

Lemma semantics_determinate: forall p rs, determinate (semantics p rs).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities.
+ split. constructor. auto.
+ discriminate.
+ discriminate.
+ assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
+ assert (args0 = args) by (eapply Asm.extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H3. eexact H7. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros; inv H; simpl.
  lia.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. assert (m = m0) by congruence. subst. inv H2; inv H3.
  assert (m1 = m3 /\ stk = stk0) by intuition congruence. destruct H0; subst.
  assert (m2 = m4) by congruence. subst.
  f_equal. (* congruence. *)
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. red; intros; red; intros. inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

Theorem reloc_prog_single_events p rs:
  single_events (semantics p rs).
Proof.
  red. simpl. intros s t s' STEP.
  inv STEP; simpl. lia.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
Qed.

Theorem reloc_prog_receptive p rs:
  receptive (semantics p rs).
Proof.
  split.
  - simpl. intros s t1 s1 t2 STEP MT.
    inv STEP.
    inv MT. eexists. eapply exec_step_internal; eauto.
    edestruct external_call_receptive as (vres2 & m2 & EC2); eauto.
    eexists. eapply exec_step_builtin; eauto.
    edestruct external_call_receptive as (vres2 & m2 & EC2); eauto.
    eexists. eapply exec_step_external; eauto.
  - eapply reloc_prog_single_events; eauto.
Qed.

End WITH_INSTR_SIZE.