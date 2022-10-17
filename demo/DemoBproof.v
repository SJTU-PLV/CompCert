Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.
Require Import Conventions Mach.

Require Import Locations.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers.
Require Import SymbolTable DemoB DemoBspec.

Require Import CallConv Compiler.

Require Import CKLRAlgebra Extends Inject InjectFootprint.

(** * Step1 : self_simulation of Bspec *)

Section SELF_INJP.

Section ms.
Variable w : world injp.

Inductive match_states' : state -> state -> Prop :=
  |match_Callstateg_intro f m1 m2 Hm i:
     w = injpw f m1 m2 Hm ->
     match_states' (Callstateg i m1) (Callstateg i m2)
  |match_Callstatef_intro f m1 m2 Hm i:
     w = injpw f m1 m2 Hm ->
     match_states' (Callstatef i m1) (Callstatef i m2)
  |match_Returnstatef_intro f m1 m2 Hm i ti:
     injp_acc w (injpw f m1 m2 Hm) ->
     match_states' (Returnstatef i ti m1) (Returnstatef i ti m2)
  |match_Returnstateg_intro f m1 m2 Hm i:
     injp_acc w (injpw f m1 m2 Hm) ->
     match_states' (Returnstateg i m1) (Returnstateg i m2).
End ms.

Theorem self_simulation_C :
  forward_simulation (cc_c injp) (cc_c injp) Bspec Bspec.
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *.
  pose (ms := fun s1 s2 => match_states' w s1 s2).
  eapply forward_simulation_step with (match_states := ms); cbn; eauto.
  -  intros. inv Hse. inv H. cbn in H3.
    eapply Genv.is_internal_transf; eauto.
    + red. red. repeat apply conj; eauto.
      instantiate (1:= id).
      constructor.
      -- constructor; eauto. econstructor; eauto. apply linkorder_refl.
      -- constructor; eauto.
         econstructor; eauto. simpl.
         econstructor; eauto. econstructor; eauto.
         econstructor; eauto. simpl.
         econstructor; eauto. econstructor; eauto. apply linkorder_refl.
         econstructor; eauto.
    + reflexivity.
  - intros. inv H0. inv H. inv H4. inv H6. inv H2. inv H4. cbn in *.
    inv Hse. inv H7.
    eapply Genv.find_symbol_match in H; eauto. destruct H as [tb [A B]].
    exists (Callstateg i m2). split.
    econstructor; eauto. simpl in H1. rewrite H1 in A. inv A.
    rewrite Ptrofs.add_zero. reflexivity.
    econstructor; eauto.
  - intros. inv H; inv H0.
    exists (cr (Vint i) m2). split; econstructor; eauto.
    split. eauto. constructor. simpl. eauto.
    constructor.
  - intros. inv H; inv H0. inversion Hse. subst.
    eapply Genv.find_symbol_match in H2 as H'; eauto.
    destruct H' as [tb [A B]].
    exists (injpw f m1 m2 Hm) , (cq (Vptr tb Ptrofs.zero) int_int_sg ((Vint (Int.sub i Int.one)) :: nil) m2).
    repeat apply conj; eauto.
    + constructor. eauto.
    + constructor. simpl.
    replace (Vptr tb Ptrofs.zero) with (Vptr tb (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0))).
    econstructor; eauto. rewrite Ptrofs.add_zero. reflexivity.
    simpl. constructor. constructor. constructor. constructor. congruence.
    + intros r1 r2 s1' [w'[ Hw Hr]] F.
      destruct w' as [f' m1' m2' INJ0].
      destruct r1 as [t1 m1'1].
      destruct r2 as [t2 m2'1].
      inv Hr. cbn in *.
      inv F. inv H3. inv H7.
      exists (Returnstatef i ti m2'1). split.
      econstructor; eauto.
      econstructor; eauto.
  - intros. inv H0; inv H.
    + (* zero *)
      exists (Returnstateg (Int.zero) m2). split. constructor; eauto.
      econstructor; eauto. reflexivity.
    + (* read *)
      exists (Returnstateg ti m2).
      inv Hse. eapply Genv.find_symbol_match in H2; eauto.
      destruct H2 as [b' [VINJ FINDM']].
      exploit Mem.loadv_inject. 2: eapply LOAD0. all: eauto.
      intros [v0 [LOAD0' VINJ0]]. inv VINJ0.
      exploit Mem.loadv_inject; eauto.
      intros [v1 [LOAD1' VINJ1]]. inv VINJ1.
      split.
      econstructor; eauto.
      econstructor; eauto. reflexivity.
    + (* call *)
      exists (Callstatef i m2).
      inv Hse. eapply Genv.find_symbol_match in H2; eauto.
      destruct H2 as [b' [VINJ FINDM']].
      exploit Mem.loadv_inject. 2: eapply LOAD0. all: eauto.
      intros [v0 [LOAD0' VINJ0]]. inv VINJ0.
      split.
      econstructor; eauto.
      econstructor; eauto.
    + (* return *)
      destruct w as [f0 m1'0 m2'0 Hm0].
      inv Hse. inv H1. rename m' into m1'1. rename m'' into m1'2.
      eapply Genv.match_stbls_incr in H3; eauto.
      2:{ intros. exploit H14; eauto. intros [E F].
      unfold Mem.valid_block in *. split; eauto. }
      eapply Genv.find_symbol_match in H3. 2: eapply FINDM.
      destruct H3 as [b' [C D]].
      edestruct Mem.store_mapped_inject as [m2'1 [STORE0' INJ1]]; eauto.
      edestruct Mem.store_mapped_inject as [m2'2 [STORE1' INJ2]]; eauto.
      exists (Returnstateg (Int.add ti i) m2'2).
      econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
      instantiate (1:= INJ2).
      transitivity (injpw f m1 m2 Hm'2).
      constructor; eauto.
      constructor; eauto.
      -- red. intros. eapply Mem.perm_store_2; eauto.
         eapply Mem.perm_store_2; eauto.
      -- red. intros. eapply Mem.perm_store_2; eauto.
         eapply Mem.perm_store_2; eauto.
      -- eapply Mem.unchanged_on_trans.
         eapply Mem.store_unchanged_on; eauto.
         intros. intro. red in H0. congruence.
         eapply Mem.store_unchanged_on; eauto.
         intros. intro. red in H0. congruence.
      -- eapply Mem.unchanged_on_trans. 
         eapply Mem.store_unchanged_on; eauto.
         intros. intro. red in H0. apply H0 in C.
         apply Mem.store_valid_access_3 in STORE0.
         destruct STORE0 as [RANGE ALIGN].
         red in RANGE. exploit RANGE; eauto.
         intro. eapply C. replace (i0 - 0) with i0 by lia.
         eauto with mem.
         eapply Mem.store_unchanged_on; eauto.
         intros. intro. red in H0. apply H0 in C.
         apply Mem.store_valid_access_3 in STORE1.
         destruct STORE1 as [RANGE ALIGN].
         red in RANGE. exploit RANGE; eauto.
         intro. eapply C. replace (i0 - 0) with i0 by lia.
         eauto with mem.
      -- red. intros. congruence.
  - constructor. intros. inv H.
Qed.

End SELF_INJP.

Section WT_C.

Theorem self_simulation_wt :
  forward_simulation (wt_c @ lessdef_c) (wt_c @ lessdef_c) Bspec Bspec.
Proof.
  constructor. econstructor; eauto.
  intros se1 se2 w Hse Hse1. cbn in *.
  destruct w as [[se1' [se2' sg]] ?]. destruct Hse as [Hse Hse2].
  subst. inv Hse.
  instantiate (1 := fun se1 se2 w _ => (fun s1 s2 => s1 = s2 /\ snd (snd (fst w)) = int_int_sg)). cbn beta. simpl.
  instantiate (1 := state).
  instantiate (1 := fun s1 s2 => False).
  constructor; eauto.
  - intros. simpl. inv H. inv H0. inv H. inv H1. reflexivity.
  - intros. inv H. inv H1. cbn in *. inv H. inv H1. exists s1. exists s1.
    split. inv H2. inv H0. simpl. simpl in *.
    inv H. inv H2. inv H5.
    econstructor; eauto. split. reflexivity.
    inv H0. reflexivity.
  - intros. inv H. exists r1.
    split. auto. exists r1. inv H0.
    split; simpl; auto.
    econstructor; simpl. eauto.
    econstructor. constructor.
  - intros. subst.
    exists (se2 , (se2, int_int_sg), tt).
    exists q1. inv H. repeat apply conj; simpl; auto.
    + exists q1. split; inv H0; simpl;  constructor; simpl; eauto.
    + constructor; eauto. simpl. constructor. eauto.
    + intros. exists s1'. exists s1'. split; eauto.
      destruct H as [r3 [A B]].
      inv A. inv B. inv H1. inv H2. econstructor; eauto.
  - intros. inv H0. exists s1', s1'. split. left. econstructor; eauto.
    econstructor. traceEq.
    eauto.
  - constructor. intros. inv H.
Qed.

End WT_C.

Module CL.

Definition int_loc_arguments := loc_arguments int_int_sg.

Definition int_loc_argument := if Archi.ptr64 then (if Archi.win64 then (R CX) else (R DI))
                                          else S Outgoing 0 Tint.
Lemma loc_result_int:
 loc_result int_int_sg = One AX.
Proof.
  intros. unfold int_int_sg, loc_result.
  replace Archi.ptr64 with true by reflexivity.
  reflexivity.
Qed.

Lemma ls_result_int:
  forall ls, Locmap.getpair (map_rpair R (loc_result int_int_sg)) ls = ls (R AX).
Proof.
  intros. rewrite loc_result_int. reflexivity.
Qed.

Definition int_loc_result' : rpair mreg := loc_result int_int_sg.
(* Compute int_loc_result. One AX *)

Definition int_loc_result : loc := R AX.

Definition loc_int_loc (i: int) (l : loc): Locmap.t :=
  fun loc => if Loc.eq loc l  then (Vint i) else Vundef.

Inductive state :=
  | Callstateg (ls: Locmap.t) (m:mem)
  | Callstatef (ls: Locmap.t) (m:mem)
  | Returnstatef (aif: int) (ls: Locmap.t) (m:mem)
  | Returnstateg (ls: Locmap.t) (m:mem).

Section WITH_SE.
  Context (se: Genv.symtbl).

Inductive initial_state : query li_locset -> state -> Prop :=
| initial_state_intro
    v i m b (ls: Locmap.t)
    (SYMB: Genv.find_symbol se g_id = Some b)
    (FPTR: v = Vptr b Ptrofs.zero)
    (* (RANGE: 0 <= i.(Int.intval) < MAX) *)
    (LS: (Vint i :: nil) =  (fun p : rpair loc => Locmap.getpair p ls) ## (loc_arguments int_int_sg)):
    initial_state (lq v int_int_sg ls m) (Callstateg ls m).

Inductive at_external: state -> query li_locset -> Prop :=
| at_external_intro
    g_fptr m ls
    (FINDG: Genv.find_symbol se f_id = Some g_fptr):
    at_external (Callstatef ls m)
                (lq (Vptr g_fptr Ptrofs.zero) int_int_sg ls m).

Inductive after_external: state -> reply li_locset -> state -> Prop :=
| after_external_intro
    m ls ls' m1 i ti
    (LS: (Vint (Int.sub i Int.one) :: nil) =  (fun p : rpair loc => Locmap.getpair p ls) ## (loc_arguments int_int_sg))
    (LS' : Vint ti = Locmap.getpair (map_rpair R (loc_result int_int_sg)) ls'):
(*    (LS'' : ls'' = Locmap.set (R AX) (Vint (Int.add ti i)) ls')
    (FINDM: Genv.find_symbol se _memoized = Some b_mem)
    (STORE0: Mem.storev Mint32 m1 (Vptr b_mem Ptrofs.zero) (Vint i) = Some m2)
    (STORE0: Mem.storev Mint32 m2 (Vptr b_mem (Ptrofs.repr 4)) (Vint (Int.add ti i)) = Some m3):
*)
    after_external (Callstatef ls m) (lr ls' m1) (Returnstatef i ls' m1).

Inductive step : state -> trace -> state -> Prop :=
| step_zero
    i ls m ls'
    (ZERO: i.(Int.intval) = 0%Z)
    (LS: (Vint i :: nil) =  (fun p : rpair loc => Locmap.getpair p ls) ## (loc_arguments int_int_sg))
    (LS' : Vint (Int.zero) = Locmap.getpair (map_rpair R (loc_result int_int_sg)) ls'):
    step (Callstateg ls m) E0 (Returnstateg ls' m)
| step_read
    i ti b_mem m ls ls'
    (LS: (Vint i :: nil) =  (fun p : rpair loc => Locmap.getpair p ls) ## (loc_arguments int_int_sg))
    (LS'' : Vint (ti) = Locmap.getpair (map_rpair R (loc_result int_int_sg)) ls')
    (NZERO: i.(Int.intval) <> 0%Z)
    (FINDM: Genv.find_symbol se _memoized = Some b_mem)
    (LOAD0: Mem.loadv Mint32 m (Vptr b_mem Ptrofs.zero) = Some (Vint i))
    (LOAD1: Mem.loadv Mint32 m (Vptr b_mem (Ptrofs.repr 4)) = Some (Vint ti)):
    step (Callstateg ls m) E0 (Returnstateg ls' m)
| step_call
    i m ls b_mem i' ls'
    (NZERO: i.(Int.intval) <> 0%Z)
    (FINDM: Genv.find_symbol se _memoized = Some b_mem)
    (LOAD0: Mem.loadv Mint32 m (Vptr b_mem Ptrofs.zero) = Some (Vint i'))
    (NEQ: i <> i')
    (LS: (Vint i :: nil) =  (fun p : rpair loc => Locmap.getpair p ls) ## (loc_arguments int_int_sg))
    (LS' : ls' = Locmap.set (R BX) (Vint i) (Locmap.set int_loc_argument (Vint (Int.sub i Int.one)) ls)):
    step (Callstateg ls m) E0 (Callstatef ls' m)
| step_return
    b_mem m m' m'' ti ls ls' i
    (FINDM: Genv.find_symbol se _memoized = Some b_mem)
    (STORE0: Mem.storev Mint32 m (Vptr b_mem Ptrofs.zero) (Vint i) = Some m')
    (STORE0: Mem.storev Mint32 m' (Vptr b_mem (Ptrofs.repr 4)) (Vint (Int.add ti i)) = Some m'')
    (LS: Vint ti =  Locmap.getpair (map_rpair R (loc_result int_int_sg)) ls)
    (LS': ls' = Locmap.set (R AX) (Vint (Int.add ti i)) ls):
    step (Returnstatef i ls m) E0 (Returnstateg ls' m'').

(*maybe we should remember the origin value ls # (R BX) in f states.
  Because the arugment i of function g occupies the position of this callee-save position
*)

Inductive final_state: state -> reply li_locset  -> Prop :=
  | final_state_intro
      m ls:
      final_state (Returnstateg ls m) (lr ls m).

End WITH_SE.

Program Definition BspecL : Smallstep.semantics li_locset li_locset :=
  {|
   Smallstep.skel := erase_program prog;
   Smallstep.state := state;
   Smallstep.activate se :=
     let ge := Genv.globalenv se prog in
     {|
       Smallstep.step ge := step ge;
       Smallstep.valid_query q := Genv.is_internal ge (entry q);
       Smallstep.initial_state := initial_state ge;
       Smallstep.at_external := at_external ge;
       Smallstep.after_external := after_external;
       Smallstep.final_state := final_state;
       globalenv := ge;
     |}
   |}.

Inductive match_states : DemoBspec.state -> state -> Prop :=
  |cl_callstateg i ls m
     (LS: (Vint i :: nil) =  (fun p : rpair loc => Locmap.getpair p ls) ## (loc_arguments int_int_sg)):
     match_states (DemoBspec.Callstateg i m) (Callstateg ls m)
  |cl_callstatef i ls m
     (LS1: (Vint (Int.sub i Int.one) :: nil) =  (fun p : rpair loc => Locmap.getpair p ls) ## (loc_arguments int_int_sg))
     (LS2: Vint i = ls (R BX)):
     match_states (DemoBspec.Callstatef i m) (Callstatef ls m)
  |cl_returnstatef i ti ls m
     (LS' : Vint ti = Locmap.getpair (map_rpair R (loc_result int_int_sg)) ls):
     match_states (DemoBspec.Returnstatef i ti m) (Returnstatef i ls m)
  |cl_returnstateg i ls m
     (LS: Vint i = Locmap.getpair (map_rpair R (loc_result int_int_sg)) ls):
     match_states (DemoBspec.Returnstateg i m) (Returnstateg ls m).

Theorem c_locset :
  forward_simulation (cc_c_locset) (cc_c_locset) Bspec BspecL.
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *.
  pose (ms := fun s1 s2 => (match_states s1 s2 /\ w = int_int_sg)).
  eapply forward_simulation_step with (match_states := ms); cbn; eauto.
  - intros. inv H. simpl. reflexivity.
  - intros. inv H0. inv H. exists (Callstateg rs m).
    split.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
  - intros. inv H. inv H0. inv H1.
    exists (lr ls m). split.
    econstructor; eauto.
    constructor. eauto.
  - intros. inversion H0. inv H. inv H0. inv H3.
    exists int_int_sg, (lq (Vptr g_fptr Ptrofs.zero) int_int_sg ls m).
    repeat apply conj; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + intros. inv H0. inv H.
      exists (Returnstatef aif rs' m'). split.
      econstructor; eauto.
      red. split.
      econstructor; eauto. auto.
  - intros. inv H; inv H0; inv H.
    + exists (Returnstateg (loc_int_loc (Int.zero) int_loc_result) m).
      split;econstructor; eauto.
      constructor; eauto.
    + exists (Returnstateg (loc_int_loc (ti) int_loc_result) m). split.
      eapply step_read; eauto. reflexivity.
      econstructor; eauto.
      econstructor; eauto.
    + exists (Callstatef (Locmap.set (R BX) (Vint i) (Locmap.set int_loc_argument (Vint (Int.sub i Int.one)) ls)) m). split; econstructor; eauto.
      constructor; eauto.
      unfold int_loc_arguments, int_int_sg. unfold loc_arguments.
      unfold int_loc_argument. replace Archi.ptr64 with true by reflexivity.
      simpl. destruct Archi.win64; simpl; f_equal.
    + eexists. split. econstructor; eauto.
      econstructor; eauto.
      econstructor; eauto.
  - constructor. intros. inv H.
Qed.

End CL.

Module LM.

Inductive state :=
  |Callstateg (sp ra: val) (rs: Mach.regset) (m:mem)
  |Callstatef (sp ra: val) (rs: Mach.regset) (m: mem)
  |Returnstatef (rs: Mach.regset) (m:mem)
  |Returnstateg (rs: Mach.regset) (m:mem).

Section WITH_SE.
  Context (se: Genv.symtbl).

(* Compute CL.int_loc_argument. *)
Definition int_argument_mreg := if Archi.win64 then CX else DI.

Inductive initial_state : query li_mach -> state -> Prop :=
| initial_state_intro
    v m b i sp ra rs
    (SYMB: Genv.find_symbol se g_id = Some b)
    (FPTR: v = Vptr b Ptrofs.zero)
(*     (RANGE: 0 <= i.(Int.intval) < MAX) *)
    (RS : rs int_argument_mreg = Vint i)
    (SP: Val.has_type sp Tptr)
    (RA: Val.has_type ra Tptr):
    initial_state (mq v sp ra rs m) (Callstateg sp ra rs m).

Inductive at_external: state -> query li_mach -> Prop :=
| at_external_intro
    g_fptr m sp ra rs
    (FINDG: Genv.find_symbol se f_id = Some g_fptr):
    at_external (Callstatef sp ra rs m)
                (mq (Vptr g_fptr Ptrofs.zero) sp ra rs m).

Inductive after_external : state -> reply li_mach -> state -> Prop :=
| after_external_intro
    i m  sp ra rs rs'  m' ti
    (RS1 : rs int_argument_mreg = Vint (Int.sub i Int.one))
(*    (RS2 : rs BX = Vint i) *)
    (RS' : rs' AX = Vint ti):
(*    (RS'' : rs'' = Regmap.set AX (Vint (Int.add ti i)) rs') *)
(*    (FINDM: Genv.find_symbol se _memoized = Some b_mem)
    (STORE0: Mem.storev Mint32 m' (Vptr b_mem Ptrofs.zero) (Vint i) = Some m'')
    (STORE0: Mem.storev Mint32 m'' (Vptr b_mem (Ptrofs.repr 4)) (Vint (Int.add ti i)) = Some m'''):
*)
    (forall r, is_callee_save r = true -> rs' r = rs r) ->
    Mem.unchanged_on (loc_init_args (size_arguments int_int_sg) sp) m m' ->
    after_external (Callstatef sp ra rs m) (mr rs' m') (Returnstatef rs' m').

Inductive step : state -> trace -> state -> Prop :=
| step_zero
    i m rs rs' sp ra
    (ZERO: i.(Int.intval) = 0%Z)
    (RS: rs int_argument_mreg = Vint i)
    (RS' : rs' = Regmap.set AX (Vint (Int.zero)) rs ):
     step (Callstateg sp ra rs m) E0 (Returnstateg rs' m)
| step_read
    i ti m rs rs' sp ra b_mem
    (NZERO: i.(Int.intval) <> 0%Z)
    (FINDM: Genv.find_symbol se _memoized = Some b_mem)
    (LOAD0: Mem.loadv Mint32 m (Vptr b_mem Ptrofs.zero) = Some (Vint i))
    (LOAD1: Mem.loadv Mint32 m (Vptr b_mem (Ptrofs.repr 4)) = Some (Vint ti))
    (RS: rs int_argument_mreg = Vint i)
    (RS' : rs' = Regmap.set AX (Vint ti) rs):
    step (Callstateg sp ra rs m) E0 (Returnstateg rs' m)
| step_call
    i i' m rs rs' sp ra b_mem
    (NZERO: i.(Int.intval) <> 0%Z)
    (FINDM: Genv.find_symbol se _memoized = Some b_mem)
    (LOAD0: Mem.loadv Mint32 m (Vptr b_mem Ptrofs.zero) = Some (Vint i'))
    (NEQ: i <> i')
    (RS: rs int_argument_mreg = Vint i)
    (RS': rs' = Regmap.set BX (Vint i) (Regmap.set int_argument_mreg (Vint (Int.sub i (Int.repr 1))) rs)):
    step (Callstateg sp ra rs m) E0 (Callstatef sp ra rs' m)
|step_return
    b_mem m m' m'' ti rs rs' i
    (FINDM: Genv.find_symbol se _memoized = Some b_mem)
    (STORE0: Mem.storev Mint32 m (Vptr b_mem Ptrofs.zero) (Vint i) = Some m')
    (STORE0: Mem.storev Mint32 m' (Vptr b_mem (Ptrofs.repr 4)) (Vint (Int.add ti i)) = Some m'')
    (RS1: Vint i = rs BX)
    (RS2: Vint ti =  rs AX)
    (LS': rs' = Regmap.set AX (Vint (Int.add ti i)) rs):
    step (Returnstatef rs m) E0 (Returnstateg rs' m'').

Inductive final_state: state -> reply li_mach  -> Prop :=
  | final_state_mach_intro
      m rs:
      final_state (Returnstateg rs m) (mr rs m).

End WITH_SE.

Program Definition BspecM : Smallstep.semantics li_mach li_mach :=
  {|
   Smallstep.skel := erase_program prog;
   Smallstep.state := state;
   Smallstep.activate se :=
     let ge := Genv.globalenv se DemoB.prog in
     {|
       Smallstep.step ge := step ge;
       Smallstep.valid_query q := Genv.is_internal ge (mq_vf q);
       Smallstep.initial_state := initial_state ge;
       Smallstep.at_external := at_external ge;
       Smallstep.after_external := after_external;
       Smallstep.final_state := final_state;
       globalenv := ge;
     |}
   |}.

Definition make_regset_result (ls: Locmap.t) (sg: signature) (r: mreg) : val :=
  if in_dec mreg_eq r (regs_of_rpair (loc_result sg)) then ls (R r) else Vundef.

Section MS.
Variable rs0: Mach.regset.
Variable sp: val.
Variable m0: mem.

Inductive match_states_locset_mach :  CL.state -> state -> Prop :=
  |LM_Callstateg ls ra
    (LS_RS : ls = make_locset rs0 m0 sp)
    (SP: Val.has_type sp Tptr)
    (RA: Val.has_type ra Tptr):
     match_states_locset_mach (CL.Callstateg ls m0) (Callstateg sp ra rs0 m0)
  |LM_Callstatef ls ra rs
    (LS_RS : ls = make_locset rs m0 sp)
    (SP: Val.has_type sp Tptr)
    (RA: Val.has_type ra Tptr):
      match_states_locset_mach (CL.Callstatef ls m0) (Callstatef sp ra rs m0)
  |LM_returnstatef ls rs m_ m i
     (LS_RS : rs AX  = ls (R AX))
(*     (RS: forall r : mreg, is_callee_save r = true -> rs r = rs0 r) *)
     (MEM: Mem.unchanged_on (not_init_args (size_arguments int_int_sg) sp) m_ m)
     (SUP: Mem.support m_ = Mem.support m)
     (TMEM: Mem.unchanged_on (loc_init_args (size_arguments int_int_sg) sp) m0 m):
     match_states_locset_mach (CL.Returnstatef i ls m_) (Returnstatef rs m)
  |LM_returnstateg ls rs m_ m
     (LS_RS : rs AX  = ls (R AX))
     (RS: forall r : mreg, is_callee_save r = true -> rs r = rs0 r)
     (MEM: Mem.unchanged_on (not_init_args (size_arguments int_int_sg) sp) m_ m)
     (SUP: Mem.support m_ = Mem.support m)
     (TMEM: Mem.unchanged_on (loc_init_args (size_arguments int_int_sg) sp) m0 m):
     match_states_locset_mach (CL.Returnstateg ls m_) (Returnstateg rs m).

End MS.

Lemma argument_int_value:
  forall rs m sp i,
    Vint i :: nil =
    (fun p : rpair loc => Locmap.getpair p (make_locset rs m sp)) ## (loc_arguments int_int_sg) ->
    rs int_argument_mreg = Vint i.
Proof.
  intros.
  unfold make_locset in *.
  unfold int_int_sg, loc_arguments, int_argument_mreg in *.
  replace Archi.ptr64 with true in *. simpl in *. destruct Archi.win64. simpl in *.
  congruence. simpl in *. congruence. reflexivity.
Qed.

Lemma size_int_int_sg_0:
  size_arguments int_int_sg = 0.
Proof.
  unfold size_arguments, int_int_sg, loc_arguments. replace Archi.ptr64 with true by reflexivity.
  destruct Archi.win64; simpl;  reflexivity.
Qed.

Theorem locset_mach:
  forward_simulation (cc_locset_mach) (cc_locset_mach) CL.BspecL BspecM.
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *. subst. 
  pose (ms := fun s1 s2 => match_states_locset_mach (lmw_rs w) (lmw_sp w) (lmw_m w) s1 s2 /\ (lmw_sg w) = int_int_sg).
  eapply forward_simulation_step with (match_states := ms); cbn; eauto.
  - intros. inv H. reflexivity.
  - intros. inv H. inv H0. inv H1.
    exists (Callstateg sp ra rs m_). split.
    econstructor; eauto. eapply argument_int_value; eauto.
    red. simpl. split. econstructor; eauto. auto.
    rewrite size_int_int_sg_0 in H4. extlia.
  - intros. inv H. inv H0. inv H1.
    exists (mr rs m0). split.
    econstructor; eauto.
    (* rewrite CL.ls_result_int in LS.
    rewrite LS_RS. eauto. *)
    destruct w. cbn in *. subst lmw_sg.
    econstructor; eauto.
    rewrite CL.loc_result_int. simpl. intros. inv H. auto. inv H0.
    intros. inv H. rewrite size_int_int_sg_0 in H0. extlia.
  - intros. inv H0. inv H. inv H0. destruct w. cbn in *. subst lmw_sg.
    (* set (rs' := Regmap.set int_argument_mreg (Vint (Int.sub i (Int.repr 1))) lmw_rs). *)
    exists (lmw int_int_sg rs lmw_m lmw_sp), (mq (Vptr g_fptr Ptrofs.zero) lmw_sp ra rs lmw_m).
    repeat apply conj; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
      constructor. red. apply size_int_int_sg_0.
    + intros. inv H0. inv H. cbn in *.
      exists (Returnstatef rs' m'). split.
      econstructor; eauto.
      -- eapply argument_int_value; eauto.
      -- admit.
      -- econstructor; eauto.
         econstructor; eauto.
         eapply H6. unfold int_int_sg. unfold loc_result.
         replace Archi.ptr64 with true by reflexivity. simpl.
         eauto.
  - intros. inv H0. inv H; inv H1.
    + exists (Returnstateg (Regmap.set AX (Vint Int.zero) (lmw_rs w)) (lmw_m w)). split.
      econstructor; eauto. eapply argument_int_value; eauto.
      econstructor; eauto. econstructor; eauto with mem.
      intros. rewrite Regmap.gso. eauto.
      destruct r; unfold is_callee_save in H; try congruence.
    + exists (Returnstateg (Regmap.set AX (Vint ti) (lmw_rs w)) (lmw_m w)). split.
      eapply step_read; eauto.
      eapply argument_int_value; eauto. eauto.
      econstructor; eauto.
      econstructor; eauto with mem.
      intros. rewrite Regmap.gso. eauto.
      destruct r; unfold is_callee_save in H; try congruence.
    + eexists. split. eapply step_call; eauto.
      eapply argument_int_value; eauto.
      econstructor; eauto.
      econstructor; eauto.
      { 
        unfold CL.int_loc_argument. unfold int_argument_mreg.
      replace Archi.ptr64 with true by reflexivity.
      apply Axioms.extensionality. intro l.
      destruct (Loc.eq l (R BX)).
        - subst l. rewrite Locmap.gss. unfold make_locset.
          rewrite Regmap.gss. reflexivity.
        - rewrite Locmap.gso.
          2: { destruct l; try congruence; simpl; eauto. }
          destruct (Loc.eq l (if Archi.win64 then R CX else R DI)).
          + subst l. rewrite Locmap.gss.
          unfold make_locset. destruct Archi.win64.
          rewrite Regmap.gso; try congruence.
          rewrite Regmap.gss. reflexivity.
          rewrite Regmap.gso; try congruence.
          rewrite Regmap.gss. reflexivity.
          + rewrite Locmap.gso.
            unfold make_locset.
          destruct l. rewrite Regmap.gso; try congruence. rewrite Regmap.gso. eauto.
          destruct Archi.win64; destruct r; try congruence.
          reflexivity.
          destruct l. destruct Archi.win64; destruct r; try congruence.
          destruct Archi.win64; simpl; eauto.
      }
    + set (rs' := Regmap.set AX (Vint (Int.add ti i)) rs).
      edestruct Mem.store_mapped_unchanged_on as [m'2 [STORE0' UNC1]]. apply MEM. all: eauto.
      intros. red. intro. inv H. rewrite size_int_int_sg_0 in H1. extlia.
      edestruct Mem.store_mapped_unchanged_on as [m'3 [STORE1' UNC2]]. apply UNC1. all: eauto.
      intros. red. intro. inv H. rewrite size_int_int_sg_0 in H1. extlia.
      eexists; split.
      eapply step_return; eauto.
      admit.
      rewrite CL.loc_result_int in LS. cbn in *. rewrite LS_RS. eauto.
      econstructor; eauto.
      econstructor; eauto.
      -- intros. admit.
      -- apply Mem.support_store in STORE0. apply Mem.support_store in STORE1.
         apply Mem.support_store in STORE0'. apply Mem.support_store in STORE1'.
         congruence.
      -- constructor. inversion TMEM.
         apply Mem.support_store in STORE0'. apply Mem.support_store in STORE1'.
         rewrite STORE1', STORE0'. eauto.
         intros. inv H. rewrite size_int_int_sg_0 in H3. extlia.
         intros. inv H. rewrite size_int_int_sg_0 in H3. extlia.
  - constructor. intros. inv H.
Admitted.
End LM.

Module MA.
Axiom not_win64 : Archi.win64 = false.

Definition int_argument_preg := IR RDI.

Section MS.
Variable rs0: regset.
Variable s0: sup.

Inductive match_states' :  LM.state -> Asm.state -> Prop :=
  |LM_callstateg mrs m
    (MRS_RS : forall r, mrs r = rs0 (preg_of r))
    (SUP: s0 = Mem.support m):
     match_states' (LM.Callstateg (rs0 RSP) (rs0 RA) mrs m) (State rs0 m true)
  |LM_callstatef mrs rs m
    (MRS_RS : forall r, mrs r = rs0 (preg_of r))
    (SUP: s0 = Mem.support m):
      match_states' (LM.Callstatef (rs0 RSP) (rs0 RA) mrs m) (State rs m true)
  |LM_returnstatef mrs rs m
     (MRS_RS : forall r, mrs r = rs (preg_of r))
     (RSP' : rs RSP = rs0 RSP)
     (PC': rs PC = rs0 RA)
     (SUP: Mem.sup_include s0 (Mem.support m)):
     match_states' (LM.Returnstatef mrs m) (State rs m true)
  |LM_returnstateg mrs rs m
     (MRS_RS : forall r, mrs r = rs (preg_of r))
     (RSP' : rs RSP = rs0 RSP)
     (PC': rs PC = rs0 RA)
     (SUP: Mem.sup_include s0 (Mem.support m)):
     match_states' (LM.Returnstateg mrs m) (State rs m false).

Definition match_states (s1: LM.state) (s2: sup * Asm.state) :=
  match_states' s1 (snd s2) /\ s0 = fst s2.
End MS.

Lemma int_argument_preg_of:
  int_argument_preg = preg_of LM.int_argument_mreg.
Proof.
  unfold LM.int_argument_mreg, int_argument_preg, preg_of.
  rewrite not_win64. reflexivity.
Qed.

Lemma int_result_preg_of:
  IR RAX = preg_of AX.
Proof.
  reflexivity.
Qed.

Theorem mach_asm:
  forward_simulation (cc_mach_asm) (cc_mach_asm) LM.BspecM (Asm.semantics DemoB.prog).
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *. subst.
  pose (ms := fun s1 s2 => match_states (fst w) (snd w) s1 s2
                         /\ (fst w) PC <> Vundef /\ (fst w RA <> Vundef)
                         /\ valid_blockv (snd w) (fst w RSP)).
  eapply forward_simulation_star with (match_states := ms); cbn in *; eauto.
  - intros. simpl. cbn in *. destruct w. inv H. reflexivity.
  - intros. inv H0. destruct w. inv H. exists (Mem.support m, (State r m true)).
    split. simpl. split; eauto.
    econstructor; eauto.
    admit.
    inv H8. congruence.
    constructor; eauto.
    constructor; eauto.
    constructor; eauto.
  - intros. destruct w. inv H. inv H1. inv H0. destruct s2. inv H.
    cbn in *. subst. destruct H2 as [A [B C]].
    exists (rs0,m). split. econstructor; eauto.
    econstructor; eauto.
  - intros. inv H. inv H1. inv H. destruct s2. destruct w. cbn in *. subst.
    exists (rs.),()
Admitted.
      (*call*)

Theorem Bproof :
  forward_simulation cc_compcert cc_compcert Bspec (Asm.semantics DemoB.prog).
Proof.
  unfold cc_compcert.
  rewrite <- (cc_compose_assoc wt_c lessdef_c) at 1.
  rewrite <- (cc_compose_assoc wt_c lessdef_c).
  eapply compose_forward_simulations.
  eapply self_simulation_C.
  eapply compose_forward_simulations.
  eapply self_simulation_wt.
  repeat eapply compose_forward_simulations.
  eapply CL.c_locset. eapply LM.locset_mach. eapply mach_asm.
  eapply semantics_asm_rel; eauto.
Qed.





(*
Module MA.

Inductive state :=
  |Callstate (rs: regset) (m:mem)
  |Interstate (rs: regset) (m: mem)
  |Returnstate (rs: regset) (m:mem).

Section WITH_SE.
  Context (se: Genv.symtbl).

(* Compute CL.int_loc_argument. *)
Definition int_argument_preg := if Archi.win64 then IR RCX else IR RDI.

(* cc_mach_asm_mr *)

Inductive initial_state : query li_asm -> state -> Prop :=
| initial_state_intro
    m b i rs
    (SYMB: Genv.find_symbol se g_id = Some b)
(*    (RANGE: 0 <= i.(Int.intval) < MAX) *)
    (RS : rs int_argument_preg = Vint i)
    (PC: rs PC = Vptr b Ptrofs.zero)
    (RA: rs RA <> Vundef)
    (RSP: rs RSP <> Vundef):
    initial_state (rs,m) (Callstate rs m).

Inductive at_external: state -> query li_asm -> Prop :=
| at_external_intro
    g_fptr i m rs rs'
    (FINDG: Genv.find_symbol se f_id = Some g_fptr)
    (RS: rs int_argument_preg = Vint i)
    (RS': rs' = (rs # int_argument_preg <- (Vint (Int.sub i (Int.repr 1)))) # PC <- (Vptr g_fptr Ptrofs.zero)):
    at_external (Interstate rs m)
                (rs',m).

Inductive after_external : state -> reply li_asm -> state -> Prop :=
| after_external_intro
    i m rs rs' rs'' m' b_mem m'' m''' ti
    (RS: rs int_argument_preg = Vint i)
    (RS' : rs' (IR RAX) = Vint ti)
    (RS'' : rs'' = Pregmap.set (IR RAX) (Vint (Int.add ti i)) rs') (*more here?*)
    (SUP : Mem.sup_include (Mem.support m) (Mem.support m'))
    (FINDM: Genv.find_symbol se _memoized = Some b_mem)
    (STORE0: Mem.storev Mint32 m' (Vptr b_mem Ptrofs.zero) (Vint i) = Some m'')
    (STORE0: Mem.storev Mint32 m'' (Vptr b_mem (Ptrofs.repr 4)) (Vint (Int.add ti i)) = Some m'''):
    after_external (Interstate rs m) (rs',m') (Returnstate rs'' m''').

Inductive step : state -> trace -> state -> Prop :=
| step_zero
    i m rs rs'
    (ZERO: i.(Int.intval) = 0%Z)
    (RS: rs int_argument_preg = Vint i)
    (RS': rs' = (rs # (IR RAX) <- (Vint (Int.zero))) # PC <- (rs RA)):
    step (Callstate rs m) E0 (Returnstate rs' m)
| step_read
    i m rs rs' ti b_mem
    (RS: rs int_argument_preg = Vint i)
    (RS': rs' = (rs # (IR RAX) <- (Vint ti)) # PC <- (rs RA))
    (NZERO: i.(Int.intval) <> 0%Z)
    (FINDM: Genv.find_symbol se _memoized = Some b_mem)
    (LOAD0: Mem.loadv Mint32 m (Vptr b_mem Ptrofs.zero) = Some (Vint i))
    (LOAD1: Mem.loadv Mint32 m (Vptr b_mem (Ptrofs.repr 4)) = Some (Vint ti)):
    step (Callstate rs m) E0 (Returnstate rs' m)
| step_call
    i m rs b_mem i'
    (NZERO: i.(Int.intval) <> 0%Z)
    (RS: rs int_argument_preg = Vint i)
    (FINDM: Genv.find_symbol se _memoized = Some b_mem)
    (LOAD0: Mem.loadv Mint32 m (Vptr b_mem Ptrofs.zero) = Some (Vint i'))
    (NEQ: i <> i'):
    step (Callstate rs m) E0 (Interstate rs m).

Inductive final_state: state -> reply li_asm  -> Prop :=
  | final_state_intro
      s m rs
      (RS: rs (IR RAX) = Vint s):
      final_state (Returnstate rs m) (rs, m).

End WITH_SE.

Program Definition BspecA : Smallstep.semantics li_asm li_asm :=
  {|
   Smallstep.skel := erase_program prog;
   Smallstep.state := state;
   Smallstep.activate se :=
     let ge := Genv.globalenv se DemoB.prog in
     {|
       Smallstep.step ge := step ge;
       Smallstep.valid_query q := Genv.is_internal ge (asm_entry q);
       Smallstep.initial_state := initial_state ge;
       Smallstep.at_external := at_external ge;
       Smallstep.after_external := after_external ge;
       Smallstep.final_state := final_state;
       globalenv := ge;
     |}
   |}.

Definition make_regset_result (ls: Locmap.t) (sg: signature) (r: mreg) : val :=
  if in_dec mreg_eq r (regs_of_rpair (loc_result sg)) then ls (R r) else Vundef.


Theorem mach_asm:
  forward_simulation (cc_mach_asm) (cc_mach_asm) LM.BspecM BspecA.
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *. subst.
  pose (ms := fun s1 s2 => match_states_mach_asm (fst w) (snd w) s1 s2
                         /\ (fst w) PC <> Vundef /\ (fst w RA <> Vundef)
                         /\ valid_blockv (snd w) (fst w RSP)).
  eapply forward_simulation_step with (match_states := ms); cbn; destruct w; eauto.
  - intros. inv H. simpl. reflexivity.
  - intros. inv H. inv H0.
    exists (Callstate r m). split.
    econstructor; eauto. rewrite int_argument_preg_of.
    rewrite <- H4; eauto.
    intro. rewrite H in H2. inv H2.
    red. econstructor; eauto.
    econstructor; eauto.
  - intros. inv H0. inv H. inv H0. cbn in *.
    exists (rs0 , m). split.
    econstructor; eauto.
    rewrite MRS_RS in RS. eauto.
    econstructor; eauto.
  - intros. inv H0. inv H. cbn in *. inv H0. destruct H1 as (A & B & C).
    set (s:= Mem.support m).
    set (r' := r # int_argument_preg <- (Vint (Int.sub i (Int.repr 1))) # PC <- (Vptr g_fptr Ptrofs.zero) ).
    exists (r',s), (r',m). repeat apply conj; eauto.
    + econstructor; eauto.
      rewrite int_argument_preg_of. rewrite <- MRS_RS. eauto.
      unfold r'. reflexivity.
    + assert (VF': Vptr g_fptr Ptrofs.zero = r' PC).
      unfold r'. rewrite Pregmap.gss. eauto.
      assert (SP': r RSP = r' RSP).
      unfold r'. rewrite !Pregmap.gso. eauto.
      unfold int_argument_preg. destruct Archi.win64; congruence. congruence.
      assert (RA': r RA = r' RA).
      unfold r'. rewrite !Pregmap.gso. eauto.
      unfold int_argument_preg. destruct Archi.win64; congruence. congruence.
      rewrite VF',SP',RA'. unfold s.
      econstructor; eauto.
      unfold r'. rewrite Pregmap.gss. congruence.
      rewrite <- SP'. eauto.
      congruence.
      intros r0. destruct (mreg_eq r0 (LM.int_argument_mreg)).
      -- subst. rewrite Regmap.gss. unfold r'. rewrite int_argument_preg_of. rewrite Pregmap.gso.
         rewrite Pregmap.gss. eauto. unfold LM.int_argument_mreg. destruct Archi.win64; simpl; congruence.
      -- rewrite Regmap.gso; eauto. unfold r'.
         rewrite !Pregmap.gso. eauto. unfold LM.int_argument_mreg, int_argument_preg in *.
         destruct Archi.win64; destruct r0; simpl; congruence.
         destruct r0; simpl; congruence.
    + intros. inv H0. rewrite RS in RS0.  inv RS0. inv H. (* why 2 RS? *)
      set (rs'2 := rs'0 # RAX <- (Vint (Int.add ti i0))).
      exists (Returnstate rs'2 m''').
      split. econstructor; eauto.
      rewrite int_argument_preg_of. rewrite <- MRS_RS. eauto.
      rewrite H6 in RS'. eauto.
      unfold rs'2. reflexivity.
      constructor; eauto.
      constructor; eauto.
      -- unfold rs'2. intro mreg.
         destruct (mreg_eq mreg AX).
         subst. rewrite Regmap.gss. simpl.
         rewrite Pregmap.gss. eauto.
         rewrite Regmap.gso; eauto.
         rewrite Pregmap.gso; eauto.
         destruct mreg; simpl; try congruence.
      -- unfold rs'2. rewrite Pregmap.gso; try congruence.
         rewrite H2. unfold r'. rewrite Pregmap.gso; try congruence.
         rewrite Pregmap.gso. eauto.
         unfold int_argument_preg. destruct Archi.win64; congruence.
      -- unfold rs'2. rewrite Pregmap.gso; try congruence.
         rewrite H3. unfold r'. rewrite Pregmap.gso; try congruence.
         rewrite Pregmap.gso. eauto.
         unfold int_argument_preg. destruct Archi.win64; congruence.
      -- rewrite <- (Mem.support_storev _ _ _ _ _ STORE1).
         rewrite <- (Mem.support_storev _ _ _ _ _ STORE0). eauto.
  - intros. inv H; inv H0; inv H; destruct H1 as (A & B & C). cbn in *.
    + eexists. split.
      econstructor; eauto.
      rewrite int_argument_preg_of. rewrite <- MRS_RS. eauto.
      econstructor; eauto.
      econstructor; eauto.
      intros r0. destruct (mreg_eq r0 AX).
      -- subst. simpl.
         rewrite Regmap.gss.
         rewrite Pregmap.gso; try congruence.
         rewrite Pregmap.gss. reflexivity.
      -- rewrite !Pregmap.gso; try congruence.
         rewrite Regmap.gso; try congruence.
         destruct r0; simpl; congruence.
         destruct r0; simpl; congruence.
      -- subst s. eauto with mem.
    + eexists. split.
      eapply step_read; eauto.
      rewrite int_argument_preg_of. rewrite <- MRS_RS. eauto.
      econstructor; eauto.
      econstructor; eauto.
      intros r0. destruct (mreg_eq r0 AX).
      -- subst. simpl.
         rewrite Regmap.gss.
         rewrite Pregmap.gso; try congruence.
         rewrite Pregmap.gss. reflexivity.
      -- rewrite !Pregmap.gso; try congruence.
         rewrite Regmap.gso; try congruence.
         destruct r0; simpl; congruence.
         destruct r0; simpl; congruence.
      -- cbn in *. subst s. eauto with mem.
    + cbn in *. exists (Interstate r m). split.
      econstructor; eauto. rewrite int_argument_preg_of. rewrite <- MRS_RS. eauto.
      econstructor; eauto.
      econstructor; eauto.
  - constructor. intros. inv H.
Qed.

End MA.
*)
(*
Inductive match_states : MA.state -> (sup * Asm.state) -> Prop :=
  | match_states_callstate rs trs m tm
      (MRS : forall r, Val.lessdef (rs r) (trs r))
      (MMEM : Mem.extends m tm):
      match_states (MA.Callstate rs m) ((Mem.support m),(State trs tm true))
  | match_states_interstate rs trs m tm
      (MRS : forall r, Val.lessdef (rs r) (trs r))
      (MMEM : Mem.extends m tm):
      match_states (MA.Interstate rs m) ((Mem.support m),(State trs tm true))
  | match_states_returnstate rs trs m tm
      (MRS : forall r, Val.lessdef (rs r) (trs r))
      (MMEM : Mem.extends m tm):
      match_states (MA.Returnstate rs m) ((Mem.support m),(State trs tm false)).

Definition measure (s: MA.state) : nat :=
  match s with
  | MA.Callstate _ _ => 2%nat
  | MA.Interstate  _ _ => 1%nat
  | MA.Returnstate  _ _ => 0%nat
  end.
*)
(* the example asm program is not under win64 architecture *)
Axiom not_win64 : Archi.win64 = false.

Lemma int_DI: MA.int_argument_preg = IR RDI.
Proof. unfold MA.int_argument_preg. rewrite not_win64. reflexivity. Qed.

Theorem asm_simulation_ext:
  forward_simulation (cc_asm ext) (cc_asm ext) MA.BspecA (Asm.semantics DemoB.prog).
Proof.
  constructor.
  econstructor.
  reflexivity.
  intros se1 se2 w Hse Hse1.
  instantiate (3 := MA.state).
  instantiate (2 := ltof MA.state measure).
  set (ms := fun s1 s2 => match_states s1 s2).
  apply forward_simulation_star with (match_states := ms).
  - intros. destruct q1, q2. inv H. simpl. destruct H1 as [rPC MEM]. cbn in *.
    generalize (H0 PC). intro Hpc.
    apply val_inject_lessdef_eqrel in Hpc.
    inv Hpc; try congruence.
  - intros.
    intros. destruct q1, q2. inv H. destruct H2 as [rPC MEM]. cbn in *.
    inv H0.
    exists ((Mem.support m),(State r0 m0 true)). repeat apply conj; eauto.
    + econstructor; eauto.
      generalize (H1 Asm.PC). intro Hpc. apply val_inject_lessdef_eqrel in Hpc.
      inv Hpc; try congruence. rewrite PC.
      {
        instantiate (1:= func_g). admit. (*ok, need some effort *)
      }
      generalize (H1 SP). intro Hsp. apply val_inject_lessdef_eqrel in Hsp.
      inv Hsp; congruence.
      generalize (H1 Asm.RA). intro Hra. apply val_inject_lessdef_eqrel in Hra.
      inv Hra; congruence.
    + inversion MEM. congruence.
    + econstructor; eauto. intros. apply val_inject_lessdef_eqrel; eauto.
  - intros.
    inv H0. inv H. exists (trs,tm).
    split.
    econstructor; eauto. exists tt. split. reflexivity.
    econstructor; eauto. intros. eapply val_inject_lessdef_eqrel; eauto.
  - intros. inv H0. inv H.
    exists tt, (trs,tm). repeat apply conj; eauto.
    + inv Hse. econstructor. admit.
    + admit.
      (*
      intros. simpl. eapply val_inject_lessdef_eqrel; eauto.
      destruct (preg_eq r PC). subst.
      rewrite !Pregmap.gss. constructor; eauto.
      rewrite int_DI in *.
      destruct (preg_eq r RDI). subst.
      rewrite Pregmap.gso; try congruence. rewrite Pregmap.gss.
      rewrite Pregmap.gso; try congruence. rewrite Pregmap.gss.
      constructor; eauto.
      rewrite !Pregmap.gso; try congruence. eauto.
      *)
    + rewrite Pregmap.gss. congruence.
    + intros. inv H. inv H1. inv H0. destruct r2. inv H2.
      simpl. exists (Mem.support m, State r m0 false).
      admit. (*wrong now*)
  - intros. inv H; inv H0.
    + (*zero_big_step *)
      left. eexists. admit. (*split.
      econstructor. simpl. instantiate (2 := ((Mem.support m) , (Asm.State trs tm true))).
      simpl. split; eauto.
      econstructor;  admit.
      admit.*)
    + (*read_big_step*)
      left. eexists. admit.
    + right. split; eauto. split; eauto.
      constructor; eauto.
  - auto using well_founded_ltof.
Admitted.
      (*call*)

Theorem asm_simulation_inj:
  forward_simulation (cc_asm inj) (cc_asm inj) MA.BspecA (Asm.semantics DemoB.prog).
Proof.
  intros.
  assert (H : ccref (cc_asm ext @ cc_asm inj) (cc_asm inj)).
  rewrite <- cc_asm_compose. rewrite ext_inj. reflexivity.
  rewrite <- H at 1.
  rewrite <- ext_inj at 2. rewrite cc_asm_compose.
  eapply compose_forward_simulations.
  eapply asm_simulation_ext.
  eapply semantics_asm_rel.
Qed.

Theorem Bproof :
  forward_simulation cc_compcert cc_compcert Bspec (Asm.semantics DemoB.prog).
Proof.
  unfold cc_compcert.
  rewrite <- (cc_compose_assoc wt_c lessdef_c) at 1.
  rewrite <- (cc_compose_assoc wt_c lessdef_c).
  eapply compose_forward_simulations.
  eapply self_simulation_C.
  eapply compose_forward_simulations.
  eapply self_simulation_wt.
  repeat eapply compose_forward_simulations.
  eapply CL.c_locset. eapply LM.locset_mach. eapply MA.mach_asm.
  eapply asm_simulation_inj.
Qed.

