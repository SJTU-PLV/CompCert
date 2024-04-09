Require Import Coqlib.
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import CKLR.
Require Import LanguageInterface.
Require Import Smallstep.

(* Require Import RelationClasses. *)
Class Lens (T A: Type) :=
  {
    get : T -> A;
    set : T -> A -> T;
    get_set : forall t a, get (set t a) = a;
    set_get : forall t, set t (get t) = t;
    set_set : forall t a1 a2, set (set t a1) a2 = set t a2;
  }.

Program Instance lens_id {T: Type} : Lens T T :=
  {
    get t := t;
    set _ t := t;
  }.

Program Instance lens_fst {U V} : Lens (U * V) U :=
  {
    get '(u, v) := u;
    set '(_, v) u := (u, v);
  }.

Program Instance lens_snd {U V} : Lens (U * V) V :=
  {
    get '(u, v) := v;
    set '(u, _) v := (u, v);
  }.

Class World (T: Type) :=
  {
    w_state : Type;
    w_lens : Lens T w_state;
    w_acc : w_state -> w_state -> Prop;
    w_acc_trans : PreOrder  w_acc;
  }.

Existing Instance w_lens.
Existing Instance w_acc_trans.
Arguments w_state {_} _.
Arguments w_acc {_ _}.
Infix "*->" := w_acc (at level 60, no associativity).

Module GS.

  Record callconv {li1 li2} :=
  mk_callconv {
    ccworld : Type;
    ccworld_world : World ccworld;
    match_senv: ccworld -> Genv.symtbl -> Genv.symtbl -> Prop;
    match_query: ccworld -> query li1 -> query li2 -> Prop;
    match_reply: ccworld -> reply li1 -> reply li2 -> Prop;

    match_senv_public_preserved:
      forall w se1 se2,
        match_senv w se1 se2 ->
        forall id, Genv.public_symbol se2 id = Genv.public_symbol se1 id;
    match_senv_valid_for:
      forall w se1 se2 sk,
        match_senv w se1 se2 ->
        Genv.valid_for sk se1 ->
        Genv.valid_for sk se2;
    }.

  Arguments callconv: clear implicits.
  (* Existing Instance ccworld_world | 3. *)
  
  Definition gworld {li1 li2}(cc: callconv li1 li2) := w_state (ccworld_world cc).
  
Section FSIM.

    Context {li1 li2} (cc: callconv li1 li2).
    Context (se1 se2: Genv.symtbl).
    Context (wb: ccworld cc).
    Context {state1 state2: Type}.

    Let gw_type := gworld cc.
    
    Record fsim_properties
           (L1: lts li1 li1 state1) (L2: lts li2 li2 state2)
           (index: Type) (order: index -> index -> Prop)
           (match_states: gw_type -> index -> state1 -> state2 -> Prop) :=
      {
        fsim_match_initial_states:
          forall q1 q2 s1, match_query cc wb q1 q2 -> initial_state L1 q1 s1 ->
          match_senv cc wb se1 se2 ->
          exists i, exists s2, initial_state L2 q2 s2 /\ match_states (get wb) i s1 s2;
        fsim_match_final_states:
          forall gw i s1 s2 r1, match_states gw i s1 s2 -> final_state L1 s1 r1 ->
          exists r2, final_state L2 s2 r2 /\
          match_reply cc (set wb gw) r1 r2;
        fsim_match_external:
          forall gw i s1 s2 q1, match_states gw i s1 s2 -> at_external L1 s1 q1 ->
          exists wa q2 , at_external L2 s2 q2 /\ exists gw', gw *-> gw' /\ get wa = gw' /\
          match_query cc wa q1 q2 /\ match_senv cc wa se1 se2 /\
          forall r1 r2 s1' gw'', gw' *-> gw'' -> match_reply cc (set wa gw'') r1 r2 ->
          after_external L1 s1 r1 s1' ->
          exists i' s2', after_external L2 s2 r2 s2' /\
          exists gw''' , gw'' *-> gw''' /\ match_states gw''' i' s1' s2';
        fsim_simulation:
          forall s1 t s1', Step L1 s1 t s1' ->
          forall gw i s2, match_states gw i s1 s2 ->
          exists i', exists s2', (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i)) /\
          exists gw', gw *-> gw' /\ match_states gw' i' s1' s2';
      }.
    Arguments fsim_properties : clear implicits.

    Lemma fsim_simulation':
      forall L1 L2 index order match_states, fsim_properties L1 L2 index order match_states ->
      forall i s1 t s1', Step L1 s1 t s1' ->
      forall gw s2, match_states gw i s1 s2 ->
      exists i' gw', gw *-> gw' /\
      ((exists s2', Plus L2 s2 t s2' /\ match_states gw' i' s1' s2')
      \/ (order i' i /\ t = E0 /\ match_states gw' i' s1' s2)).
    Proof.
      intros. exploit @fsim_simulation; eauto.
      intros (i' & s2' & A & wi & Hi & B).
      exists i', wi. repeat split; eauto.
      destruct A.
      left; exists s2'; auto.
      destruct H2. inv H2.
      right; eauto.
      left; exists s2'; split; auto. econstructor; eauto.
    Qed.

    Section SIMULATION_SEQUENCES.

      Context L1 L2 index order match_states
              (S: fsim_properties L1 L2 index order match_states).

      Lemma simulation_star:
        forall s1 t s1', Star L1 s1 t s1' ->
        forall gw i s2, match_states gw i s1 s2 ->
        exists gw' i', exists s2', Star L2 s2 t s2' /\
        gw *-> gw'  /\ match_states gw' i' s1' s2'.
      Proof.
        induction 1; intros.
        eexists _, i; exists s2; repeat split; auto. apply star_refl.
        reflexivity. assumption.
        exploit fsim_simulation; eauto.
        intros (i' & s2' & A & wi & Hi & B).
        exploit IHstar; eauto.
        intros (wj & i'' & s2'' & Hx & Hj & C).
        exists wj, i''; exists s2''; repeat split; auto.
        eapply star_trans; eauto.
        intuition auto. apply plus_star; auto.
        all: etransitivity; eauto.
      Qed.

      
    End SIMULATION_SEQUENCES.
  End FSIM.

  Arguments fsim_properties  {_ _} _ _ _ _  {_ _} L1 L2 index order match_states.

  Record fsim_components {li1 li2} (cc: callconv li1 li2) L1 L2 :=
    Forward_simulation {
        fsim_index: Type;
        fsim_order: fsim_index -> fsim_index -> Prop;
        fsim_match_states: _;

        fsim_skel: skel L1 = skel L2;
        fsim_lts se1 se2 w:
          GS.match_senv cc w se1 se2 ->
          Genv.valid_for (skel L1) se1 ->
          fsim_properties cc se1 se2 w (activate L1 se1) (activate L2 se2)
            fsim_index fsim_order (fsim_match_states se1 se2 w);
        fsim_order_wf:
          well_founded fsim_order;
      }.

  Arguments Forward_simulation {_ _ cc L1 L2 fsim_index}.

  Definition forward_simulation {li1 li2} cc L1 L2 :=
    inhabited (@fsim_components li1 li2 cc L1 L2).
  
  Arguments Forward_simulation {_ _ cc L1 L2 fsim_index}.

End GS.

(** Definition of new CAinjp *)
Require Import Conventions Mach Asm.
Require Import InjectFootprint CA.

Definition get_injp := cajw_injp.

Definition set_injp (wa: cc_cainjp_world) (w : injp_world) :=
  match wa with cajw w' sig rs => cajw w sig rs end.

Program Instance lens_injp : Lens (cc_cainjp_world) injp_world :=
  {
    get := get_injp;
    set := set_injp;
  }.
Next Obligation. destruct t. reflexivity. Qed.
Next Obligation. destruct t. reflexivity. Qed.
Next Obligation. destruct t. reflexivity. Qed.

Program Instance CAworld : World cc_cainjp_world :=
    {
      w_state := injp_world;
      w_lens := lens_injp;
      w_acc := injp_acc;
      w_acc_trans := injp_acc_preo;
    }.
     
Inductive cc_c_asm_injp_mr : cc_cainjp_world -> c_reply -> reply li_asm -> Prop :=
  cc_c_asm_injp_mr_intro sg res  j' m' tm' Hm' (rs rs' :regset) :
     let tres := rs_getpair (map_rpair preg_of (loc_result sg)) rs' in
     Val.inject j' res tres ->
     (forall r, is_callee_save r = true -> rs' (preg_of r) = rs (preg_of r)) ->
     (*(forall b ofs, loc_init_args (size_arguments sg) tsp b ofs ->
              loc_out_of_reach j m b ofs) -> *)
     rs'#SP = rs#SP -> rs'#PC = rs#RA ->
     cc_c_asm_injp_mr
       (cajw (injpw j' m' tm' Hm') sg rs)
       (cr res m')
       (rs', tm').

Program Definition cc_c_asm_injp_new : GS.callconv li_c li_asm :=
  {|
    GS.ccworld := cc_cainjp_world;
    GS.ccworld_world := CAworld;
    GS.match_senv w := match_stbls injp (cajw_injp w);
    GS.match_query := cc_c_asm_injp_mq;
    GS.match_reply := cc_c_asm_injp_mr
  |}.
Next Obligation.
  inv H. inv H1. eauto.
Qed.
Next Obligation.
  inv H.
  eapply Genv.valid_for_match in H2.
  apply H2. eauto.
Qed.



(** Legacy  * )
(*
Record callconvnew {li1 li2} :=
  mk_callconv {
    ccworld : Type;
    wacc : relation ccworld;
    match_senv: ccworld -> Genv.symtbl -> Genv.symtbl -> Prop;
    match_query: ccworld -> query li1 -> query li2 -> Prop;
    match_reply: ccworld -> reply li1 -> reply li2 -> Prop;

    match_senv_public_preserved:
      forall w se1 se2,
        match_senv w se1 se2 ->
        forall id, Genv.public_symbol se2 id = Genv.public_symbol se1 id;
    match_senv_valid_for:
      forall w se1 se2 sk,
        match_senv w se1 se2 ->
        Genv.valid_for sk se1 ->
        Genv.valid_for sk se2;
    wacc_preorder:
      PreOrder wacc;
      
    }.

Arguments callconvnew: clear implicits.

(**   *)
Section FSIM.

Context {li1 li2} (cc: callconvnew li1 li2).
Context (se1 se2: Genv.symtbl) (w: ccworld cc).
Context {state1 state2: Type}.

(** The general form of a forward simulation. *)

Record fsim_properties (L1: lts li1 li1 state1) (L2: lts li2 li2 state2) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> (ccworld cc) -> state1 -> state2 -> Prop) : Prop := {
    fsim_match_valid_query:
      forall q1 q2, match_query cc w q1 q2 ->
      valid_query L2 q2 = valid_query L1 q1;
    fsim_match_initial_states:
      forall q1 q2 s1, match_query cc w q1 q2 -> initial_state L1 q1 s1 ->
      exists i, exists w', exists s2, initial_state L2 q2 s2 /\ match_states i w' s1 s2 /\ wacc cc w w';
    fsim_match_final_states:
      forall i w s1 s2 r1, match_states i w s1 s2 -> final_state L1 s1 r1 ->
      exists r2 w', final_state L2 s2 r2 /\ match_reply cc w' r1 r2 /\ wacc cc w w';
    fsim_match_external:
      forall i w s1 s2 q1, match_states i w s1 s2 -> at_external L1 s1 q1 ->
      exists w' q2, at_external L2 s2 q2 /\ match_query cc w' q1 q2 /\ match_senv cc w' se1 se2 /\ wacc cc w w' /\
      forall r1 r2 s1' w'', match_reply cc w'' r1 r2 -> after_external L1 s1 r1 s1' -> wacc cc w' w'' ->
      exists i' s2' w''', after_external L2 s2 r2 s2' /\ match_states i' w''' s1' s2' /\ wacc cc w'' w''';
    fsim_simulation:
      forall s1 t s1', Step L1 s1 t s1' ->
      forall i s2 w, match_states i w s1 s2 ->
      exists i', exists s2', exists w',
         (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
      /\ match_states i' w' s1' s2' /\ wacc cc w w';
  }.

Arguments fsim_properties : clear implicits.

(** An alternate form of the simulation diagram *)
End FSIM.

Arguments fsim_properties {_ _} _ _ _ _ {_ _} L1 L2 index order match_states.

Record fsim_components {li1 li2} (cc: callconvnew li1 li2) L1 L2 :=
  Forward_simulation {
    fsim_index: Type;
    fsim_order: fsim_index -> fsim_index -> Prop;
    fsim_match_states: _;

    fsim_skel:
      skel L1 = skel L2;
    fsim_lts se1 se2 w:
      @match_senv li1 li2 cc w se1 se2 ->
      Genv.valid_for (skel L1) se1 ->
      fsim_properties cc se1 se2 w (activate L1 se1) (activate L2 se2)
        fsim_index fsim_order (fsim_match_states se1 se2);
    fsim_order_wf:
      well_founded fsim_order;
  }.

Arguments Forward_simulation {_ _ cc L1 L2 fsim_index}.

Definition forward_simulation {li1 li2} cc L1 L2 :=
  inhabited (@fsim_components li1 li2 cc L1 L2).

(** Definition of new CAinjp *)

Require Import Conventions Mach Asm.
Require Import InjectFootprint CA.

Inductive CAinjp_acc : cc_cainjp_world -> cc_cainjp_world -> Prop :=
  cainjp_acc_intro : forall w1 sig w2 rs1 rs2
    (INJPACC: injp_acc w1 w2)
    (CALLEESAVE: (forall r, is_callee_save r = true -> rs2 (preg_of r) = rs1 (preg_of r)))
    (RSPSAVE: rs2 # SP = rs1 # SP)
    (PCSAVE: rs2 # PC = rs1 # RA),
    CAinjp_acc (cajw w1 sig rs1) (cajw w2 sig rs2).  

Global Instance cainjp_acc_pero:
  PreOrder CAinjp_acc.
Proof.
  split.
  - intros [[j m1 m2 Hm] sig rs].
    constructor; eauto. reflexivity.
    
Inductive cc_c_asm_injp_mr : cc_cainjp_world -> c_reply -> reply li_asm -> Prop :=
  cc_c_asm_injp_mr_intro sg res  j' m' tm' Hm' (rs' :regset) :
     let tres := rs_getpair (map_rpair preg_of (loc_result sg)) rs' in
     Val.inject j' res tres ->
     (* uselss? (forall b ofs, loc_init_args (size_arguments sg) tsp b ofs ->
              loc_out_of_reach j m b ofs) -> *)
     cc_c_asm_injp_mr
       (cajw (injpw j' m' tm' Hm') sg rs')
       (cr res m')
       (rs', tm').

Program Definition cc_c_asm_injp_new : callconvnew li_c li_asm :=
  {|
    match_senv w := match_stbls injp (cajw_injp w);
    wacc := CAinjp_acc;
    match_query := cc_c_asm_injp_mq;
    match_reply := cc_c_asm_injp_mr
  |}.
Next Obligation.
  inv H. inv H1. eauto.
Qed.
Next Obligation.
  inv H.
  eapply Genv.valid_for_match in H2.
  apply H2. eauto.
Qed.
Next Obligation.
 *)
*)
