Require Import Coqlib.
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import CKLR.
Require Import LanguageInterface.
Require Import Smallstep.

Set Implicit Arguments.

Require Import RelationClasses.
Require Import Relations.


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

Program Instance lens_unit {T} : Lens T unit :=
  {
    get _ := tt;
    set t tt := t;
  }.
Next Obligation. intros; try easy. now destruct a. Defined.

Program Instance lens_prod {T S A B: Type} `(Lens T A) `(Lens S B) : Lens (T * S) (A * B) :=
  {
    get '(t, s) := (get t, get s);
    set '(t, s) '(a, b) := (set t a, set s b);
  }.
Next Obligation. now rewrite !get_set. Defined.
Next Obligation. now rewrite !set_get. Defined.
Next Obligation. now rewrite !set_set. Defined.

Program Instance lens_comp {U V W: Type} `(Lens U V) `(Lens V W) : Lens U W :=
  {
    get u := get (get u);
    set u w := set u (set (get u) w);
  }.
Next Obligation. now rewrite !get_set. Defined.
Next Obligation. now rewrite !set_get. Defined.
Next Obligation. rewrite !get_set. rewrite !set_set. reflexivity. Defined.


Class World (T: Type) :=
  {
    w_state : Type;
    w_lens : Lens T w_state;
    w_acci : w_state -> w_state -> Prop;
    w_acce : w_state -> w_state -> Prop;
    w_acci_trans : PreOrder w_acci;
  }.

Existing Instance w_lens.
Existing Instance w_acci_trans.
Arguments w_state {_} _.
Arguments w_acci {_ _}.
Arguments w_acce {_ _}.

Infix "*->" := w_acci (at level 60, no associativity).
Infix "o->" := w_acce (at level 55, no associativity).

Section PROD.
  Context {A: Type} {B:Type} (WA: World A) (WB: World B).

  Program Instance world_prod: World (A * B) :=
    {
      w_state := @w_state A _ * @w_state B _;
      w_lens := lens_prod w_lens w_lens;
      w_acci := Relators.prod_rel (w_acci) (w_acci) ;
      w_acce := Relators.prod_rel w_acce w_acce;
    }.

  Lemma ext_step_prod (a1 a2: w_state WA) (b1 b2: w_state WB):
    (a1, b1) o-> (a2, b2) <-> a1 o-> a2 /\ b1 o-> b2.
  Proof.
    split.
    - intros H. inv H. cbn in *. split; eauto.
    - intros [X Y]. split; eauto.
  Qed.

  Lemma int_step_prod (a1 a2: w_state WA) (b1 b2: w_state WB):
    (a1, b1) *-> (a2, b2) <-> a1 *-> a2 /\ b1 *-> b2.
  Proof.
    split.
    - intros H. inv H. cbn in *. split; eauto.
    - intros [X Y]. split; eauto.
  Qed.

End PROD.
Arguments world_prod {_} {_} _ _.

Section SYMTBL.

  Context {T: Type} {W: World T}.

  Instance symtbl_world  : World (Genv.symtbl * T) :=
    {
      w_state := @w_state T _;
      w_lens := lens_comp lens_snd w_lens;
      w_acci := w_acci;
      w_acce := w_acce;
    }.

End SYMTBL.


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

  Program Definition cc_compose {li1 li2 li3}
          (cc12: callconv li1 li2) (cc23: callconv li2 li3) :=
    {|
      ccworld := Genv.symtbl * (ccworld cc12 * ccworld cc23);
      ccworld_world := @symtbl_world _ (world_prod (ccworld_world cc12) (ccworld_world cc23));
      match_senv '(se2, (w12, w23)) se1 se3 :=
        match_senv cc12 w12 se1 se2 /\ match_senv cc23 w23 se2 se3;
      match_query '(se2, (w12, w23)) q1 q3 :=
      exists q2, match_query cc12 w12 q1 q2 /\ match_query cc23 w23 q2 q3;
      match_reply '(se2, (w12, w23)) r1 r3 :=
      exists r2, match_reply cc12 w12 r1 r2 /\ match_reply cc23 w23 r2 r3;
    |}.
  Next Obligation.
    etransitivity; eapply match_senv_public_preserved ; eauto.
  Qed.
  Next Obligation.
    eapply match_senv_valid_for; eauto.
    eapply match_senv_valid_for; eauto.
  Qed.

  (* Declare Scope gc_cc_scope.
  Infix "@" := cc_compose (at level 30, right associativity) : gs_cc_scope. *)
  
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
        fsim_match_valid_query:
        forall q1 q2, match_query cc wb q1 q2 ->
                 valid_query L2 q2 = valid_query L1 q1;
        fsim_match_initial_states:
          forall q1 q2 s1, match_query cc wb q1 q2 -> initial_state L1 q1 s1 ->
          match_senv cc wb se1 se2 ->
          exists i, exists s2, initial_state L2 q2 s2 /\ match_states (get wb) i s1 s2;
        fsim_match_final_states:
          forall gw i s1 s2 r1, match_states gw i s1 s2 -> final_state L1 s1 r1 ->
          exists r2 gw', final_state L2 s2 r2 /\ (get wb) o-> gw' /\ gw *-> gw' /\
          match_reply cc (set wb gw') r1 r2;
        fsim_match_external:
          forall gw i s1 s2 q1, match_states gw i s1 s2 -> at_external L1 s1 q1 ->
          exists wa q2 , at_external L2 s2 q2 /\ gw *-> (get wa) /\
          match_query cc wa q1 q2 /\ match_senv cc wa se1 se2 /\
          forall r1 r2 s1' gw'', (get wa) o-> gw'' -> match_reply cc (set wa gw'') r1 r2 ->
          after_external L1 s1 r1 s1' ->
          exists i' s2', after_external L2 s2 r2 s2' /\
          match_states gw'' i' s1' s2';
          (* exists gw''' , gw'' *-> gw''' /\ match_states gw''' i' s1' s2'; (*The problem of va passes*) *)
        fsim_simulation:
          forall s1 t s1', Step L1 s1 t s1' ->
          forall gw i s2, match_states gw i s1 s2 ->
          exists i', exists s2', (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i)) /\
          match_states gw i' s1' s2';
      }.
    Arguments fsim_properties : clear implicits.

    Lemma fsim_simulation':
      forall L1 L2 index order match_states, fsim_properties L1 L2 index order match_states ->
      forall i s1 t s1', Step L1 s1 t s1' ->
      forall gw s2, match_states gw i s1 s2 ->
      exists i',
      ((exists s2', Plus L2 s2 t s2' /\ match_states gw i' s1' s2')
      \/ (order i' i /\ t = E0 /\ match_states gw i' s1' s2)).
    Proof.
      intros. exploit @fsim_simulation; eauto.
      intros (i' & s2' & A & B).
      exists i'. repeat split; eauto.
      destruct A.
      left; exists s2'; auto.
      destruct H2. inv H2.
      right; eauto.
      left; exists s2'; split; auto. econstructor; eauto.
    Qed.

    
    (** ** Forward simulation diagrams. *)

    (** Various simulation diagrams that imply forward simulation *)
    
    Section FORWARD_SIMU_DIAGRAMS.
      
      Variable L1: lts li1 li1 state1.
      Variable L2: lts li2 li2 state2.

      Variable match_states: gw_type -> state1 -> state2 -> Prop.

      Hypothesis match_valid_query:
        forall q1 q2, match_query cc wb q1 q2 ->
                 valid_query L2 q2 = valid_query L1 q1.

      Hypothesis match_initial_states:
        forall q1 q2 s1, match_query cc wb q1 q2 -> initial_state L1 q1 s1 ->
        exists s2, initial_state L2 q2 s2 /\ match_states (get wb) s1 s2.

      Hypothesis match_final_states:
        forall gw s1 s2 r1, match_states gw s1 s2 -> final_state L1 s1 r1 ->
        exists r2 gw', final_state L2 s2 r2 /\ (get wb) o-> gw' /\ gw *-> gw'  /\ match_reply cc (set wb gw') r1 r2.

      (* fsim_match_external:
          forall gw i s1 s2 q1, match_states gw i s1 s2 -> at_external L1 s1 q1 ->
          exists wa q2 , at_external L2 s2 q2 /\ gw *-> (get wa) /\
          match_query cc wa q1 q2 /\ match_senv cc wa se1 se2 /\
          forall r1 r2 s1' gw'', (get wa) o-> gw'' -> match_reply cc (set wa gw'') r1 r2 ->
          after_external L1 s1 r1 s1' ->
          exists i' s2', after_external L2 s2 r2 s2' /\
          match_states gw'' i' s1' s2';
          (* exists gw''' , gw'' *-> gw''' /\ match_states gw''' i' s1' s2'; (*The problem of va passes*) *)
        fsim_simulation:
          forall s1 t s1', Step L1 s1 t s1' ->
          forall gw i s2, match_states gw i s1 s2 ->
          exists i', exists s2', (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i)) /\
          match_states gw i' s1' s2';*)
      Hypothesis match_external:
        forall gw s1 s2 q1, match_states gw s1 s2 -> at_external L1 s1 q1 ->
            exists wA q2, at_external L2 s2 q2 /\ gw *-> (get wA) /\
                       match_query cc wA q1 q2 /\ match_senv cc wA se1 se2 /\
                       forall r1 r2 s1' gw'', (get wA) o-> gw'' -> match_reply cc (set wA gw'') r1 r2 ->
                                         after_external L1 s1 r1 s1' ->
                                         exists s2', after_external L2 s2 r2 s2' /\ match_states gw'' s1' s2'.

      Let ms gw idx s1 s2 := idx = s1 /\ match_states gw s1 s2.

(** Simulation when one transition in the first program
    corresponds to zero, one or several transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_STAR_WF.

(** [order] is a well-founded ordering associated with states
  of the first semantics.  Stuttering steps must correspond
  to states that decrease w.r.t. [order]. *)

Variable order: state1 -> state1 -> Prop.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2 gw, match_states gw s1 s2 ->
  exists s2',
  (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order s1' s1))
  /\ match_states gw s1' s2'.

Lemma forward_simulation_star_wf:
  fsim_properties L1 L2 state1 order ms.
Proof.
  subst ms;
  constructor.
- auto.
- intros. exploit match_initial_states; eauto. intros [s2 [A B]].
    exists s1; exists s2; auto.
- intros. destruct H. eapply match_final_states; eauto.
- intros. destruct H. edestruct match_external as (w & q2 & H2 & Hac & Hq & Hw & Hr); eauto.
  exists w, q2. intuition auto. edestruct Hr as (s2' & Hs2' & Hs'); eauto.
- intros. destruct H0. subst i. exploit simulation; eauto. intros [s2' [A B]].
  exists s1'; exists s2'; intuition auto.
Qed.

End SIMULATION_STAR_WF.

Section SIMULATION_STAR.

(** We now consider the case where we have a nonnegative integer measure
  associated with states of the first semantics.  It must decrease when we take
  a stuttering step. *)

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2 gw, match_states gw s1 s2 ->
  (exists s2', Plus L2 s2 t s2' /\ match_states gw s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states gw s1' s2)%nat.

Lemma forward_simulation_star:
  fsim_properties L1 L2 state1 (ltof _ measure) ms.
Proof.
  apply forward_simulation_star_wf.
  intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
  exists s2'; auto.
  exists s2; split. right; split. rewrite B. apply star_refl. auto. auto.
Qed.

End SIMULATION_STAR.

(** Simulation when one transition in the first program corresponds
    to one or several transitions in the second program. *)

Section SIMULATION_PLUS.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2 gw, match_states gw s1 s2 ->
  exists s2', Plus L2 s2 t s2' /\ match_states gw s1' s2'.

Lemma forward_simulation_plus:
  fsim_properties L1 L2 state1 (ltof _ (fun _ => O)) ms.
Proof.
  apply forward_simulation_star.
  intros. exploit simulation; eauto.
Qed.

End SIMULATION_PLUS.

(** Lock-step simulation: each transition in the first semantics
    corresponds to exactly one transition in the second semantics. *)

Section SIMULATION_STEP.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2 gw, match_states gw s1 s2 ->
  exists s2', Step L2 s2 t s2' /\ match_states gw s1' s2'.

Lemma forward_simulation_step:
  fsim_properties L1 L2 state1 (ltof _ (fun _ => O)) ms.
Proof.
  apply forward_simulation_plus.
  intros. exploit simulation; eauto. intros [s2' [A B]].
  exists s2'; split; auto. apply plus_one; auto.
Qed.

End SIMULATION_STEP.

(** Simulation when one transition in the first program
    corresponds to zero or one transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_OPT.

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2 gw, match_states gw s1 s2 ->
  (exists s2', Step L2 s2 t s2' /\ match_states gw s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states gw s1' s2)%nat.

Lemma forward_simulation_opt:
  fsim_properties L1 L2 state1 (ltof _ measure) ms.
Proof.
  apply forward_simulation_star.
  intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
  left; exists s2'; split; auto. apply plus_one; auto.
  right; auto.
Qed.

End SIMULATION_OPT.

End FORWARD_SIMU_DIAGRAMS.

    (** ** Forward simulation with the "eventually" modality *)

(** A forward simulation diagram where the first semantics can take some extra steps
    before reaching a state that restores the simulation relation. *)

Section FORWARD_SIMU_EVENTUALLY.

Variable L1: lts li1 li1 state1.
Variable L2: lts li2 li2 state2.
Variable index: Type.
Variable order: index -> index -> Prop.
Variable match_states: gw_type -> index -> state1 -> state2 -> Prop.

Hypothesis order_wf: well_founded order.

Hypothesis match_valid_query:
  forall q1 q2, match_query cc wb q1 q2 ->
  valid_query L2 q2 = valid_query L1 q1.

Hypothesis initial_states:
  forall q1 q2 s1, match_query cc wb q1 q2 -> initial_state L1 q1 s1 ->
              exists i, exists s2, initial_state L2 q2 s2 /\ match_states (get wb) i s1 s2.

Hypothesis final_states:
  forall wp i s1 s2 r1,
    match_states wp i s1 s2 -> final_state L1 s1 r1 ->
    exists r2 wp', final_state L2 s2 r2 /\ (get wb) o-> wp' /\ wp *-> wp' /\ match_reply cc (set wb wp')  r1 r2.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall wp i s2, match_states wp i s1 s2 ->
  exists n i' s2',
     (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
     /\ Eventually L1 n s1' (fun s1'' => match_states wp i' s1'' s2').

Hypothesis match_external:
  forall gw i s1 s2 q1, match_states gw i s1 s2 -> at_external L1 s1 q1 ->
  exists wA q2, at_external L2 s2 q2 /\ gw *-> (get wA) /\ match_query cc wA q1 q2 /\ match_senv cc wA se1 se2 /\
  forall r1 r2 s1' gw'', (get wA) o-> gw'' -> match_reply cc (set wA gw'') r1 r2 -> after_external L1 s1 r1 s1' ->
               exists i' s2', after_external L2 s2 r2 s2' /\ match_states gw'' i' s1' s2'.

(*Hypothesis public_preserved:
  forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id. *)

Let ms := fun gw i s1 s2 => Eventually L1 (snd i) s1 (fun s1'' => match_states gw (fst i) s1'' s2).
Let index' :=  (index * nat)%type.
Let order' := lex_ord order Nat.lt. 
Lemma forward_simulation_eventually: fsim_properties L1 L2 index' order' ms.
Proof.
  constructor.
- auto.
- intros. exploit initial_states; eauto. intros (i & s2 & A & B).
  exists (i, O), s2; split; auto using eventually_now.
  constructor. simpl. eauto.
- intros gw [i n] s1 s2 r EV FS; simpl in *. inv EV.
  + eapply final_states; eauto.
  + eelim H; eauto.
- intros gw [i n] s1 s2 q1 EV AT. simpl in *. inv EV.
  + exploit match_external; eauto. intros (wA & q2 & AT' & ACI &  MQ & MS & AFTER).
    exists wA, q2. intuition eauto. exploit AFTER; eauto.
    intros (i' & s2' & A & B).
    exists (i', O), s2'. split. eauto. constructor. simpl. eauto.
  + eelim H0; eauto.
- intros s1 t s1' ST gw [i n] s2 EV; simpl in *. inv EV.
  + exploit simulation; eauto. intros (n' & i' & s2' & A & B).
    exists (i', n'), s2'; split; auto.
    destruct A as [P | [P Q]]; auto using lex_ord_left.
    right. split. eauto. constructor. eauto.
  + apply H1 in ST. destruct ST as (A & B). subst t.
    exists (i, n0), s2; split.
    right; split. apply star_refl. 
    apply lex_ord_right. simpl in H2. lia.
    exact B.
Qed.
    
End FORWARD_SIMU_EVENTUALLY.

(** Two simplified diagrams. *)

Section FORWARD_SIMU_EVENTUALLY_SIMPL.

Variable L1: lts li1 li1 state1.
Variable L2: lts li2 li2 state2.
Variable match_states: gw_type -> state1 -> state2 -> Prop.

(*Hypothesis public_preserved:
  forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id. *)
Hypothesis match_valid_query:
  forall q1 q2, match_query cc wb q1 q2 ->
           valid_query L2 q2 = valid_query L1 q1.
Hypothesis initial_states:
  forall q1 q2 s1, match_query cc wb q1 q2 -> initial_state L1 q1 s1  ->
  exists s2, initial_state L2 q2 s2 /\ match_states (get wb) s1 s2.
Hypothesis final_states:
  forall gw s1 s2 r1,
    match_states gw s1 s2 -> final_state L1 s1 r1 ->
    exists r2 gw', final_state L2 s2 r2 /\ (get wb) o-> gw' /\ gw *-> gw' /\ match_reply cc (set wb gw') r1 r2.
Hypothesis match_external:
  forall gw s1 s2 q1, match_states gw s1 s2 -> at_external L1 s1 q1 ->
  exists wA q2, at_external L2 s2 q2 /\ gw *-> (get wA) /\ match_query cc wA q1 q2 /\ match_senv cc wA se1 se2 /\
  forall r1 r2 s1' gw'', (get wA) o-> gw'' -> match_reply cc (set wA gw'') r1 r2 -> after_external L1 s1 r1 s1' ->
  exists s2', after_external L2 s2 r2 s2' /\ match_states gw'' s1' s2'.

(** Simplified "plus" simulation diagram, when L2 always makes at least one transition. *)

Section FORWARD_SIMU_EVENTUALLY_PLUS.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall gw s2, match_states gw s1 s2 ->
  exists n s2',
     Plus L2 s2 t s2'
  /\ Eventually L1 n s1' (fun s1'' => match_states gw s1'' s2').

Let ms' := fun gw (i:nat) s1 s2 => match_states gw s1 s2.
Let ms := fun gw i s1 s2 => Eventually L1 (snd i) s1 (fun s1'' => ms' gw (fst i) s1'' s2).
Let index' :=  (nat * nat)%type.
Let order' := lex_ord lt Nat.lt. 

Lemma forward_simulation_eventually_plus: fsim_properties L1 L2 index' order' ms.
Proof.
  apply forward_simulation_eventually.
- auto.
- intros. exploit initial_states. eauto. eauto.
  intros (s2 & A & B). exists O, s2; auto.
- intros. eapply final_states; eauto.
- intros. exploit simulation; eauto. intros (n & s2' & A & B).
  exists n, O, s2'; eauto.  
- intros. exploit match_external; eauto.
  intros (wA & q2 & A & B & C & D & E). exists wA, q2. repeat apply conj.
  eauto. eauto. eauto. eauto. intros. exploit E. eauto. eauto. eauto.
  intros (s2' & A' & B'). exists O, s2'; auto.
Qed.

End FORWARD_SIMU_EVENTUALLY_PLUS.

(** Simplified "star" simulation diagram, with a decreasing, well-founded order on L1 states. *)

Section FORWARD_SIMU_EVENTUALLY_STAR_WF.

Variable order: state1 -> state1 -> Prop.
(* Hypothesis order_wf: well_founded order. *)

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall gw s2, match_states gw s1 s2 ->
     (exists s2',
        (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order s1' s1)) /\ match_states gw s1' s2')
  \/ (exists n s2',
        Plus L2 s2 t s2' /\ Eventually L1 n s1' (fun s1'' => match_states gw s1'' s2')).

Let index' := (nat * state1)%type.
Let order' := lex_ord Nat.lt order.
Let ms := fun gw i s1 s2 => snd i = s1 /\ Eventually L1 (fst i) s1 (fun s1'' => match_states gw s1'' s2).
Lemma forward_simulation_eventually_star_wf: fsim_properties L1 L2 index' order' ms.
Proof.
  constructor; intros.
- auto.
- exploit initial_states; eauto. intros (s2 & A & B).
  exists (O, s1), s2. split. auto. constructor. auto. auto using eventually_now.
- destruct i as [n s11]; destruct H as [P Q]; simpl in *; subst s11.
  inv Q.
  + eapply final_states; eauto.
  + eelim H; eauto.
- destruct i as [n s11]; destruct H as [P Q]; simpl in *; subst s11.
  inv Q.
  + exploit match_external; eauto. intros (wA & q2 & A & B & C & D & E).
    exists wA, q2. intuition eauto. exploit E; eauto.
    intros (s2' & A' & B'). exists (O, s1'). exists s2'. split. eauto.
    unfold ms. split. eauto. constructor. eauto.
  + eelim H1; eauto.
- destruct i as [n s11]; destruct H0 as [P Q]; simpl in *; subst s11.
  inv Q.
  + exploit simulation; eauto. intros [(s2' & A & B) | (n & s2' & A & B)].
    * exists (O, s1'), s2'; split. 
      destruct A as [A | [A1 A2]]. eauto. right. split; auto using lex_ord_right.
      eapply lex_ord_right. eauto. constructor; eauto using eventually_now.
    * exists (n, s1'), s2'; unfold ms; auto.
  + apply H2 in H. destruct H. subst t.
    exists (n0, s1'), s2; split.
    right; split. apply star_refl. apply lex_ord_left; lia.
    unfold ms. auto.
Qed.

End FORWARD_SIMU_EVENTUALLY_STAR_WF.

(** Simplified "star" simulation diagram, with a decreasing measure on L1 states. *)

Section FORWARD_SIMU_EVENTUALLY_STAR.

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall wp s2, match_states wp s1 s2 ->
     (exists s2',
        (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ measure s1' < measure s1))%nat
        /\ match_states wp s1' s2')
  \/ (exists n s2',
        Plus L2 s2 t s2' /\ Eventually L1 n s1' (fun s1'' => match_states wp s1'' s2')).

Let order := (ltof _ measure).
Let index' := (nat * state1)%type.
Let order' := lex_ord Nat.lt order.
Let ms := fun wp i s1 s2 => snd i = s1 /\ Eventually L1 (fst i) s1 (fun s1'' => match_states wp s1'' s2).
Lemma forward_simulation_eventually_star: fsim_properties L1 L2 index' order' ms.
Proof.
  apply forward_simulation_eventually_star_wf.
- exact simulation.
Qed.

End FORWARD_SIMU_EVENTUALLY_STAR.

End FORWARD_SIMU_EVENTUALLY_SIMPL.


Section SIMULATION_SEQUENCES.
  
  Context L1 L2 index order match_states
    (S: fsim_properties L1 L2 index order match_states).
  
  Lemma simulation_star:
    forall s1 t s1', Star L1 s1 t s1' ->
        forall gw i s2, match_states gw i s1 s2 ->
        exists i', exists s2', Star L2 s2 t s2' /\
        match_states gw i' s1' s2'.
  Proof.
    induction 1; intros.
    eexists i; exists s2; repeat split; auto. apply star_refl.
    exploit fsim_simulation; eauto.
    intros (i' & s2' & A & B).
    exploit IHstar; eauto.
    intros (i'' & s2'' & Hx& C).
    exists i''; exists s2''; repeat split; auto.
    eapply star_trans; eauto.
    intuition auto. apply plus_star; auto.
  Qed.

  Lemma simulation_plus:
    forall s1 t s1', Plus L1 s1 t s1' ->
                forall gw i s2, match_states gw i s1 s2 ->
        exists i',
          ((exists s2', Plus L2 s2 t s2' /\ match_states gw i' s1' s2') \/
             clos_trans _ order i' i /\ t = E0 /\ match_states gw i' s1' s2).
  Proof.
    induction 1 using plus_ind2; intros.
    (* base case *)
    - exploit fsim_simulation'; eauto.
      intros (i' & A).
      exists i'. repeat split; eauto.
      destruct A.
      left; auto.
      right; intuition.
    (* inductive case *)
    - exploit fsim_simulation'; eauto.
      intros (i' & A).
      destruct A as [[s2' [A B]] | [A [B C]]].
      + exploit simulation_star. apply plus_star; eauto. eauto.
        intros (i'' & s2'' & P & Q).
        exists i''. repeat split.
        left; exists s2''; split; auto. eapply plus_star_trans; eauto.
      + exploit IHplus; eauto.
        intros (i'' & P).
        destruct P as [[s2'' [P Q]] | [P [Q R]]].
        * subst.
          exists i''. repeat split.
          left; exists s2''; auto.
        * subst.
          exists i''. repeat split.
          right; intuition auto.
          eapply t_trans; eauto. eapply t_step; eauto.
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

  
(** * Backward simulations between two transition semantics. *)

Section BSIM.

Context {li1 li2} (cc: callconv li1 li2).
Context (se1 se2: Genv.symtbl) (wb: ccworld cc).
Context {state1 state2: Type}.

Let gw_type := gworld cc.

(** The general form of a backward simulation. *)

Record bsim_properties (L1 : lts li1 li1 state1) (L2: lts li2 li2 state2) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: gw_type -> index -> state1 -> state2 -> Prop) : Prop := {
    bsim_match_valid_query:
      forall q1 q2, match_query cc wb q1 q2 ->
      valid_query L2 q2 = valid_query L1 q1;
    bsim_match_initial_states:
      forall q1 q2, match_query cc wb q1 q2 ->
      bsim_match_cont (rex (match_states (get wb))) (initial_state L1 q1) (initial_state L2 q2);
    bsim_match_final_states:
      forall gw i s1 s2 r2,
      match_states gw i s1 s2 -> safe L1 s1 -> final_state L2 s2 r2 ->
      exists s1' r1 gw', Star L1 s1 E0 s1' /\ final_state L1 s1' r1 /\ (get wb) o-> gw' /\ gw *-> gw' /\
                      match_reply cc (set wb gw') r1 r2;
    bsim_match_external:
      forall gw i s1 s2 q2, match_states gw i s1 s2 -> safe L1 s1 -> at_external L2 s2 q2 ->
      exists wA s1' q1, Star L1 s1 E0 s1' /\ at_external L1 s1' q1 /\ gw *-> (get wA) /\
      match_query cc wA q1 q2 /\ match_senv cc wA se1 se2 /\
      forall r1 r2 gw'', (get wA o-> gw'') -> match_reply cc (set wA gw'') r1 r2 ->
      bsim_match_cont (rex (match_states gw'')) (after_external L1 s1' r1) (after_external L2 s2 r2); 
    bsim_progress:
      forall gw i s1 s2,
      match_states gw i s1 s2 -> safe L1 s1 ->
      (exists r, final_state L2 s2 r) \/
      (exists q, at_external L2 s2 q) \/
      (exists t, exists s2', Step L2 s2 t s2');
    bsim_simulation:
      forall s2 t s2', Step L2 s2 t s2' ->
      forall gw i s1, match_states gw i s1 s2 -> safe L1 s1 ->
      exists i', exists s1',
         (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
      /\ match_states gw i' s1' s2';
  }.

Arguments bsim_properties: clear implicits.

(** An alternate form of the simulation diagram *)

Lemma bsim_simulation':
  forall L1 L2 index order match_states, bsim_properties L1 L2 index order match_states ->
  forall i s2 t s2', Step L2 s2 t s2' ->
  forall gw s1, match_states gw i s1 s2 -> safe L1 s1 ->
  (exists i', exists s1', Plus L1 s1 t s1' /\ match_states gw i' s1' s2')
  \/ (exists i', order i' i /\ t = E0 /\ match_states gw i' s1 s2').
Proof.
  intros. exploit bsim_simulation; eauto.
  intros [i' [s1' [A B]]]. intuition.
  left; exists i'; exists s1'; auto.
  inv H4.
  right; exists i'; auto.
  left; exists i'; exists s1'; split; auto. econstructor; eauto.
Qed.
End BSIM.

Arguments bsim_properties {_ _} _ _ _ _  {_ _} L1 L2 index order match_states. 


Record bsim_components {li1 li2} (cc: callconv li1 li2) L1 L2 :=
  Backward_simulation {
    bsim_index: Type;
    bsim_order: bsim_index -> bsim_index -> Prop;
    bsim_match_states: _;

    bsim_skel:
      skel L1 = skel L2;
    bsim_lts:
      forall se1 se2 w,
        GS.match_senv cc w se1 se2 ->
        Genv.valid_for (skel L1) se1 ->
        bsim_properties cc se1 se2 w (activate L1 se1) (activate L2 se2)
                        bsim_index bsim_order (bsim_match_states se1 se2 w);
    bsim_order_wf:
      well_founded bsim_order;
    }.

Arguments Backward_simulation {_ _ cc L1 L2 bsim_index}.

Definition backward_simulation {li1 li2} cc L1 L2 :=
  inhabited (@bsim_components li1 li2 cc L1 L2).


Section FORWARD_TO_BACKWARD.

Context {li1 li2} (cc: callconv li1 li2).
Context (se1 se2: Genv.symtbl) (wB: ccworld cc).
Context {state1 state2} (L1: lts li1 li1 state1) (L2: lts li2 li2 state2).
Context {index order match_states} (FS: fsim_properties cc se1 se2 wB L1 L2 index order match_states).
Hypothesis order_wf: well_founded order.
Hypothesis Hse: match_senv cc wB se1 se2.
Hypothesis L1_receptive: lts_receptive L1 se1.
Hypothesis L2_determinate: lts_determinate L2 se2.

(** Exploiting forward simulation *)

Inductive f2b_transitions: gworld cc -> state1 -> state2 -> Prop :=
  | f2b_trans_final: forall s1 s2 s1' r1 r2 gw i (gw': gworld cc),
      Star L1 s1 E0 s1' ->
      match_states gw i s1' s2 ->
      (get wB) o-> gw' -> gw *-> gw' ->
      match_reply cc (set wB gw') r1 r2 ->
      final_state L1 s1' r1 ->
      final_state L2 s2 r2 ->
      f2b_transitions gw s1 s2
  | f2b_trans_ext: forall s1 s2 s1' gw i wA q1 q2,
      Star L1 s1 E0 s1' ->
      match_states gw i s1' s2 ->
      gw *-> get wA ->
      match_query cc wA q1 q2 ->
      match_senv cc wA se1 se2 ->
      at_external L1 s1' q1 ->
      at_external L2 s2 q2 ->
      (forall r1 r2 s1'' gw'',
          get wA o-> gw'' ->
          match_reply cc (set wA gw'') r1 r2 ->
          after_external L1 s1' r1 s1'' ->
          exists j s2',
            after_external L2 s2 r2 s2' /\
            match_states gw'' j s1'' s2') ->
      f2b_transitions gw s1 s2
  | f2b_trans_step: forall s1 s2 s1' t s1'' s2' i' i'' gw,
      Star L1 s1 E0 s1' ->
      Step L1 s1' t s1'' ->
      Plus L2 s2 t s2' ->
      match_states gw i' s1' s2 ->
      match_states gw i'' s1'' s2' ->
      f2b_transitions gw s1 s2.

Lemma f2b_progress:
  forall i gw s1 s2, match_states gw i s1 s2 -> safe L1 s1 -> f2b_transitions gw s1 s2.
Proof.
  intros i0; pattern i0. apply well_founded_ind with (R := order); auto.
  intros i REC gw s1 s2 MATCH SAFE.
  destruct (SAFE s1) as [[r FINAL] | [[q EXTERN] | [t [s1' STEP1]]]]. apply star_refl.
- (* final state reached *)
  edestruct @fsim_match_final_states as (r2 & gw' & Hr & ACO & ACI & Hfinal); eauto.
  eapply f2b_trans_final; eauto.
  apply star_refl. 
- (* external call reached *)
  edestruct @fsim_match_external as (w & q2 & Hat & ACI & Hq & Hse' & Hafter); eauto.
  eapply f2b_trans_ext; eauto.
  apply star_refl.
- (* L1 can make one step *)
  exploit (fsim_simulation FS); eauto. intros [i' [s2' [A MATCH']]].
  assert (B: Plus L2 s2 t s2' \/ (s2' = s2 /\ t = E0 /\ order i' i)).
    intuition auto.
    destruct (star_inv H0); intuition auto.
  clear A. destruct B as [PLUS2 | [EQ1 [EQ2 ORDER]]].
+ eapply f2b_trans_step; eauto. apply star_refl.
+ subst. exploit REC; eauto. eapply star_safe; eauto. apply star_one; auto.
  intros TRANS; inv TRANS.
* eapply f2b_trans_final; eauto. eapply star_left; eauto.
* eapply f2b_trans_ext; eauto. eapply star_left; eauto.
* eapply f2b_trans_step; eauto. eapply star_left; eauto.
Qed.

Lemma fsim_simulation_not_E0:
  forall s1 t s1', Step L1 s1 t s1' -> t <> E0 ->
  forall gw i s2, match_states gw i s1 s2 ->
  exists i', exists s2', Plus L2 s2 t s2' /\ match_states gw i' s1' s2'.
Proof.
  intros. exploit (fsim_simulation FS); eauto. intros [i' [s2' [A B]]].
  exists i'; exists s2'; split; auto.
  destruct A. auto. destruct H2. exploit star_inv; eauto. intros [[EQ1 EQ2] | P]; auto.
  congruence.
Qed.

(** Exploiting determinacy *)

Remark silent_or_not_silent:
  forall t, t = E0 \/ t <> E0.
Proof.
  intros; unfold E0; destruct t; auto; right; congruence.
Qed.

Remark not_silent_length:
  forall t1 t2, (length (t1 ** t2) <= 1)%nat -> t1 = E0 \/ t2 = E0.
Proof.
  unfold Eapp, E0; intros. rewrite app_length in H.
  destruct t1; destruct t2; auto. simpl in H. extlia.
Qed.

Lemma f2b_determinacy_inv:
  forall s2 t' s2' t'' s2'',
  Step L2 s2 t' s2' -> Step L2 s2 t'' s2'' ->
  (t' = E0 /\ t'' = E0 /\ s2' = s2'')
  \/ (t' <> E0 /\ t'' <> E0 /\ match_traces se1 t' t'').
Proof.
  intros.
  assert (match_traces se2 t' t'').
    eapply sd_determ_1; eauto.
  destruct (silent_or_not_silent t').
  subst. inv H1.
  left; intuition. eapply sd_determ_2; eauto.
  destruct (silent_or_not_silent t'').
  subst. inv H1. elim H2; auto.
  right; intuition.
  eapply match_traces_preserved with (ge1 := se2); auto.
  intro. symmetry. eapply match_senv_public_preserved; eauto.
Qed.

Lemma f2b_determinacy_star:
  forall s s1, Star L2 s E0 s1 ->
  forall t s2 s3,
  Step L2 s1 t s2 -> t <> E0 ->
  Star L2 s t s3 ->
  Star L2 s1 t s3.
Proof.
  intros s0 s01 ST0. pattern s0, s01. eapply star_E0_ind; eauto.
  intros. inv H3. congruence.
  exploit f2b_determinacy_inv. eexact H. eexact H4.
  intros [[EQ1 [EQ2 EQ3]] | [NEQ1 [NEQ2 MT]]].
  subst. simpl in *. eauto.
  congruence.
Qed.

(** Orders *)

Inductive f2b_index : Type :=
  | F2BI_before (n: nat)
  | F2BI_after (n: nat).

Inductive f2b_order: f2b_index -> f2b_index -> Prop :=
  | f2b_order_before: forall n n',
      (n' < n)%nat ->
      f2b_order (F2BI_before n') (F2BI_before n)
  | f2b_order_after: forall n n',
      (n' < n)%nat ->
      f2b_order (F2BI_after n') (F2BI_after n)
  | f2b_order_switch: forall n n',
      f2b_order (F2BI_before n') (F2BI_after n).

Lemma wf_f2b_order:
  well_founded f2b_order.
Proof.
  assert (ACC1: forall n, Acc f2b_order (F2BI_before n)).
    intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto.
  assert (ACC2: forall n, Acc f2b_order (F2BI_after n)).
    intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto. auto.
  red; intros. destruct a; auto.
Qed.

(** Constructing the backward simulation *)

Inductive f2b_match_states: gworld cc -> f2b_index -> state1 -> state2 -> Prop :=
  | f2b_match_at: forall gw i s1 s2,
      match_states gw i s1 s2 ->
      f2b_match_states gw (F2BI_after O) s1 s2
  | f2b_match_before: forall gw s1 t s1' s2b s2 n s2a i,
      Step L1 s1 t s1' ->  t <> E0 ->
      Star L2 s2b E0 s2 ->
      starN (step L2) (globalenv L2) n s2 t s2a ->
      match_states gw i s1 s2b ->
      f2b_match_states gw (F2BI_before n) s1 s2
  | f2b_match_after: forall gw n s2 s2a s1 i,
      starN (step L2) (globalenv L2) (S n) s2 E0 s2a ->
      match_states gw i s1 s2a ->
      f2b_match_states gw (F2BI_after (S n)) s1 s2.

Remark f2b_match_after':
  forall n s2 s2a s1 gw i,
  starN (step L2) (globalenv L2) n s2 E0 s2a ->
  match_states gw i s1 s2a ->
  f2b_match_states gw (F2BI_after n) s1 s2.
Proof.
  intros. inv H.
  econstructor; eauto.
  econstructor; eauto. econstructor; eauto.
Qed.

(** Backward simulation of L2 steps *)

Lemma f2b_simulation_step:
  forall s2 t s2', Step L2 s2 t s2' ->
  forall gw i s1, f2b_match_states gw i s1 s2 -> safe L1 s1 ->
  exists i', exists s1',
    (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ f2b_order i' i))
     /\ f2b_match_states gw i' s1' s2'.
Proof.
  intros s2 t s2' STEP2 gw i s1 MATCH SAFE.
  inv MATCH.
- (* 1. At matching states *)
  exploit f2b_progress; eauto. intros TRANS. inv TRANS.
+ (* 1.1  L1 can reach final state and L2 is at final state: impossible! *)
  exploit (sd_final_nostep L2_determinate); eauto. contradiction.
+ (* 1.1b  Same, with external states *)
  exploit (sd_at_external_nostep L2_determinate); eauto. contradiction.
+ (* 1.2  L1 can make 0 or several steps; L2 can make 1 or several matching steps. *)
  inv H2.
  exploit f2b_determinacy_inv. eexact H5. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
* (* 1.2.1  L2 makes a silent transition *)
  destruct (silent_or_not_silent t2).
  (* 1.2.1.1  L1 makes a silent transition too: perform transition now and go to "after" state *)
  subst. simpl in *. destruct (star_starN H6) as [n STEPS2].
  exists (F2BI_after n); exists s1''; split.
  left. eapply plus_right; eauto.
  eapply f2b_match_after'; eauto.
  (* 1.2.1.2 L1 makes a non-silent transition: keep it for later and go to "before" state *)
  subst. simpl in *. destruct (star_starN H6) as [n STEPS2].
  exists (F2BI_before n); exists s1'; split.
  right; split. auto. constructor.
  econstructor. eauto. auto. apply star_one; eauto. eauto. eauto.
* (* 1.2.2 L2 makes a non-silent transition, and so does L1 *)
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  congruence.
  subst t2. rewrite E0_right in H1.
  (* Use receptiveness to equate the traces *)
  exploit (sr_receptive L1_receptive); eauto. intros [s1''' STEP1].
  exploit fsim_simulation_not_E0. eexact STEP1. auto. eauto.
  intros [i''' [s2''' [P Q]]]. inv P.
  (* Exploit determinacy *)
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  subst t0. simpl in *. exploit @sd_determ_1. eauto. eexact STEP2. eexact H2.
  intros. elim NOT2. inv H8. auto.
  subst t2. rewrite E0_right in *.
  assert (s4 = s2'). eapply sd_determ_2; eauto. subst s4.
  (* Perform transition now and go to "after" state *)
  destruct (star_starN H7) as [n STEPS2]. exists (F2BI_after n); exists s1'''; split.
  left. eapply plus_right; eauto.
  eapply f2b_match_after'; eauto.

- (* 2. Before *)
  inv H2. congruence.
  exploit f2b_determinacy_inv. eexact H4. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
+ (* 2.1 L2 makes a silent transition: remain in "before" state *)
  subst. simpl in *. exists (F2BI_before n0); exists s1; split.
  right; split. apply star_refl. constructor. lia.
  econstructor; eauto. eapply star_right; eauto.
+ (* 2.2 L2 make a non-silent transition *)
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  congruence.
  subst. rewrite E0_right in *.
  (* Use receptiveness to equate the traces *)
  exploit (sr_receptive L1_receptive); eauto. intros [s1''' STEP1].
  exploit fsim_simulation_not_E0. eexact STEP1. auto. eauto.
  intros [i''' [s2''' [P Q]]].
  (* Exploit determinacy *)
  exploit f2b_determinacy_star. eauto. eexact STEP2. auto. apply plus_star; eauto.
  intro R. inv R. congruence.
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  subst. simpl in *. exploit @sd_determ_1. eauto. eexact STEP2. eexact H2.
  intros. elim NOT2. inv H7; auto.
  subst. rewrite E0_right in *.
  assert (s3 = s2'). eapply sd_determ_2; eauto. subst s3.
  (* Perform transition now and go to "after" state *)
  destruct (star_starN H6) as [n STEPS2]. exists (F2BI_after n); exists s1'''; split.
  left. apply plus_one; auto.
  eapply f2b_match_after'; eauto.

- (* 3. After *)
  inv H. exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit f2b_determinacy_inv. eexact H2. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  subst. exists (F2BI_after n); exists s1; split.
  right; split. apply star_refl. constructor; lia.
  eapply f2b_match_after'; eauto.
  congruence.
Qed.

End FORWARD_TO_BACKWARD.

(** The backward simulation *)

Lemma forward_to_backward_simulation:
  forall {li1 li2} (cc: callconv li1 li2),
  forall L1 L2,
  forward_simulation cc L1 L2 -> receptive L1 -> determinate L2 ->
  backward_simulation cc L1 L2.
Proof.
  intros until L2. intros FS L1_receptive L2_determinate.
  destruct FS as [[index order match_states Hskel FS order_wf]].
  set (ms se1 se2 w := f2b_match_states cc (L1 se1) (L2 se2) (match_states := match_states se1 se2 w)).
  constructor.
  eapply Backward_simulation with f2b_order ms; auto using wf_f2b_order.
  intros se1 se2 wB Hse Hse1.
  specialize (FS se1 se2 wB Hse Hse1).
  specialize (L1_receptive se1). specialize (L2_determinate se2).
  split.
- (* valid queries *)
  eapply fsim_match_valid_query; eauto.
- split.
  (* initial states exist *)
  intros. exploit (fsim_match_initial_states FS); eauto. intros [i [s2 [A B]]].
  exists s2; auto.
  (* initial states *)
  intros. exploit (fsim_match_initial_states FS); eauto. intros [i [s2' [A B]]].
  assert (s2 = s2') by (eapply sd_initial_determ; eauto). subst s2'.
  exists s1; split; auto. exists (F2BI_after O). econstructor; eauto.
- (* final states *)
  intros. inv H.
  exploit @f2b_progress; eauto. intros TRANS; inv TRANS.
  assert (r0 = r2) by eauto using sd_final_determ; subst.
  exists s1',r1,gw'. eauto.
  eelim sd_final_noext; eauto.
  inv H4. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
  inv H5. congruence. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
  inv H2. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
- (* external states *)
  intros. inv H.
  + exploit @f2b_progress; eauto.
    intros TRANS; inv TRANS.
    * eelim (sd_final_noext L2_determinate); eauto.
    * assert (q0 = q2) by eauto using sd_at_external_determ; subst.
      exists wA, s1', q1. intuition auto. split.
      intros. edestruct H9 as (j & s2' & Hs2' & Hs'); eauto.
      intros. edestruct H9 as (j & s2' & Hs2' & Hs'); eauto.
      assert (s3 = s2') by eauto using sd_after_external_determ; subst.
      exists s0. intuition auto.
      exists (F2BI_after O). econstructor; eauto.
    * inv H4. eelim (sd_at_external_nostep L2_determinate); eauto.
  + inv H5. congruence. eelim (sd_at_external_nostep L2_determinate); eauto.
  + inv H2. eelim (sd_at_external_nostep L2_determinate); eauto.
- (* progress *)
  intros. inv H.
  exploit @f2b_progress; eauto. intros TRANS; inv TRANS; eauto.
  inv H3. eauto.
  inv H4. congruence. eauto.
  inv H1. eauto.
- (* simulation *)
  eapply f2b_simulation_step; eauto.
Qed.

End GS.

(** Transform the old callconv into new callconv with [world_unit], therefore new fsim is essentially the same as old one *)

Import GS.

Local Instance world_unit {T: Type} : World T :=
  {
    w_state := unit;
    w_lens := lens_unit;
    w_acci := fun _ _ => True;
    w_acce := fun _ _ => True;
  }.

Program Definition cc_unit_world {li1 li2} (cc: LanguageInterface.callconv li1 li2) : callconv li1 li2 :=
    {|
      ccworld := LanguageInterface.ccworld cc;
      ccworld_world := world_unit;
      match_senv w := LanguageInterface.match_senv cc w;
      match_query w := LanguageInterface.match_query cc w;
      match_reply w := LanguageInterface.match_reply cc w;
    |}.
Next Obligation.
  eapply LanguageInterface.match_senv_public_preserved; eauto.
Qed.
Next Obligation.
  eapply LanguageInterface.match_senv_valid_for; eauto.
Qed.

Coercion cc_unit_world : LanguageInterface.callconv >-> callconv.

