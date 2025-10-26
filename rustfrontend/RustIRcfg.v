Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST Errors.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes Rusttypes.
Require Import Cop RustOp.
Require Import LanguageInterface.
Require Import Clight Rustlight Rustlightown.
Require Import InitDomain RustIR.
Require Import Permutation.

Import ListNotations.

(** ** Definition of selector. It is the program pointer in AST-like 
program.  *)

Inductive select_kind : Type :=
| Selseqleft: select_kind
| Selseqright: select_kind
(* Then and else are guarded by the conditional expression to ensure
that this experssion is unchanged during the translation *)
| Selifthen : select_kind
| Selifelse : select_kind
| Selloop: select_kind.

Definition selector := list select_kind.

Inductive selector_disjoint : selector -> selector -> Prop :=
| sel_disjoint_neq: forall s1 s2 l1 l2,
    s1 <> s2 ->
    selector_disjoint (s1::l1) (s2::l2)
| sel_disjoint_cons: forall s l1 l2,
    selector_disjoint l1 l2 ->
    selector_disjoint (s::l1) (s::l2).

(* list_sel_norepet: selector version of list_norepet except that we
strength the neq to selector_disjoint *)
Inductive list_sel_norepet : list selector -> Prop :=
  | list_sel_norepet_nil:
      list_sel_norepet nil
  | list_sel_norepet_cons: forall hd tl
      (DIS: forall sel, In sel tl -> selector_disjoint hd sel)
      (NOREP: list_sel_norepet tl),
      list_sel_norepet (hd :: tl).

(* list_sel_disjoint: selector version of list_disjoint except that we
strength the neq to selector_disjoint *)
Definition list_sel_disjoint (l1 l2: list selector) : Prop :=
  forall (x y: selector), In x l1 -> In y l2 -> selector_disjoint x y.

Lemma list_sel_norepet_app:
  forall (l1 l2: list selector),
  list_sel_norepet (l1 ++ l2) <->
  list_sel_norepet l1 /\ list_sel_norepet l2 /\ list_sel_disjoint l1 l2.
Proof.
  induction l1; simpl; intros; split; intros.
  - intuition. constructor. red;simpl;auto.
    tauto.
  - intuition.
  - inv H. rewrite IHl1 in NOREP.
    destruct NOREP as (A1 & A2 & A3).
    repeat apply conj; auto.
    + constructor. intros. eapply DIS. eapply in_app. auto.
      auto.
    + red. intros. inv H.
      * eapply DIS. eapply in_app. auto.
      * eapply A3; auto.
  - destruct H as (A1 & A2 & A3). inv A1.
    econstructor.
    + intros. eapply in_app in H. destruct H.
      * eauto.
      * eapply A3. constructor. auto. auto.
    + eapply IHl1. repeat apply conj; auto.
      red. intros. eapply A3. eapply in_cons. auto. auto.
Qed.

(* Definition select_stmt_aux (sel: select_kind) (stmt: option statement)  *)
(* : option statement := *)
(*   match sel, stmt with *)
(*   | Selseqleft, Some (Ssequence s1 s2) => Some s1 *)
(*   | Selseqright, Some (Ssequence s1 s2) => Some s2 *)
(*   | Selifthen, Some (Sifthenelse _ s1 s2) => Some s1 *)
(*   | Selifelse, Some (Sifthenelse _ s1 s2) => Some s2 *)
(*   | Selloop, Some (Sloop s) => Some s *)
(*   | _, _ => None *)
(*   end. *)

(* Definition select_stmt (stmt: statement) (sel: selector) : option statement := *)
(*   fold_right select_stmt_aux (Some stmt) sel. *)

(** Maybe we can use fold_right to implement select_stmt and reverse *)
(* the selectors to simplify the proof *)
Fixpoint select_stmt (stmt: statement) (sel: selector) : option statement :=
  match sel, stmt with
  | nil, _ => Some stmt
  | Selseqleft :: sel', Ssequence s1 s2 => select_stmt s1 sel'
  | Selseqright :: sel', Ssequence s1 s2 => select_stmt s2 sel'
  | Selifthen :: sel', Sifthenelse _ s1 s2 => select_stmt s1 sel'
  | Selifelse :: sel', Sifthenelse _ s1 s2 => select_stmt s2 sel'
  | Selloop :: sel', Sloop s => select_stmt s sel'
  | _, _ => None
  end.

(* Change in place the statement resided in this selector to an another
statement. And return the modified statement *)
(** TODO: we do not want to use [rev] *)

(* Fixpoint update_stmt_aux (root: statement) (sel: selector) (stmt: statement): option statement := *)
(*   match sel, root with *)
(*   | nil, _ => Some stmt *)
(*   | Selseqleft :: sel', Ssequence s1 s2 => select_stmt s1 sel' *)
(*   | Selseqright :: sel', Ssequence s1 s2 => select_stmt s2 sel' *)
(*   | Selifthen :: sel', Sifthenelse _ s1 s2 => select_stmt s1 sel' *)
(*   | Selifelse :: sel', Sifthenelse _ s1 s2 => select_stmt s2 sel' *)
(*   | Selloop :: sel', Sloop s => select_stmt s sel' *)
(*   end.   *)
  (* match sel, root with *)
  (* | nil, _ => Some stmt *)
  (* | Selseqleft :: sel', Ssequence s1 s2 => *)
  (*     match (update_stmt_aux s1 sel' stmt) with *)
  (*     | Some s1' => Some (Ssequence s1' s2) *)
  (*     | None => None *)
  (*     end *)
  (* | Selseqright :: sel', Ssequence s1 s2 =>       *)
  (*     match (update_stmt_aux s2 sel' stmt) with *)
  (*     | Some s2' => Some (Ssequence s1 s2') *)
  (*     | None => None *)
  (*     end *)
  (* | Selifthen :: sel', Sifthenelse e s1 s2 => *)
  (*     match (update_stmt_aux s1 sel' stmt) with *)
  (*     | Some s1' => Some (Sifthenelse e s1' s2) *)
  (*     | None => None *)
  (*     end *)
  (* | Selifelse :: sel', Sifthenelse e s1 s2 => *)
  (*     match (update_stmt_aux s2 sel' stmt) with *)
  (*     | Some s2' => Some (Sifthenelse e s1 s2') *)
  (*     | None => None *)
  (*     end *)
  (* | Selloop :: sel', Sloop s => *)
  (*     match (update_stmt_aux s sel' stmt) with *)
  (*     | Some s' => Some (Sloop s') *)
  (*     | None => None *)
  (*     end *)
  (* | _, _ => None *)
  (* end. *)

Fixpoint update_stmt (root: statement) (sel: selector) (stmt: statement): option statement :=
  match sel, root with
  | nil, _ => Some stmt
  | Selseqleft :: sel', Ssequence s1 s2 =>
      match (update_stmt s1 sel' stmt) with
      | Some s1' => Some (Ssequence s1' s2)
      | None => None
      end
  | Selseqright :: sel', Ssequence s1 s2 =>      
      match (update_stmt s2 sel' stmt) with
      | Some s2' => Some (Ssequence s1 s2')
      | None => None
      end
  | Selifthen :: sel', Sifthenelse e s1 s2 =>
      match (update_stmt s1 sel' stmt) with
      | Some s1' => Some (Sifthenelse e s1' s2)
      | None => None
      end
  | Selifelse :: sel', Sifthenelse e s1 s2 =>
      match (update_stmt s2 sel' stmt) with
      | Some s2' => Some (Sifthenelse e s1 s2')
      | None => None
      end
  | Selloop :: sel', Sloop s =>
      match (update_stmt s sel' stmt) with
      | Some s' => Some (Sloop s')
      | None => None
      end
  | _, _ => None
  end.

(** ** Control flow graph based on selector *)

Definition node := positive.

(* An instruction  is either a selector or a control command (e.g., if-then-else) *)
Inductive instruction : Type :=
  | Inop: node -> instruction
  | Isel: selector -> node -> instruction
  | Icond: expr -> node -> node -> instruction
  | Iend: instruction.

Definition rustcfg := PTree.t instruction.

Definition successors_instr (i: instruction) : list node :=
  match i with
  | Inop n => n :: nil
  | Isel _ n => n :: nil
  | Icond _ n1 n2 => n1 :: n2 :: nil
  | Iend => nil
  end.

Definition get_stmt (stmt: statement) (cfg: rustcfg) (pc: node) : option statement :=
  match cfg!pc with
  | Some instr =>
      match instr with
      | Isel sel _ =>
          select_stmt stmt sel
      | _ => None
      end
  | None => None
  end.


(** ** Generate CFG from a statement *)

(** * Translation state *)

Record generator: Type := mkstate {
  st_nextnode: node;
  st_code: rustcfg;
  st_wf: forall (pc: node), Plt pc st_nextnode \/ st_code!pc = None
}.


Inductive state_incr: generator -> generator -> Prop :=
  state_incr_intro:
    forall (s1 s2: generator)
    (PLE: Ple s1.(st_nextnode) s2.(st_nextnode))
    (INCL: forall pc, s1.(st_code)!pc = None
                 \/ s2.(st_code)!pc = s1.(st_code)!pc)
    (* there is an append strategy of the elements of s1 and s2 under
    the permutation *)
    (PERMU: exists l, Permutation (PTree.elements (st_code s2)) (PTree.elements (st_code s1) ++ l)),
    state_incr s1 s2.

Lemma state_incr_refl:
  forall s, state_incr s s.
Proof.
  intros. apply state_incr_intro.
  apply Ple_refl.
  intros. auto.
  (* permutation *)
  exists nil. erewrite app_nil_r.
  reflexivity.
Qed.

Lemma state_incr_trans:
  forall s1 s2 s3, state_incr s1 s2 -> state_incr s2 s3 -> state_incr s1 s3.
Proof.
  intros. inv H; inv H0. apply state_incr_intro.
  apply Ple_trans with (st_nextnode s2); assumption.
  intros. generalize (INCL pc) (INCL0 pc). intuition congruence.
  destruct PERMU0. destruct PERMU.
  exists (x0++x). etransitivity. eauto.
  erewrite app_assoc.
  eapply Permutation_app. auto.
  reflexivity.
Qed.


(** ** The generator and error monad *)

(* just copy from RTLgen *)

Inductive res (A: Type) (s: generator): Type :=
  | Err: Errors.errmsg -> res A s
  | Res: A -> forall (s': generator), state_incr s s' -> res A s.

Arguments Res [A s].
Arguments Err [A s].

Definition mon (A: Type) : Type := forall (s: generator), res A s.

Definition ret {A: Type} (x: A) : mon A :=
  fun (s: generator) => Res x s (state_incr_refl s).


Definition error {A: Type} (msg: Errors.errmsg) : mon A := 
  fun (s: generator) => Err msg.

Definition bind {A B: Type} (f: mon A) (g: A -> mon B) : mon B :=
  fun (s: generator) =>
    match f s with
    | Err msg => Err msg
    | Res a s' i =>
        match g a s' with
        | Err msg => Err msg
        | Res b s'' i' => Res b s'' (state_incr_trans s s' s'' i i')
        end
    end.

Definition bind2 {A B C: Type} (f: mon (A * B)) (g: A -> B -> mon C) : mon C :=
  bind f (fun xy => g (fst xy) (snd xy)).

Declare Scope cfg_monad_scope.
Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200): cfg_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200): cfg_monad_scope.

Definition handle_error {A: Type} (f g: mon A) : mon A :=
  fun (s: generator) =>
    match f s with
    | Res a s' i => Res a s' i
    | Err _ => g s
    end.

(** monadInv for this error monad *)

Remark bind_inversion:
  forall (A B: Type) (f: mon A) (g: A -> mon B)
         (y: B) (s1 s3: generator) (i: state_incr s1 s3),
  bind f g s1 = Res y s3 i ->
  exists x, exists s2, exists i1, exists i2,
  f s1 = Res x s2 i1 /\ g x s2 = Res y s3 i2.
Proof.
  intros until i. unfold bind. destruct (f s1); intros.
  discriminate.
  exists a; exists s'; exists s.
  destruct (g a s'); inv H.
  exists s0; auto.
Qed.

Remark bind2_inversion:
  forall (A B C: Type) (f: mon (A*B)) (g: A -> B -> mon C)
         (z: C) (s1 s3: generator) (i: state_incr s1 s3),
  bind2 f g s1 = Res z s3 i ->
  exists x, exists y, exists s2, exists i1, exists i2,
  f s1 = Res (x, y) s2 i1 /\ g x y s2 = Res z s3 i2.
Proof.
  unfold bind2; intros.
  exploit bind_inversion; eauto.
  intros [[x y] [s2 [i1 [i2 [P Q]]]]]. simpl in Q.
  exists x; exists y; exists s2; exists i1; exists i2; auto.
Qed.

Ltac monadInv1 H :=
  match type of H with
  | (Res _ _ _ = Res _ _ _) =>
      inversion H; clear H; try subst
  | (Err _ = Res _ _ _) =>
      discriminate
  | (@ret _ _ _ = Res _ _ _) =>
      inversion H; clear H; try subst
  | (@error _ _ _ = Res _ _ _) =>
      discriminate
  | (bind ?F ?G ?S = Res ?X ?S' ?I) =>
      let x := fresh "x" in (
      let s := fresh "s" in (
      let i1 := fresh "INCR" in (
      let i2 := fresh "INCR" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion _ _ F G X S S' I H) as [x [s [i1 [i2 [EQ1 EQ2]]]]];
      clear H;
      try (monadInv1 EQ2)))))))
  | (bind2 ?F ?G ?S = OK ?X ?S' ?I) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let s := fresh "s" in (
      let i1 := fresh "INCR" in (
      let i2 := fresh "INCR" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion _ _ _ F G X S S' I H) as [x1 [x2 [s [i1 [i2 [EQ1 EQ2]]]]]];
      clear H;
      try (monadInv1 EQ2))))))))
  end.

Ltac monadInv H :=
  match type of H with
  | (@ret _ _ _ = Res _ _ _) => monadInv1 H
  | (@error _ _ _ = Res _ _ _) => monadInv1 H
  | (bind ?F ?G ?S = Res ?X ?S' ?I) => monadInv1 H
  | (bind2 ?F ?G ?S = Res ?X ?S' ?I) => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.


(** ** Operations on generator *)

(** The initial generator (empty CFG). *)

Remark init_state_wf:
  forall pc, Plt pc 1%positive \/ (PTree.empty instruction)!pc = None.
Proof. intros; right; apply PTree.gempty. Qed.

Definition init_state : generator :=
  mkstate 1%positive (PTree.empty instruction) init_state_wf.


Remark add_instr_wf:
  forall s i pc,
  let n := s.(st_nextnode) in
  Plt pc (Pos.succ n) \/ (PTree.set n i s.(st_code))!pc = None.
Proof.
  intros. case (peq pc n); intro.
  subst pc; left; apply Plt_succ.
  rewrite PTree.gso; auto.
  elim (st_wf s pc); intro.
  left. apply Plt_trans_succ. exact H.
  right; assumption.
Qed.

Remark add_instr_incr:
  forall s i,
  let n := s.(st_nextnode) in                                
  state_incr s (mkstate (Pos.succ n)
                  (PTree.set n i s.(st_code))
                  (add_instr_wf s i)).
Proof.
intros.
  constructor; simpl.
  apply Ple_succ.
  intros. destruct (st_wf s pc). right. apply PTree.gso. apply Plt_ne; auto. auto.
  (* permutation *)
  exists [(n,i)].  
  exploit (@PTree.elements_remove instruction n i (PTree.set n i (st_code s))).
  eapply PTree.gss.
  intros (l1 & l2 & A1 & A2).
  rewrite A1.
  assert (A3: PTree.elements (st_code s) = l1 ++ l2).
  { erewrite <- A2.
    eapply PTree.elements_extensional.
    intros. rewrite PTree.grspec.
    destruct s. simpl in *.
    destruct (st_wf0 i0).
    - destruct PTree.elt_eq. subst.
      unfold n in H. unfold Plt in H. exfalso. eapply Pos.lt_irrefl. eauto.
      erewrite PTree.gso; auto.
    - destruct PTree.elt_eq. subst. auto.
      erewrite PTree.gso; auto. }
  rewrite A3.
  rewrite <- app_assoc. eapply Permutation_app.
  reflexivity. eapply Permutation_cons_app. rewrite app_nil_r. reflexivity.  
Qed.

Definition add_instr (i: instruction) : mon node :=
  fun s =>
    let n := s.(st_nextnode) in
    Res n
       (mkstate (Pos.succ n) (PTree.set n i s.(st_code))
                (add_instr_wf s i))
       (add_instr_incr s i).

(** [add_instr] can be decomposed in two steps: reserving a fresh
  CFG node, and filling it later with an instruction.  This is needed
  to compile loops. *)

Remark reserve_instr_wf:
  forall s pc,
  Plt pc (Pos.succ s.(st_nextnode)) \/ s.(st_code)!pc = None.
Proof.
  intros. elim (st_wf s pc); intro.
  left; apply Plt_trans_succ; auto.
  right; auto.
Qed.

Remark reserve_instr_incr:
  forall s,
  let n := s.(st_nextnode) in
  state_incr s (mkstate (Pos.succ n)
                  s.(st_code)
                      (reserve_instr_wf s)).
Proof.
  intros; constructor; simpl.
  apply Ple_succ.
  auto.
  (* permutation *)
  exists nil. rewrite app_nil_r. reflexivity.
Qed.

Definition reserve_instr: mon node :=
  fun (s: generator) =>
  let n := s.(st_nextnode) in
  Res n
     (mkstate (Pos.succ n) s.(st_code) (reserve_instr_wf s))
     (reserve_instr_incr s).

Remark update_instr_wf:
  forall s n i,
  Plt n s.(st_nextnode) ->
  forall pc,
  Plt pc s.(st_nextnode) \/ (PTree.set n i s.(st_code))!pc = None.
Proof.
  intros.
  case (peq pc n); intro.
  subst pc; left; assumption.
  rewrite PTree.gso; auto. exact (st_wf s pc).
Qed.

Remark update_instr_incr:
  forall s n i (LT: Plt n s.(st_nextnode)),
  s.(st_code)!n = None ->
  state_incr s
             (mkstate s.(st_nextnode) (PTree.set n i s.(st_code))
                     (update_instr_wf s n i LT)).
Proof.
  intros.
  constructor; simpl; intros.
  apply Ple_refl.
  rewrite PTree.gsspec. destruct (peq pc n). left; congruence. right; auto.
  (* permutation *)
  (* permutation *)
  exists [(n,i)].
  exploit (@PTree.elements_remove instruction n i (PTree.set n i (st_code s))).
  eapply PTree.gss.
  intros (l1 & l2 & A1 & A2).
  rewrite A1.
  assert (A3: PTree.elements (st_code s) = l1 ++ l2).
  { erewrite <- A2.
    eapply PTree.elements_extensional.
    intros. rewrite PTree.grspec.
    destruct PTree.elt_eq. subst. auto.
      erewrite PTree.gso; auto. }
  rewrite A3.
  rewrite <- app_assoc. eapply Permutation_app.
  reflexivity. eapply Permutation_cons_app. rewrite app_nil_r. reflexivity.  
Qed.

Definition check_empty_node:
  forall (s: generator) (n: node), { s.(st_code)!n = None } + { True }.
Proof.
  intros. case (s.(st_code)!n); intros. right; auto. left; auto.
Defined.

Definition update_instr (n: node) (i: instruction) : mon unit :=
  fun s =>
    match plt n s.(st_nextnode), check_empty_node s n with
    | left LT, left EMPTY =>
        Res tt
           (mkstate s.(st_nextnode) (PTree.set n i s.(st_code))
                    (update_instr_wf s n i LT))
           (update_instr_incr s n i LT EMPTY)
    | _, _ =>
        Err (Errors.msg "RTLgen.update_instr")
    end. 


Local Open Scope cfg_monad_scope.

(** Translation of statement *)

Section COMPOSITE_ENV.

Variable (ce: composite_env).

Import ListNotations.

Fixpoint transl_stmt (end_node: node) (stmt: statement) (sel: selector) 
(succ: node) (cont: option node) (brk: option node) {struct stmt} 
: mon node :=
  let transl_stmt := transl_stmt end_node in
  match stmt with
  | Sskip =>
      ret succ
  | Sassign p e =>
      add_instr (Isel sel succ)
  | Sassign_variant p enum_id fid e =>
      add_instr (Isel sel succ)
  | Sbox p e =>
      add_instr (Isel sel succ)
  | Ssequence stmt1 stmt2 =>
      do succ2 <- transl_stmt stmt2 (sel ++ [Selseqright]) succ cont brk;
      do succ1 <- transl_stmt stmt1 (sel ++ [Selseqleft]) succ2 cont brk;
      ret succ1
  | Sifthenelse e stmt1 stmt2 =>
      do n1 <- transl_stmt stmt1 (sel ++ [Selifthen]) succ cont brk;
      do n2 <- transl_stmt stmt2 (sel ++ [Selifelse]) succ cont brk;
      do n3 <- add_instr (Icond e n1 n2);
      ret n3
  | Sloop stmt =>
      do loop_jump_node <- reserve_instr;
      (* The succ in function body is loop_start *)
      do body_start <- transl_stmt stmt (sel ++ [Selloop]) loop_jump_node (Some loop_jump_node) (Some succ);
      do _ <- update_instr loop_jump_node (Inop body_start);
      (* return loop_jump_node and return body_start are equivalent *)
      ret loop_jump_node
  | Sbreak =>
      match brk with
      | None =>
          error (Errors.msg "No loop outside the break: transl_stmt")
      | Some brk =>
          (* no need to add an instruction *)
          (* add_instr (Inop brk) *)
          ret brk
      end
  | Scontinue =>
      match cont with
      | None =>
          error (Errors.msg "No loop outside the continue")
      | Some cont =>
          (* add_instr (Inop cont) *)
          ret cont
      end
  | Sstoragelive id =>
      add_instr (Isel sel succ)
  | Sstoragedead id =>
      add_instr (Isel sel succ)
  | Sdrop p =>
      add_instr (Isel sel succ)
  | Scall p a al =>
      add_instr (Isel sel succ)
  | Smethod_call p receiver method_name al =>
      add_instr (Isel sel succ)
  | Sreturn e =>
      add_instr (Isel sel end_node)
    end.

Definition generate_cfg' (stmt: statement): mon node :=
  (* return node *)
  do return_node <- add_instr Iend;
  transl_stmt return_node stmt nil return_node None None.

Definition generate_cfg (stmt: statement): Errors.res (node * rustcfg) :=  
  match generate_cfg' stmt init_state with
  | Res start st _ =>
      Errors.OK (start, st.(st_code))
  | Err msg =>
      Errors.Error msg
  end.
  

End COMPOSITE_ENV.


(** * Relations between the generated CFG and the source statement *)

(* Translation relation of the generate_cfg: [tr_stmt body cfg stmt pc
  out cont break endn] holds if the graph [cfg], starting at node
  [pc], contains instructions that perform the RustIR statement
  [stmt]. These instructions branch to node [out] if the statement
  terminates normally, branch to node [cont] if the statement reaches
  Scontinue, branch to break if the statement reaches Sbreak and
  branch to [endn] if the statement returns *)
Inductive tr_stmt (body: statement) (cfg: rustcfg) : statement -> node -> node -> option node -> option node -> node -> Prop :=
| tr_Sskip: forall pc cont brk endn,    
    tr_stmt body cfg Sskip pc pc cont brk endn
| tr_Sassign: forall pc next sel p e cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sassign p e)),
    tr_stmt body cfg (Sassign p e) pc next cont brk endn
| tr_Sassign_variant: forall pc next sel p e enum_id fid cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sassign_variant p enum_id fid e)),
    tr_stmt body cfg (Sassign_variant p enum_id fid e) pc next cont brk endn
| tr_Sbox: forall pc next sel p e cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sbox p e)),
    tr_stmt body cfg (Sbox p e) pc next cont brk endn
| tr_Sstoragelive: forall pc next sel id cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sstoragelive id)),
    tr_stmt body cfg (Sstoragelive id) pc next cont brk endn
| tr_Sstoragedead: forall pc next sel id cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sstoragedead id)),
    tr_stmt body cfg (Sstoragedead id) pc next cont brk endn
| tr_Sdrop: forall pc next sel p cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sdrop p)),
    tr_stmt body cfg (Sdrop p) pc next cont brk endn
| tr_Scall: forall pc next sel p e args cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Scall p e args)),
    tr_stmt body cfg (Scall p e args) pc next cont brk endn
| tr_Ssequence: forall s1 s2 n1 n2 n3 cont brk endn
    (STMT1: tr_stmt body cfg s1 n1 n2 cont brk endn)
    (STMT2: tr_stmt body cfg s2 n2 n3 cont brk endn),
    tr_stmt body cfg (Ssequence s1 s2) n1 n3 cont brk endn
| tr_Sifthenelse: forall s1 s2 e pc n1 n2 endif cont brk endn
    (STMT1: tr_stmt body cfg s1 n1 endif cont brk endn)
    (STMT2: tr_stmt body cfg s2 n2 endif cont brk endn)
    (SEL: cfg ! pc = Some (Icond e n1 n2)),
    tr_stmt body cfg (Sifthenelse e s1 s2) pc endif cont brk endn
| tr_Sloop: forall s next loop_start loop_jump_node cont brk endn
    (STMT: tr_stmt body cfg s loop_start loop_jump_node (Some loop_jump_node) (Some next) endn)
    (SEL: cfg ! loop_jump_node = Some (Inop loop_start)),
    (* next is not specific because loop is impossible to terminate
    normally *)
    tr_stmt body cfg (Sloop s) loop_jump_node next brk cont endn
(* backward traversal of CFG. [next] node is used in tr_cont, so it
should matches the AST *)
| tr_Sbreak: forall brk cont endn next,
    tr_stmt body cfg Sbreak brk next cont (Some brk) endn
| tr_Scontinue: forall brk cont endn next,
    tr_stmt body cfg Scontinue cont next (Some cont) brk endn
| tr_Sreturn: forall pc sel succ endn e cont brk
    (SEL: cfg ! pc = Some (Isel sel endn))
    (STMT: select_stmt body sel = Some (Sreturn e)),
    tr_stmt body cfg (Sreturn e) pc succ cont brk endn
.

Inductive tr_fun (f: function) (nret: node) : node -> rustcfg -> Prop :=
| tr_fun_intro: forall entry cfg
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (STMT: tr_stmt f.(fn_body) cfg f.(fn_body) entry nret None None nret)
    (RET: cfg ! nret = Some Iend),
    tr_fun f nret entry cfg.


(** Comment it because we changed the definition of select_stmt and
update_stmt, and tr_fun is unused in the proof of the compilation *)
Lemma add_instr_at:
    forall i n s s' R, add_instr i s = Res n s' R ->
    (st_code s') ! n = Some i.
Proof.
  intros. monadInv H. simpl. rewrite PTree.gss. auto.
Qed.


Lemma update_instr_at:
    forall i n x s s' R, update_instr n i s = Res x s' R ->
    (st_code s') ! n = Some i.
Proof.
  intros. unfold update_instr in H.
  destruct (plt n (st_nextnode s)) eqn:E;
  destruct (check_empty_node s n) eqn:E2; inversion H.
  eapply PTree.gss.
Qed.

Lemma instr_at_incr:
  forall s1 s2 n i,
  state_incr s1 s2 -> s1.(st_code)!n = Some i -> s2.(st_code)!n = Some i.
Proof.
  intros. inv H.
  destruct (INCL n); congruence.
Qed.


(** * A general framework for CFG compilation based on selectors *)

Local Open Scope error_monad_scope.

Definition set_stmt (pc: node) (body: statement) (sel: selector) 
(s: statement) : Errors.res statement :=
  match update_stmt body sel s with
  | Some body1 => OK body1
  | None =>
      Error [CTX pc; MSG " update_stmt error in set_stmt"]
  end.


Section TRANSL.

Context {AN: Type} {An: Type} (get_an: AN -> node -> An).
Context (ae: AN).
Context (transl_stmt: An -> statement -> Errors.res statement).

(* There is no way to translate the condition expression because we do
not know its location in the AST, we can only check its validity
(e.g., in the move checking). To support translation of the condition
expression, we need to add selector for it, but it would make the
proof more compilated. *)
Context (check_expr: An -> expr -> Errors.res unit).

Definition transl_on_instr (src: statement) (pc: node) (instr: instruction)
 : Errors.res statement :=
  match instr with
  | Isel sel _ =>
      match select_stmt src sel with
      | Some s =>
          match transl_stmt (get_an ae pc) s with
          | OK ts =>
             set_stmt pc src sel ts
          | Error msg =>
             Error ((CTX pc) :: msg)
          end
      | None =>
          Error [CTX pc; MSG " select_stmt error in transl_on_instr"]
      end
  | Icond e _ _ =>
      do _ <- check_expr (get_an ae pc) e;
      OK src
  (* no way to translate them in the AST side without selector *)
  | _ => OK src
  end.

Definition transl_on :=
  fun body pc instr => 
    do body' <- body; transl_on_instr body' pc instr.

Definition transl_on_cfg (src: statement) (cfg: rustcfg) 
: Errors.res statement :=
  PTree.fold transl_on cfg (OK src).

(* Translation relation between source statment and target statement *)

Section SPEC.

(* Dynamic elaboration of statement based on own_env *)
Inductive match_stmt (body: statement) (cfg: rustcfg) : statement -> 
statement -> node -> node -> option node -> option node -> node -> Prop :=
| match_Sskip: forall pc cont brk endn,
    match_stmt body cfg Sskip Sskip pc pc cont brk endn
| match_Sassign: forall pc next sel p e ts cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sassign p e))
    (TR: transl_stmt (get_an ae pc) (Sassign p e) = OK ts),
    match_stmt body cfg (Sassign p e) ts pc next cont brk endn
| match_Sassign_variant: forall pc next sel p e enum_id fid ts cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sassign_variant p enum_id fid e))
    (TR: transl_stmt (get_an ae pc) (Sassign_variant p enum_id fid e) = OK ts),
    match_stmt body cfg (Sassign_variant p enum_id fid e) ts pc next cont brk endn
| match_Sbox: forall pc next sel p e ts cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sbox p e))
    (TR: transl_stmt (get_an ae pc) (Sbox p e) = OK ts),
    match_stmt body cfg (Sbox p e) ts pc next cont brk endn
| match_Sstoragelive: forall pc next sel ts id cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sstoragelive id))
    (TR: transl_stmt (get_an ae pc) (Sstoragelive id) = OK ts),
    match_stmt body cfg (Sstoragelive id) ts pc next cont brk endn
| match_Sstoragedead: forall pc next sel ts id cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sstoragedead id))
    (TR: transl_stmt (get_an ae pc) (Sstoragedead id) = OK ts),
    match_stmt body cfg (Sstoragedead id) ts pc next cont brk endn
| match_Sdrop: forall p pc next ts sel cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Sdrop p))
    (TR: transl_stmt (get_an ae pc) (Sdrop p) = OK ts),
    match_stmt body cfg (Sdrop p) ts pc next cont brk endn
| match_Scall: forall pc next sel ts p e l cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Scall p e l))
    (TR: transl_stmt (get_an ae pc) (Scall p e l) = OK ts),
    match_stmt body cfg (Scall p e l) ts pc next cont brk endn
| match_Smethod_call: forall pc next sel ts p receiver method_name l cont brk endn
    (SEL: cfg ! pc = Some (Isel sel next))
    (STMT: select_stmt body sel = Some (Smethod_call p receiver method_name l))
    (TR: transl_stmt (get_an ae pc) (Smethod_call p receiver method_name l) = OK ts),
    match_stmt body cfg (Smethod_call p receiver method_name l) ts pc next cont brk endn
| match_Ssequence: forall s1 ts1 s2 ts2 n1 n2 n3 cont brk endn
    (MSTMT1: match_stmt body cfg s1 ts1 n1 n2 cont brk endn)
    (MSTMT2: match_stmt body cfg s2 ts2 n2 n3 cont brk endn),
    match_stmt body cfg (Ssequence s1 s2) (Ssequence ts1 ts2) n1 n3 cont brk endn
| match_Sifthenelse: forall s1 ts1 s2 ts2 n n1 n2 endif cont brk endn e
    (MSTMT1: match_stmt body cfg s1 ts1 n1 endif cont brk endn)
    (MSTMT2: match_stmt body cfg s2 ts2 n2 endif cont brk endn)
    (MCOND: cfg ! n = Some (Icond e n1 n2))
    (CHECK: check_expr (get_an ae n) e = OK tt),
    (* For now, no way to compile the expression in Icond *)
    match_stmt body cfg (Sifthenelse e s1 s2) (Sifthenelse e ts1 ts2) n endif cont brk endn
| match_Sloop: forall s ts next loop_start loop_jump_node cont brk endn
    (MSTMT: match_stmt body cfg s ts loop_start loop_jump_node (Some loop_jump_node) (Some next) endn)
    (START: cfg ! loop_jump_node = Some (Inop loop_start)),
    match_stmt body cfg (Sloop s) (Sloop ts) loop_jump_node next brk cont endn
| match_Sbreak: forall brk cont endn next,
    match_stmt body cfg Sbreak Sbreak brk next cont (Some brk) endn
| match_Scontinue: forall brk cont endn next,
    match_stmt body cfg Scontinue Scontinue cont next (Some cont) brk endn
| match_Sreturn: forall pc sel e ts cont brk endn succ
    (SEL: cfg ! pc = Some (Isel sel endn))
    (STMT: select_stmt body sel = Some (Sreturn e))
    (TR: transl_stmt (get_an ae pc) (Sreturn e) = OK ts),
    match_stmt body cfg (Sreturn e) ts pc succ cont brk endn
.

(** * Proof of the translation on the CFG meets the specification (match_stmt) *)

(* 1. Background:

During the compilation and static checking process of RustIR, we
temporarily convert it into a Control Flow Graph (CFG). We then use
the analysis results from this CFG to transform the original Abstract
Syntax Tree (AST). To maintain a mapping between the nodes in the CFG
and the original AST, we assign each instruction (specifically, those
instructions that would execute, like assignments) a selector. This
selector represents a path leading to a leaf node in the AST.

The compilation or static checking process (handled by the function
transl_on_cfg) traverses the CFG. For each instruction, it extracts
the selector (if present) and then directly translates the
corresponding statement in the original AST using the function
transl_on_instr. This approach allows us to perform transformations on
the AST based on the structure and information obtained from the CFG.

To connect the statements before and after compilation, we define a
translation relation that uses the intermediate CFG as a bridge. This
relation is divided into two groups: one for executable statements and
another for control statements. Specifically, we use the translation
function "transl_stmt" to relate executable statements, while control
statements are linked through a tuple structure (pc, next, cont, brk),
which represents the current program counter, the next program
counter, the continuation point and the break point.

The final theorem, transl_on_cfg_meet_spec, asserts that if an AST can
be successfully translated into a CFG and then processed by
transl_on_cfg, we can establish the match_stmt relation between the
original AST and the transformed AST. The following comments outline
our strategy for proving transl_on_cfg_meet_spec.

2. Proof structure

Top-level theorem [transl_on_cfg_meet_spec]: the translation on a
generated CFG satisfies the translation specification. It is proved by
[transl_on_cfg_charact] which says that the translation of a fragment
of an AST (by converting it to a fragment of the CFG) satisfies the
specification. This lemma is proved by induction on the AST:

2.1 Base case of [transl_on_cfg_charact]: If is mainly proved by
add_instr_charact, which says that adding an instruction (whose
selctor (called sel)is disjoint with all others selector in the graph)
to the graph, and then selecting the statement using sel in the
transformed AST returns the translated result. The disjointness
property is used to ensure that whatever the position of the added
instruction in the graph, the translation of others instruction cannot
affect its translation.

2.2 Induction case of [transl_on_cfg_charact]: the key proof that
adding a set of disjoint selectors does not change the selction result
(proved by [transl_on_cfg_state_incr_unchanged]). To prove this
property, we need to strength the unchanged property because the
adding selectors may be put into arbitary position of the graph. So we
need to prove that if all the selectors of a graph are norepet
(defined by list_sel_norepet and itosels), then any permutaion of the
graph nodes does not change the result of the translation on this
graph (lemma [transl_on_instrs_permutation_same]). The lemma
[transl_stmt_sel_norepet] shows that the CFG generated by
RustIRcfg.transl_stmt does not introduce repeated selectors.

Some tricky proof in the induction case is about the unchanged
property of the condition expression in the Sifthenelse statment. We
need to show that the translation on the graph does not change the
condition expression but it is not easy because there may be some
selectors whose children contain some condition expression (we do not
enforce that every selector in the graph is leaf selector). We can
weaken the unchanged property by showing that when for a selector sel
which is under translation, if there is no selctor that is a prefix of
sel, we can say that the statement (before and after the translation)
selected by this selctor satisfies [stmt_memb_eq]. It is proved by
[transl_on_cfg_unchanged_statement_member]

 *)




(* Copy from Cminorgenproof *)
Remark permutation_norepet:
  forall (A: Type) (l l': list A), Permutation l l' -> list_norepet l -> list_norepet l'.
Proof.
  induction 1; intros.
  constructor.
  inv H0. constructor; auto. red; intros; elim H3. apply Permutation_in with l'; auto. apply Permutation_sym; auto.
  inv H. simpl in H2. inv H3. constructor. simpl; intuition. constructor. intuition. auto.
  eauto.
Qed.


Lemma select_stmt_nil: forall s,
    select_stmt s [] = Some s.
  induction s; auto.
Qed.

Lemma select_stmt_app: forall sel1 sel2 s1 s2 s3,
    select_stmt s1 sel1 = Some s2 ->
    select_stmt s2 sel2 = Some s3 ->
    select_stmt s1 (sel1 ++ sel2) = Some s3.
Proof.
  induction sel1; intros.
  - simpl. erewrite select_stmt_nil in H. inv H. auto.
  - destruct a; destruct s1; simpl in *; try congruence; eauto.
Qed.

Lemma select_stmt_app_inv: forall l1 l2 body s,
    select_stmt body (l1 ++ l2) = Some s ->
    exists body1, select_stmt body l1 = Some body1
             /\ select_stmt body1 l2 = Some s.
Proof.
  induction l1; intros; simpl in *.
  - exists body. split. eapply select_stmt_nil.
    auto.
  - destruct a; destruct body; simpl in *; try congruence; eauto.
Qed.

Lemma update_stmt_nil: forall s body,
    update_stmt body [] s = Some s.
  induction body; auto.
Qed.


Lemma update_stmt_select: forall sel body1 body2 s,
    update_stmt body1 sel s = Some body2 ->
    select_stmt body2 sel = Some s.
Proof.
  induction sel; intros; simpl in *.
  - erewrite update_stmt_nil in H. inv H.
    eapply select_stmt_nil.
  - destruct a; destruct body1; simpl in *; try congruence; eauto.
    + destruct (update_stmt body1_1 sel s) eqn: A; try congruence.
      inv H. eapply IHsel; eauto.
    + destruct (update_stmt body1_2 sel s) eqn: A; try congruence.
      inv H. eapply IHsel; eauto.
    + destruct (update_stmt body1_1 sel s) eqn: A; try congruence.
      inv H. eapply IHsel; eauto.
    + destruct (update_stmt body1_2 sel s) eqn: A; try congruence.
      inv H. eapply IHsel; eauto.
    + destruct (update_stmt body1 sel s) eqn: A; try congruence.
      inv H. eapply IHsel; eauto.
Qed.

Lemma set_stmt_select: forall sel body1 body2 s pc,
    set_stmt pc body1 sel s = OK body2 ->
    select_stmt body2 sel = Some s.
Proof.
  intros. unfold set_stmt in H.
  destruct (update_stmt body1 sel s) eqn: A; try congruence.
  inv H.
  eapply update_stmt_select; eauto.
Qed.  

(* select and then set has no problem *)
Lemma select_stmt_then_update: forall sel body s1 s2,
    select_stmt body sel = Some s1 ->
    exists body', update_stmt body sel s2 = Some body'.
Proof.
  induction sel; intros; simpl in *.
  - rewrite select_stmt_nil in H. inv H.
    exists s2. eapply update_stmt_nil.
  - destruct a; destruct body; simpl in *; try congruence.
    1-5: edestruct IHsel; eauto; erewrite H0; eauto.   
Qed.
    
(* select and then set has no problem *)
Lemma select_stmt_then_set: forall sel body s1 s2 pc,
    select_stmt body sel = Some s1 ->
    exists body', set_stmt pc body sel s2 = OK body'.
Proof.
  intros. unfold set_stmt.
  edestruct select_stmt_then_update; eauto.
  erewrite H0. eauto.
Qed.

Lemma transl_on_instrs_error: forall l msg,
    fold_left (fun (a : Errors.res statement) (p : positive * instruction) =>
                 transl_on a (fst p) (snd p)) l (Error msg) = Error msg.
Proof.
  induction l; simpl; auto.
Qed.

Lemma update_stmt_disjoint_select: forall sel1 sel2 body1 body2 s1 s2,
    select_stmt body1 sel1 = Some s1 ->
    update_stmt body1 sel2 s2 = Some body2 ->
    selector_disjoint sel1 sel2 ->
    select_stmt body2 sel1 = Some s1.
Proof.
  induction sel1; intros.
  - inv H1.
  - inv H1.
    + destruct body1; destruct a; destruct s3; simpl in *; try congruence.
      * destruct (update_stmt body1_2 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
      * destruct (update_stmt body1_1 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
      * destruct (update_stmt body1_2 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
      * destruct (update_stmt body1_1 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
    + destruct body1; destruct a; simpl in *; try congruence.
      * destruct (update_stmt body1_1 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
      * destruct (update_stmt body1_2 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
      * destruct (update_stmt body1_1 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
      * destruct (update_stmt body1_2 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
      * destruct (update_stmt body1 l2 s2) eqn: A; try congruence. inv H0.
        simpl. eauto.
Qed.

(* Not like update_stmt_disjoint_select, the premise says that we can
get a statement from the body2 and the conclusion says that we can get
the same statement from the original body (body1)*)
Lemma update_stmt_disjoint_select_inv: forall sel1 sel2 body1 body2 s1 s2,
    select_stmt body2 sel1 = Some s1 ->
    update_stmt body1 sel2 s2 = Some body2 ->
    selector_disjoint sel1 sel2 ->
    select_stmt body1 sel1 = Some s1.
Proof.
  induction sel1; intros.
  - inv H1.
  - inv H1.
    + destruct body1; destruct s3; simpl in *; try congruence.
      * destruct (update_stmt body1_1 l2 s2) eqn: A; try congruence.
        inv H0. destruct a; simpl in *; try congruence.
      * destruct (update_stmt body1_2 l2 s2) eqn: A; try congruence.
        inv H0. destruct a; simpl in *; try congruence.
      * destruct (update_stmt body1_1 l2 s2) eqn: A; try congruence.
        inv H0. destruct a; simpl in *; try congruence.
      * destruct (update_stmt body1_2 l2 s2) eqn: A; try congruence.
        inv H0. destruct a; simpl in *; try congruence.
      * destruct (update_stmt body1 l2 s2) eqn: A; try congruence.
        inv H0. destruct a; simpl in *; try congruence.
    + destruct body1; destruct a; simpl in *; try congruence.
      * destruct (update_stmt body1_1 l2 s2) eqn: A; try congruence.
        inv H0. eauto.
      * destruct (update_stmt body1_2 l2 s2) eqn: A; try congruence.
        inv H0. eauto.
      * destruct (update_stmt body1_1 l2 s2) eqn: A; try congruence.
        inv H0. eauto.
      * destruct (update_stmt body1_2 l2 s2) eqn: A; try congruence.
        inv H0. eauto.
      * destruct (update_stmt body1 l2 s2) eqn: A; try congruence.
        inv H0. eauto.
Qed.        
            
Lemma set_stmt_disjoint_select: forall sel1 sel2 body1 body2 s1 s2 pc,
    select_stmt body1 sel1 = Some s1 ->
    set_stmt pc body1 sel2 s2 = OK body2 ->
    selector_disjoint sel1 sel2 ->
    select_stmt body2 sel1 = Some s1.
Proof.
  intros. unfold set_stmt in H0.
  destruct (update_stmt body1 sel2 s2) eqn: A in H0; try congruence.
  inv H0.
  eapply update_stmt_disjoint_select; eauto.
Qed.

Lemma set_stmt_disjoint_select_inv: forall sel1 sel2 body1 body2 s1 s2 pc,
    select_stmt body2 sel1 = Some s1 ->
    set_stmt pc body1 sel2 s2 = OK body2 ->
    selector_disjoint sel1 sel2 ->
    select_stmt body1 sel1 = Some s1.
Proof. 
  intros. unfold set_stmt in H0.
  destruct (update_stmt body1 sel2 s2) eqn: A in H0; try congruence.
  inv H0.
  eapply update_stmt_disjoint_select_inv; eauto.
Qed.

Lemma update_stmt_disjoint_reorder: forall sel1 sel2 (DIS: selector_disjoint sel1 sel2) body1 body2 body2' body3 stmt1 stmt2, 
    update_stmt body1 sel1 stmt1 = Some body2 ->
    update_stmt body2 sel2 stmt2 = Some body3 ->
    update_stmt body1 sel2 stmt2 = Some body2' ->
    update_stmt body2' sel1 stmt1 =Some  body3.
Proof.
  induction 1; intros.
  - destruct s1; destruct s2; try congruence; destruct body1; simpl in * ; try congruence.
    + destruct (update_stmt body1_1 l1 stmt1) eqn: A; try congruence.
      inv H0. simpl in *.
      destruct (update_stmt body1_2 l2 stmt2) eqn: B; try congruence.
      inv H1. inv H2. simpl. rewrite A. auto.
    + destruct (update_stmt body1_2 l1 stmt1) eqn: A; try congruence.
      inv H0. simpl in *.
      destruct (update_stmt body1_1 l2 stmt2) eqn: B; try congruence.
      inv H1. inv H2. simpl. rewrite A. auto.
    + destruct (update_stmt body1_1 l1 stmt1) eqn: A; try congruence.
      inv H0. simpl in *.
      destruct (update_stmt body1_2 l2 stmt2) eqn: B; try congruence.
      inv H1. inv H2. simpl. rewrite A. auto.
    + destruct (update_stmt body1_2 l1 stmt1) eqn: A; try congruence.
      inv H0. simpl in *.
      destruct (update_stmt body1_1 l2 stmt2) eqn: B; try congruence.
      inv H1. inv H2. simpl. rewrite A. auto.
  - destruct s; destruct body1; simpl in * ; try congruence.
    + destruct (update_stmt body1_1 l2 stmt2) eqn: A; try congruence.
      inv H1. simpl in *.
      destruct (update_stmt body1_1 l1 stmt1) eqn: B; try congruence.
      inv H. simpl in *.
      destruct (update_stmt s0 l2 stmt2) eqn: C; try congruence.
      inv H0. erewrite IHDIS; eauto.
    + destruct (update_stmt body1_2 l2 stmt2) eqn: A; try congruence.
      inv H1. simpl in *.
      destruct (update_stmt body1_2 l1 stmt1) eqn: B; try congruence.
      inv H. simpl in *.
      destruct (update_stmt s0 l2 stmt2) eqn: C; try congruence.
      inv H0. erewrite IHDIS; eauto.
    + destruct (update_stmt body1_1 l2 stmt2) eqn: A; try congruence.
      inv H1. simpl in *.
      destruct (update_stmt body1_1 l1 stmt1) eqn: B; try congruence.
      inv H. simpl in *.
      destruct (update_stmt s0 l2 stmt2) eqn: C; try congruence.
      inv H0. erewrite IHDIS; eauto.
    + destruct (update_stmt body1_2 l2 stmt2) eqn: A; try congruence.
      inv H1. simpl in *.
      destruct (update_stmt body1_2 l1 stmt1) eqn: B; try congruence.
      inv H. simpl in *.
      destruct (update_stmt s0 l2 stmt2) eqn: C; try congruence.
      inv H0. erewrite IHDIS; eauto.
    + destruct (update_stmt body1 l2 stmt2) eqn: A; try congruence.
      inv H1. simpl in *.
      destruct (update_stmt body1 l1 stmt1) eqn: B; try congruence.
      inv H. simpl in *.
      destruct (update_stmt s0 l2 stmt2) eqn: C; try congruence.
      inv H0. erewrite IHDIS; eauto.
Qed.

Lemma set_stmt_disjoint_reorder: forall sel1 sel2 body1 body2 body2' body3 s1 s2 pc1 pc2, 
    selector_disjoint sel1 sel2 ->
    set_stmt pc1 body1 sel1 s1 = OK body2 ->
    set_stmt pc2 body2 sel2 s2 = OK body3 ->
    set_stmt pc2 body1 sel2 s2 = OK body2' ->
    set_stmt pc1 body2' sel1 s1 = OK body3.
Proof.
  intros. unfold set_stmt in *.
  destruct (update_stmt body1 sel1 s1) eqn: A; try congruence.
  inv H0.
  destruct (update_stmt body2 sel2 s2) eqn: B; try congruence.
  inv H1.
  destruct (update_stmt body1 sel2 s2) eqn: C; try congruence.
  inv H2.
  erewrite update_stmt_disjoint_reorder; eauto.
Qed.

  
Lemma transl_on_instrs_unchanged: forall l sel body1 body2 s
    (SEL: select_stmt body1 sel = Some s)
    (TRANSL: fold_left (fun (a : Errors.res statement) (p : positive * instruction) =>
                          transl_on a (fst p) (snd p)) l (OK body1) = OK body2)
    (DISJOINT: forall pc sel1 n, In (pc, (Isel sel1 n)) l ->
                                selector_disjoint sel sel1),
    select_stmt body2 sel = Some s.
Proof.
  induction l; intros; simpl in *.
  - inv TRANSL. auto.
  - destruct (transl_on_instr body1 (fst a) (snd a)) eqn: A.
    2: { erewrite transl_on_instrs_error in TRANSL. congruence. }
    destruct a. simpl in *.
    unfold transl_on_instr in A.
    destruct i.
    + inv A. eapply IHl; eauto.
    + destruct (select_stmt body1 s1) eqn: SEL1; try congruence.
      destruct transl_stmt eqn: TR in A; try congruence.
      exploit set_stmt_select; eauto.
      intros SEL2.
      exploit DISJOINT. left. eauto. intros DIS.
      (* so select_stmt so sel = Some s *)      
      exploit set_stmt_disjoint_select. eapply SEL. eauto. auto.
      intros SEL3.
      eapply IHl; eauto.
    + Errors.monadInv A. eapply IHl; eauto.
    + inv A. eapply IHl; eauto.
Qed.
    
    
Lemma transl_on_cfg_unchanged: forall sel s body1 body2 cfg,
    select_stmt body1 sel = Some s ->
    transl_on_cfg body1 cfg = OK body2 ->
    (forall pc sel1 n, cfg ! pc = Some (Isel sel1 n) ->
                  selector_disjoint sel sel1) ->
    select_stmt body2 sel = Some s.
Proof.
  intros. unfold transl_on_cfg in H0.
  erewrite PTree.fold_spec in H0.
  eapply transl_on_instrs_unchanged; eauto.
  intros. eapply H1.
  eapply PTree.elements_complete. eauto.
Qed.
 
                    
(* Cases of atomic statement in transl_on_cfg_charact *)
Lemma add_instr_charact: forall sel  g n g' R body1 body2 stmt succ (* cont brk nret *)
    (TRSTMT: add_instr (Isel sel succ) g = Res n g' R)
    (SEL: select_stmt body1 sel = Some stmt)
    (TRANSL: transl_on_cfg body1 (st_code g') = OK body2)
    (DISJOINT: forall (pc : positive) (sel1 : selector) (n : node),
        (st_code g) ! pc = Some (Isel sel1 n) -> selector_disjoint sel sel1),
    exists ts,
      select_stmt body2 sel = Some ts
      /\ (st_code g') ! n = Some (Isel sel succ)
      /\ transl_stmt (get_an ae n) stmt = OK ts.
        (* match_stmt body1 (st_code g') stmt ts n succ2 cont brk nret. *)
Proof.
  intros.      
  unfold add_instr in TRSTMT. inv TRSTMT. simpl in *.
  set (pc:=st_nextnode g) in *.
  unfold transl_on_cfg in TRANSL.
  rewrite PTree.fold_spec in TRANSL.
  assert (A: (PTree.set pc (Isel sel succ) (st_code g)) ! pc = Some (Isel sel succ)).
  eapply PTree.gss.        
  exploit PTree.elements_remove; eauto.
  intros (l1 & l2 & B1 & B2).
  rewrite B1 in TRANSL.
  (* show disjointness of l1++l2 *)
  assert (E: forall i, (PTree.remove pc (PTree.set pc (Isel sel succ) (st_code g))) ! i = (st_code g) ! i).
  { intros.
    erewrite PTree.grspec.
    destruct PTree.elt_eq. subst.
    (* st_code must not contain pc by st_wf *)
    symmetry.
    destruct (st_wf g pc). unfold pc in *.
    unfold Plt in H. exfalso. eapply Pos.lt_irrefl. eauto.
    auto.
    erewrite PTree.gso; auto. }
  erewrite PTree.elements_extensional in B2; eauto.
  (* simplify TRANSL *)
  rewrite fold_left_app in TRANSL.
  set (transl:= (fun (a : Errors.res statement) (p : positive * instruction) =>
                   transl_on a (fst p) (snd p))) in *.
  set (body1' := (fold_left transl l1 (OK body1))) in *.
  simpl in TRANSL.

  unfold node in *.
  destruct ((transl body1' (pc, Isel sel succ))) eqn: C1 in TRANSL.
  2: { erewrite transl_on_instrs_error in TRANSL. congruence. }      
  (* monadInv C1 *)
  unfold transl, transl_on_instr in C1.
  simpl in C1.
  Errors.monadInv C1.
  unfold transl_on_instr in EQ0.
  destruct (select_stmt x sel) eqn: SEL1; try congruence.
  unfold body1' in EQ.
  destruct transl_stmt eqn: TR in EQ0; try congruence.
  (* transl on disjoint selector select_stmt is unchanged *)
  exploit transl_on_instrs_unchanged. eapply SEL. eauto.
  (* prove disjointness *)   
  intros. eapply DISJOINT. eapply PTree.elements_complete.
  erewrite B2. eapply in_app. eauto. intros SEL2.
  rewrite SEL1 in SEL2. inv SEL2.    
  exists s1.    
  split.
  (* set_stmt and then select it *)
  unfold set_stmt in EQ0.
  destruct (update_stmt x sel s1) eqn: UPDATE; try congruence.
  inv EQ0.
  exploit update_stmt_select; eauto. 
  intros SEL2.
  eapply transl_on_instrs_unchanged; eauto.
  (* prove disjointness *)   
  intros. eapply DISJOINT. eapply PTree.elements_complete.
  erewrite B2. eapply in_app. eauto.
  (* prove match_stmt *)
  split. eapply PTree.gss. auto.
  (* destruct stmt; simpl in ATOMIC; try contradiction. *)
  (* all: econstructor; try eapply PTree.gss; auto.  *)
Qed.


(* The new instructions in the translated cfg can only contain
   some selectors whose prefix is sel *)
Lemma transl_stmt_selectors_prefix: forall s nret sel1 sel2 n1 n2 n3 cont brk g1 g2 R pc,
    RustIRcfg.transl_stmt nret s sel1 n1 cont brk g1 = Res n2 g2 R ->
    (st_code g1) ! pc = None ->
    (st_code g2) ! pc = Some (Isel sel2 n3) ->
    exists l, sel1 ++ l = sel2.
Proof.
  Ltac solve_atomic TRANSL G2 :=
    inv TRANSL; simpl in *;
    erewrite PTree.gsspec in G2;
    destruct peq in G2; try congruence; inv G2;
    exists nil; eapply app_nil_r.
    
  induction s; intros until pc; intros TRANSL G1 G2; simpl in TRANSL; try solve_atomic TRANSL G2.  
  - inv TRANSL. congruence.
  - monadInv TRANSL.
    (* case analysis of pc in s *)
    inv INCR0. generalize (INCL pc). intros [A1|A2].
    + exploit IHs1; eauto. intros (l & A3). subst.
      erewrite <- app_assoc. eauto.
    + erewrite A2 in G2.
      exploit IHs2; eauto. intros (l & A3). subst.
      erewrite <- app_assoc. eauto.
  - monadInv TRANSL.
    assert (G3: (st_code s0) ! pc = Some (Isel sel2 n3)).
    { unfold add_instr in EQ0. inv EQ0. simpl in *.
      erewrite PTree.gsspec in G2.
      destruct peq in G2; try congruence. }
    (* case analysis of pc in s *)
    generalize INCR1. intros.
    inv INCR5. generalize (INCL pc). intros [A1|A2].
    + exploit IHs2; eauto. intros (l & A3). subst.
      erewrite <- app_assoc. eauto.
    + erewrite A2 in G3.
      exploit IHs1; eauto. intros (l & A3). subst.
      erewrite <- app_assoc. eauto.
  - monadInv TRANSL.
    assert (G3: (st_code s1) ! pc = Some (Isel sel2 n3)).
    {  unfold update_instr in EQ0. destruct plt in EQ0; try congruence.
       destruct (check_empty_node s1 n2); try congruence.
       inv EQ0. simpl in *.
       erewrite PTree.gsspec in G2.
       destruct peq in G2; try congruence. }
    assert (G4: (st_code s0) ! pc = None).
    { unfold reserve_instr in EQ. inv EQ.
      simpl in *. auto. }    
    exploit IHs; eauto.
    intros (l & A3). subst.
    erewrite <- app_assoc. eauto.
  - destruct brk; try congruence.
    inv TRANSL. congruence.
    monadInv TRANSL.
  - destruct cont; try congruence.
    inv TRANSL. congruence.
    monadInv TRANSL.
Qed.


Lemma selector_disjoint_sym: forall s1 s2,
    selector_disjoint s1 s2 ->
    selector_disjoint s2 s1.
Proof.
  induction s1; intros; inv H.
  - econstructor. auto.
  - eapply sel_disjoint_cons. eauto.
Qed.

Lemma selector_disjoint_app1: forall s1 s2 l,
    selector_disjoint s1 s2 ->
    selector_disjoint s1 (s2 ++ l).
Proof.
  induction s1; intros; inv H.
  - simpl. econstructor. auto.
  - simpl. eapply sel_disjoint_cons. eauto.
Qed.

Lemma selector_disjoint_app_left: forall s1 s2 l,
    selector_disjoint s1 s2 ->
    selector_disjoint (s1++l) s2.
Proof.
  intros. eapply selector_disjoint_sym.
  eapply selector_disjoint_app1.
  eapply selector_disjoint_sym. auto.
Qed.


Lemma selector_disjoint_app2: forall l s1 s2,
    selector_disjoint s1 s2 ->
    selector_disjoint (l ++ s1) (l ++ s2).
Proof.
  induction l; intros.
  - simpl. auto.
  - simpl. eapply sel_disjoint_cons. eauto.
Qed.

Lemma selector_disjoint_not_prefix: forall l1 l2,
    selector_disjoint (l1 ++ l2) l1 ->
    False.
Proof.
  induction l1; simpl in *; intros.
  - inv H.
  - inv H. congruence.
    eauto.
Qed.
      
Definition itosels (l: list (positive * instruction)) :=
  map (fun i => match i with | Isel sel _ => sel | _ => [] end)
  (filter (fun i => match i with | Isel _ _ => true | _ => false end)
    (map snd l)).

Let transl := (fun (a : Errors.res statement) (p : positive * instruction) =>
                 transl_on a (fst p) (snd p)).

(* Permutation is preserved if applying filter in two lists *)
Lemma Permutation_filter {A: Type} : forall (f: A -> bool) (l1 l2: list A),
    Permutation l1 l2 ->
    Permutation (filter f l1) (filter f l2).
Proof.
  induction 1.
  - simpl. constructor.
  - simpl. destruct (f x). apply perm_skip. auto.
    auto.
  - simpl. destruct (f x); destruct (f y).
    apply perm_swap. auto.    
    apply perm_skip. auto.
    reflexivity.
  - etransitivity. eauto. auto.
Qed.

Lemma Permutation_itosels : forall l1 l2,
    Permutation l1 l2 ->
    Permutation (itosels l1) (itosels l2).
Proof.
  unfold itosels. intros.
  apply Permutation_map. apply Permutation_filter.
  apply Permutation_map. auto.
Qed.

(* The list_sel_norepet property is preserved under the
  permutation *)
Lemma list_sel_norepet_permutation: forall l1 l2,
    Permutation l1 l2 ->
    list_sel_norepet l1 ->    
    list_sel_norepet l2.
Proof.
  induction 1; intros.
  - constructor.
  - inv H0. constructor; auto.
    intros. eapply DIS. eapply Permutation_in.
    symmetry. eauto. eauto.
  - inv H. inv NOREP. econstructor.
    + intros. inv H.
      apply selector_disjoint_sym.
      eapply DIS. constructor. auto.
      eapply DIS0; auto.
    + econstructor.
      -- intros. eapply DIS. apply in_cons. auto.
      -- auto.
  - auto.
Qed.

Lemma itosels_app: forall l1 l2,
    itosels (l1 ++ l2) = itosels l1 ++ itosels l2.
Proof.
  intros. unfold itosels.
  rewrite map_app. rewrite filter_app. rewrite map_app. auto.
Qed.

Lemma in_itosels: forall sel l,
    In sel (itosels l) ->
    exists pc n, In (pc, Isel sel n) l.
Proof.
  intros. unfold itosels in H.
  eapply in_map_iff in H. destruct H. destruct x.
  - destruct H. eapply filter_In in H0. destruct H0. congruence.
  - destruct H. eapply filter_In in H0. destruct H0.
    eapply in_map_iff in H0. destruct H0 as ((pc & i) & A1 & A2).
    simpl in A1. subst. eauto.
  - destruct H. eapply filter_In in H0. destruct H0. congruence.
  - destruct H. eapply filter_In in H0. destruct H0. congruence.
Qed.

(* Adding an instruction to a graph which does not contain repeated
selctors. The new graph also does not contain repeated selctors as
long as the added instruction is not a selctor or its selector is
disjoint with all the selectors in the graph *)
Lemma add_instr_sel_norepet: forall g1 g2 instr n2 R
    (DISJOINT: forall sel1 n1 pc sel2 succ,
        instr = Isel sel1 n1 ->
        (st_code g1) ! pc = Some (Isel sel2 succ) ->
        selector_disjoint sel1 sel2)
    (ADD: add_instr instr g1 = Res n2 g2 R)
    (NOREP: list_sel_norepet (itosels (PTree.elements (st_code g1)))),
    list_sel_norepet (itosels (PTree.elements (st_code g2))).
Proof.
  intros. unfold add_instr in ADD.
  inv ADD. simpl in *.
  exploit PTree.elements_remove.
  instantiate (3 := (PTree.set (st_nextnode g1) instr (st_code g1))).
  eapply PTree.gss. intros (l1 & l2 & A1 & A2).
  erewrite PTree.elements_extensional with (n:= (st_code g1))in A2.
  2: { intros. rewrite PTree.grspec.
       destruct PTree.elt_eq. subst.
       destruct (st_wf g1 (st_nextnode g1)).
       unfold Plt in H. exfalso. eapply Pos.lt_irrefl. eauto.
       rewrite H. auto.
       rewrite PTree.gso; eauto. }
  rewrite A1. rewrite A2 in NOREP.
  rewrite itosels_app in *.
  eapply list_sel_norepet_app in NOREP. destruct NOREP as (B1 & B2 & B3).
  eapply list_sel_norepet_app.
  destruct instr.
  - repeat apply conj; auto.
  - repeat apply conj; auto.
    + unfold itosels.
      erewrite map_cons. simpl. econstructor.
      intros.
      exploit in_itosels. eauto. intros (pc & n1 & IN).
      eapply DISJOINT. eauto. 
      eapply PTree.elements_complete.
      rewrite A2. eapply in_app_iff. right. eauto.
      auto.
    + red. intros. inv H0; auto.
      simpl. exploit in_itosels. eauto.
      intros (pcx & nx & IN).
      eapply selector_disjoint_sym.
      eapply DISJOINT. eauto. eapply PTree.elements_complete.
      rewrite A2. eapply in_app. eauto.
  - repeat apply conj; auto.
  - repeat apply conj; auto.
Qed.    


(* Updating an instruction to a graph which does not contain repeated
selctors. The new graph also does not contain repeated selctors as
long as the added instruction is not a selctor or its selector is
disjoint with all the selectors in the graph *)
Lemma update_instr_sel_norepet: forall g1 g2 instr n2 R pc
    (DISJOINT: forall sel1 n1 pc sel2 succ,
        instr = Isel sel1 n1 ->
        (st_code g1) ! pc = Some (Isel sel2 succ) ->
        selector_disjoint sel1 sel2)                                  
    (UPDATE: update_instr pc instr g1 = Res n2 g2 R)
    (NOREP: list_sel_norepet (itosels (PTree.elements (st_code g1)))),
    list_sel_norepet (itosels (PTree.elements (st_code g2))).
Proof.  
  intros. unfold update_instr in UPDATE.
  destruct plt in UPDATE; try congruence.
  destruct (check_empty_node g1 pc) eqn: EMP; try congruence.
  inv UPDATE. simpl in *.
  exploit PTree.elements_remove.
  instantiate (3 := (PTree.set pc instr (st_code g1))).
  eapply PTree.gss. intros (l1 & l2 & A1 & A2).
  erewrite PTree.elements_extensional with (n:= (st_code g1))in A2.
  2: { intros. rewrite PTree.grspec.
       destruct PTree.elt_eq. subst. auto.
       rewrite PTree.gso; eauto. }
  rewrite A1. rewrite A2 in NOREP.
  rewrite itosels_app in *.
  eapply list_sel_norepet_app in NOREP. destruct NOREP as (B1 & B2 & B3).
  eapply list_sel_norepet_app.
  (* rest of this proof is the same as that in add_instr_sel_norepet *)
  destruct instr.
  - repeat apply conj; auto.
  - repeat apply conj; auto.
    + unfold itosels.
      erewrite map_cons. simpl. econstructor.
      intros.
      exploit in_itosels. eauto. intros (pc1 & n1 & IN).
      eapply DISJOINT. eauto. 
      eapply PTree.elements_complete.
      rewrite A2. eapply in_app_iff. right. eauto.
      auto.
    + red. intros. inv H0; auto.
      simpl. exploit in_itosels. eauto.
      intros (pcx & nx & IN).
      eapply selector_disjoint_sym.
      eapply DISJOINT. eauto. eapply PTree.elements_complete.
      rewrite A2. eapply in_app. eauto.
  - repeat apply conj; auto.
  - repeat apply conj; auto.
Qed.


(* The selectors generated by RustIRcfg.transl_stmt are norepet *)
Lemma transl_stmt_sel_norepet: forall body g1 g2 R nret n1 n2 cont brk sel1
    (NOREP: list_sel_norepet (itosels (PTree.elements (st_code g1))))
    (TR: RustIRcfg.transl_stmt nret body sel1 n1 cont brk g1 = Res n2 g2 R)
    (DISJOINT: forall pc sel2 succ, (st_code g1) ! pc = Some (Isel sel2 succ) ->
                               selector_disjoint sel1 sel2),
    list_sel_norepet (itosels (PTree.elements (st_code g2))).
Proof.
  Ltac solve_atomic_norepet DISJOINT :=
    eapply add_instr_sel_norepet; eauto;
    intros until succ; intros EQ; inv EQ; eapply DISJOINT; eauto.
  
  induction body; intros; simpl in *; try solve_atomic_norepet DISJOINT.    
  - inv TR. auto.
  - monadInv TR.
    exploit IHbody2; eauto.
    (* prove disjointness *)
    intros.
    eapply selector_disjoint_app_left. eauto.
    intros NOREP1.
    exploit IHbody1; eauto.
    (* prove disjointness *)
    intros.
    generalize INCR. intros. inv INCR3.
    destruct (INCL pc). 
    (* case1: pc in s but not in g1 *)
    + exploit transl_stmt_selectors_prefix. eapply EQ. eauto. eauto.
      intros (l1 & A). subst. rewrite <- app_assoc.
      eapply selector_disjoint_app2. econstructor. congruence.
    + eapply selector_disjoint_app_left. eapply DISJOINT.
      erewrite <- H0. eauto.
  - monadInv TR.
    eapply add_instr_sel_norepet with (instr := (Icond e x x0)).
    congruence. eauto.
    exploit IHbody1; eauto.
    (* prove disjointness *)
    intros.
    eapply selector_disjoint_app_left. eauto.
    intros NOREP1.
    exploit IHbody2; eauto.
    (* prove disjointness *)
    intros.
    generalize INCR. intros. inv INCR5.
    destruct (INCL pc). 
    (* case1: pc in s but not in g1 *)
    + exploit transl_stmt_selectors_prefix. eapply EQ. eauto. eauto.
      intros (l1 & A). subst. rewrite <- app_assoc.
      eapply selector_disjoint_app2. econstructor. congruence.
    + eapply selector_disjoint_app_left. eapply DISJOINT.
      erewrite <- H0. eauto.
  - monadInv TR.
    unfold reserve_instr in EQ. inv EQ. 
    exploit IHbody. 2: eapply EQ1. simpl. eauto.
    simpl. intros.
    eapply selector_disjoint_app_left. eauto.
    intros NOREP1.
    (* prove update_instr preserves norepet *)
    eapply update_instr_sel_norepet with (instr := Inop x0). congruence.
    eauto. auto.
  - destruct brk.
    inv TR. auto. inv TR.
  - destruct cont. 
    inv TR. auto. inv TR.
Qed.
    
(* key proof: transl_on_instrs is unchanged during the
permutation. Prove by induciton on the permutation *)
Lemma transl_on_instrs_permutation_same: forall l1 l2 (PERM: Permutation l1 l2) body body1    
    (TR: fold_left transl l1 (OK body) = OK body1)    
    (NOREP: list_sel_norepet (itosels l1)),
    fold_left transl l2 (OK body) = OK body1.
Proof.
  induction 1; intros.
  - simpl in *. inv TR. auto.
  - simpl in *. destruct x. simpl in *.
    destruct (transl_on_instr body p i) eqn: A.
    2:{ erewrite transl_on_instrs_error in TR. inv TR. }
    eapply IHPERM; eauto.
    (* itosels properties *)
    replace ((p,i)::l) with ([(p,i)] ++ l) in NOREP by auto.
    rewrite itosels_app in NOREP. eapply list_sel_norepet_app in NOREP.
    intuition.
  (** IMPORTANT: swap case *)
  - destruct y. destruct x.
    simpl in *.
    destruct (transl_on_instr body p i) eqn: A1.
    2: { simpl in TR. erewrite transl_on_instrs_error in TR. inv TR. }
    simpl in TR.
    destruct (transl_on_instr s p0 i0) eqn: A2.
    2: { simpl in TR. erewrite transl_on_instrs_error in TR. inv TR. }
    (* case analysis of i *)
    destruct i; simpl in *.
    (* Inop *)
    + inv A1.
      assert (B1: transl (transl_on_instr s p0 i0) (p, Inop n) = OK s0).
      { destruct i0; simpl in *; inv A2; auto.
        destruct (select_stmt s s1); try congruence.
        destruct transl_stmt eqn: TR1 in H0; try congruence.
        rewrite TR1. simpl. rewrite H0. auto.
        (* Icond *)
        Errors.monadInv H0. rewrite EQ. simpl. auto. }
      rewrite B1. auto.
    (* i is Isel *)
    + destruct (select_stmt body s1) eqn: S1; try congruence.
      destruct transl_stmt eqn: TR1 in A1; try congruence.
      (* case analysis of i0 *)
      destruct i0; simpl in *.
      (* i0 is Inop *)
      * inv A2. rewrite S1. rewrite TR1. simpl. rewrite A1. auto.
      (* i0 is Isel *)
      * assert (DIS: selector_disjoint s1 s4).
        { unfold itosels in NOREP. simpl in NOREP. inv NOREP.
          inv NOREP0. eapply DIS. econstructor. auto. }
        destruct (select_stmt s s4) eqn: S2; try congruence.
        destruct transl_stmt eqn: S3 in A2; try congruence.
        exploit set_stmt_disjoint_select_inv; eauto.
        (* prove disjointness of s3 and s1 *)
        eapply selector_disjoint_sym. auto.
        intros C1.        
        rewrite C1. rewrite S3. simpl.
        (* set_stmt to body *)
        unfold transl at 2. simpl.
        unfold transl_on. simpl.
        exploit select_stmt_then_set. eapply C1. instantiate (1 := s6). instantiate (1 := p0).
        intros (body' & C2).
        erewrite C2. simpl.
        (* select disjoint statement in body' *)
        exploit set_stmt_disjoint_select. eapply S1. eapply C2.
        (* prove disjointness between s1 and s3 *)
        auto.
        intros C3. rewrite C3.
        rewrite TR1. simpl.
        erewrite set_stmt_disjoint_reorder; eauto.
      (* i0 is Icond *)
      * Errors.monadInv A2. rewrite EQ. simpl.
        rewrite S1. rewrite TR1. simpl. rewrite A1. auto.
      * inv A2. rewrite S1. rewrite TR1. simpl. rewrite A1. auto.
    (* Icond *)
    + Errors.monadInv A1.
      assert (B1: transl (transl_on_instr s p0 i0) (p, Icond e n n0) = OK s0).
      { destruct i0; simpl in *; try rewrite EQ; inv A2; auto.
        destruct (select_stmt s s1); try congruence.
        destruct transl_stmt eqn: TR1 in H0; try congruence.
        rewrite TR1. simpl. rewrite H0. simpl. rewrite EQ. auto.
        (* Icond *)
        Errors.monadInv H0. rewrite EQ0. simpl. rewrite EQ. auto. }
      rewrite B1. auto.
    (* Iend *)
    + inv A1.
      assert (B1: transl (transl_on_instr s p0 i0) (p, Iend) = OK s0).
      { destruct i0; simpl in *; inv A2; auto.
        destruct (select_stmt s s1); try congruence.
        destruct transl_stmt eqn: TR1 in H0; try congruence.
        rewrite TR1. simpl. rewrite H0. auto.
        (* Icond *)
        Errors.monadInv H0. rewrite EQ. simpl. auto. }
      rewrite B1. auto.      
  - eapply IHPERM2. eapply IHPERM1. auto.
    auto.
    (* sel_norepet under permutation *)
    eapply Permutation_itosels in PERM1.
    eapply list_sel_norepet_permutation; eauto.
Qed.

(* If the translation on the graph succeeds in a larger graph (i.e.,
g2) then the translation also succeed in a smaller graph (i.e., g1) *)
Lemma transl_on_cfg_state_incr: forall body1 body2 g1 g2,
    transl_on_cfg body1 (st_code g2) = OK body2 ->
    state_incr g1 g2 ->
    (* ensure that g1 is also norepet so that the order of the
    instructions does not matter *)
    list_sel_norepet (itosels (PTree.elements (st_code g2))) ->
    exists body3, transl_on_cfg body1 (st_code g1) = OK body3.
Proof.
  intros until g2. intros TRANSL INCR NOREP.
  unfold transl_on_cfg in *.
  rewrite PTree.fold_spec in *.
  inv INCR.
  destruct PERMU as (l & PERM).
  exploit transl_on_instrs_permutation_same; eauto.
  intros TRANSL1.
  rewrite fold_left_app in TRANSL1.
  destruct (fold_left transl (PTree.elements (st_code g1))
              (OK body1)) eqn: A.
  2: { rewrite transl_on_instrs_error in TRANSL1. inv TRANSL1. }
  fold transl.
  erewrite A. eauto.
Qed.
  
(* Two statements are equal except for their children statements. This
predicate is designed only for relating the condition expressions in
Sifthenelse *)
Definition stmt_memb_eq (s1 s2: statement) : Prop :=
  match s1, s2 with
  | Ssequence _ _, Ssequence _ _ => True
  | Sifthenelse e1 _ _, Sifthenelse e2 _ _ => e1 = e2
  | Sloop _, Sloop _ => True
  | _, _ => s1 = s2
  end.

Lemma stmt_memb_eq_refl: forall s,
    stmt_memb_eq s s.
Proof.
  destruct s; red; auto.
Qed.

Lemma stmt_memb_eq_trans: forall s1 s2 s3,
    stmt_memb_eq s1 s2 ->
    stmt_memb_eq s2 s3 ->
    stmt_memb_eq s1 s3.
Proof.
  intros.
  destruct s1; destruct s2; simpl in *; try congruence; destruct s3; try congruence; simpl; auto.
Qed.


(* Adding disjoint selectors in the graph does not change the section
of the statement disjointed with the inserted selectors *)
Lemma transl_on_cfg_state_incr_unchanged: forall body body1 body2 g1 g2 sel1 s
    (TR1: transl_on_cfg body (st_code g1) = OK body1)
    (TR2: transl_on_cfg body (st_code g2) = OK body2)
    (INCR: state_incr g1 g2)
    (SEL: select_stmt body1 sel1 = Some s)
    (DISJOINT: forall pc sel2 n, (st_code g1) ! pc = None ->
                            (st_code g2) ! pc = Some (Isel sel2 n) ->
                            selector_disjoint sel1 sel2)
    (NOREP: list_sel_norepet (itosels (PTree.elements (st_code g2)))),
    select_stmt body2 sel1 = Some s.    
Proof.
  intros.
  unfold transl_on_cfg in *.
  rewrite PTree.fold_spec in *.
  inv INCR.
  destruct PERMU as (l & PERM).
  (* translate on g2 unchanged under the permutation *)
  exploit transl_on_instrs_permutation_same; eauto.
  intros TR3.
  rewrite fold_left_app in TR3.
  unfold transl in TR3 at 2. rewrite TR1 in TR3.
  (* use transl_on_instrs_unchanged *)
  eapply transl_on_instrs_unchanged; eauto.
  (* prove l and sel1 is disjoint *)
  intros.
  (* (pc, Isel sel0 n) is in g2 *)
  exploit Permutation_in. symmetry. eauto. eapply in_app. right. eauto.
  intros IN1.
  (* prove (pc, Isel sel0 n) is not in g1 *)
  assert (IN2: ~ In pc (map fst (PTree.elements (st_code g1)))).
  { intro.
    erewrite in_map_iff in H0. destruct H0 as ((pc1 & i) & B1 & B2).
    simpl in B1. inv B1.
    (* It is a contradiction to norepet of the key *)
    eapply Permutation_map with (f:=fst) in PERM.
    exploit permutation_norepet. eauto.
    eapply PTree.elements_keys_norepet. intros.
    erewrite map_app in H0.
    erewrite list_norepet_app in H0. destruct H0 as (A1 & A2 & A3).
    eapply A3. eapply in_map_iff. eauto.
    eapply in_map_iff. eauto. auto. }
  assert (forall i, (st_code g1) ! pc <> Some i).
  { intros. intro.    
    eapply IN2. eapply PTree.elements_correct in H0.
    eapply in_map_iff. exists (pc,i). eauto. }    
  eapply DISJOINT with (pc:= pc).
  destruct ((st_code g1) ! pc) eqn: C; try congruence.
  eapply PTree.elements_complete. eauto.
Qed.

Lemma match_stmt_state_incr: forall s ts body g1 g2 pc succ cont brk nret,
    match_stmt body (st_code g1) s ts pc succ cont brk nret ->
    state_incr g1 g2 ->
    match_stmt body (st_code g2) s ts pc succ cont brk nret.
Proof.
  induction s; intros until nret; intros MSTMT INCR; inv MSTMT; try econstructor; eauto.
  all : inv INCR; destruct (INCL pc); try congruence;
    erewrite H1; auto.
Qed.


(* If the graph with more nodes does not contain repeated selectors,
so do its subset *)
Lemma state_incr_norepet: forall g1 g2,
    list_sel_norepet (itosels (PTree.elements (st_code g2))) ->
    state_incr g1 g2 ->
    list_sel_norepet (itosels (PTree.elements (st_code g1))).
Proof.
  intros. inv H0. destruct PERMU as (l & PERM).
  exploit Permutation_itosels. eauto. intros PERM1.
  generalize (list_sel_norepet_permutation _ _ PERM1 H).
  intros NOREP.
  erewrite itosels_app in NOREP.    
  eapply list_sel_norepet_app in NOREP. intuition.
Qed. 
 
(* add an instruction witch is not a selctor does not change the
result of transl_on_cfg *)
Lemma transl_on_cfg_add_non_sel_instr_unchanged_inv: forall instr g1 g2 body1 body2 n R,
    transl_on_cfg body1 (st_code g2) = OK body2 ->
    add_instr instr g1 = Res n g2 R ->
    (forall sel n2, instr <> Isel sel n2) ->
    transl_on_cfg body1 (st_code g1) = OK body2.
Proof.
  intros until R; intros TRANSL ADD NSEL.
  unfold transl_on_cfg in *.
  rewrite PTree.fold_spec in *.
  unfold add_instr in ADD. inv ADD. simpl in *.  
  exploit PTree.elements_remove.
  instantiate (3 := (PTree.set (st_nextnode g1) instr (st_code g1))).
  eapply PTree.gss. intros (l1 & l2 & A1 & A2).
  erewrite PTree.elements_extensional with (n:= (st_code g1))in A2.
  2: { intros. rewrite PTree.grspec.
       destruct PTree.elt_eq. subst.
       destruct (st_wf g1 (st_nextnode g1)).
       unfold Plt in H. exfalso. eapply Pos.lt_irrefl. eauto.
       rewrite H. auto.
       rewrite PTree.gso; eauto. }
  rewrite A2.
  rewrite A1 in TRANSL.
  fold transl. fold transl in TRANSL.
  rewrite fold_left_app in *.
  destruct (fold_left transl l1 (OK body1)) eqn: A3.
  2: { rewrite transl_on_instrs_error in TRANSL. inv TRANSL. }
  simpl in TRANSL.
  destruct (transl_on_instr s (st_nextnode g1) instr) eqn: B.
  2: { rewrite transl_on_instrs_error in TRANSL. inv TRANSL. }
  destruct instr; simpl in *; inv B; auto.
  generalize (NSEL s1 n). congruence.
  (* Icond *)
  Errors.monadInv H0. simpl. eauto.
Qed.     
  
(* update an instruction witch is not a selctor does not change the
result of transl_on_cfg *)
Lemma transl_on_cfg_update_non_sel_instr_unchanged_inv: forall instr g1 g2 body1 body2 n R pc,
    transl_on_cfg body1 (st_code g2) = OK body2 ->
    update_instr pc instr g1 = Res n g2 R ->
    (forall sel n2, instr <> Isel sel n2) ->
    transl_on_cfg body1 (st_code g1) = OK body2.
Proof.
  intros until pc; intros TRANSL ADD NSEL.
  unfold transl_on_cfg in *.
  rewrite PTree.fold_spec in *.
  unfold update_instr in ADD. destruct plt in ADD; try congruence.
  destruct (check_empty_node g1 pc) eqn: C in ADD; try congruence.
  inv ADD. simpl in *.
  exploit PTree.elements_remove.
  instantiate (3 := (PTree.set pc instr (st_code g1))).
  eapply PTree.gss. intros (l1 & l2 & A1 & A2).
  erewrite PTree.elements_extensional with (n:= (st_code g1))in A2.
  2: { intros. rewrite PTree.grspec.
       destruct PTree.elt_eq. subst. auto.
       rewrite PTree.gso; eauto. }
  rewrite A2.
  rewrite A1 in TRANSL.
  fold transl. fold transl in TRANSL.
  rewrite fold_left_app in *.
  destruct (fold_left transl l1 (OK body1)) eqn: A3.
  2: { rewrite transl_on_instrs_error in TRANSL. inv TRANSL. }
  simpl in TRANSL.
  destruct (transl_on_instr s pc instr) eqn: B.
  2: { rewrite transl_on_instrs_error in TRANSL. inv TRANSL. }
  destruct instr; simpl in *; inv B; auto.
  generalize (NSEL s1 n). congruence.
  (* Icond *)
  Errors.monadInv H0. simpl. eauto.  
Qed.
  

(* For a selector sel1, set a selector sel2 witch is not the
   prefix of sel1, then the selection of sel1 is stmt_memb_eq to
   the original result *)
Lemma update_stmt_not_prefix_memb_eq: forall sel1 sel2 body1 body2 s s1
  (NOTPRE: forall l, sel2 ++ l <> sel1)
  (SET: update_stmt  body1 sel2 s = Some body2)
  (SEL: select_stmt body1 sel1 = Some s1),
  exists s2, select_stmt body2 sel1 = Some s2
              /\ stmt_memb_eq s1 s2.
Proof.
  induction sel1; intros.
  - rewrite select_stmt_nil in SEL. inv SEL.
    exists body2. rewrite select_stmt_nil.
    split; auto.
    destruct (update_stmt s1 sel2 s) eqn: A; try congruence.
    inv SET.    
    destruct sel2. generalize (NOTPRE []). simpl. congruence.
    destruct s0; destruct s1; simpl in A; try congruence.
    + destruct (update_stmt s1_1 sel2 s) eqn: B; try congruence.
      inv A. simpl. auto.
    + destruct (update_stmt s1_2 sel2 s) eqn: B; try congruence.
      inv A. simpl. auto.
    + destruct (update_stmt s1_1 sel2 s) eqn: B; try congruence.
      inv A. simpl. auto.
    + destruct (update_stmt s1_2 sel2 s) eqn: B; try congruence.
      inv A. simpl. auto.
    + destruct (update_stmt s1 sel2 s) eqn: B; try congruence.
      inv A. simpl. auto.
  - destruct (update_stmt body1 sel2 s) eqn: A. inv SET.
    2: { inv SET. }        
    destruct a; destruct body1; simpl in *; try congruence.        
    + destruct sel2; simpl in A; try congruence.
      (* contradition: sel2 must not be empty *)
      * inv A. exfalso. eapply NOTPRE. simpl. eauto.
      * destruct s0; simpl in A; try congruence.
        -- destruct (update_stmt body1_1 sel2 s) eqn: B; try congruence.
           inv A. simpl. eapply IHsel1; eauto.
           intro. intro. subst. eapply NOTPRE. simpl. f_equal.
        -- destruct (update_stmt body1_2 sel2 s) eqn: B; try congruence.
           inv A. simpl. exists s1. split; auto. apply stmt_memb_eq_refl.
    (* mostly the same as above case *)
    + destruct sel2; simpl in A; try congruence.
      (* contradition: sel2 must not be empty *)
      * inv A. exfalso. eapply NOTPRE. simpl. eauto.
      * destruct s0; simpl in A; try congruence.
        -- destruct (update_stmt body1_1 sel2 s) eqn: B; try congruence.
           inv A. simpl. exists s1. split; auto. apply stmt_memb_eq_refl. 
        -- destruct (update_stmt body1_2 sel2 s) eqn: B; try congruence.
           inv A. simpl. eapply IHsel1; eauto.
           intro. intro. subst. eapply NOTPRE. simpl. f_equal.
    + destruct sel2; simpl in A; try congruence.
      (* contradition: sel2 must not be empty *)
      * inv A. exfalso. eapply NOTPRE. simpl. eauto.
      * destruct s0; simpl in A; try congruence.
        -- destruct (update_stmt body1_1 sel2 s) eqn: B; try congruence.
           inv A. simpl. eapply IHsel1; eauto.
           intro. intro. subst. eapply NOTPRE. simpl. f_equal.
        -- destruct (update_stmt body1_2 sel2 s) eqn: B; try congruence.
           inv A. simpl. exists s1. split; auto. apply stmt_memb_eq_refl.
    + destruct sel2; simpl in A; try congruence.
      (* contradition: sel2 must not be empty *)
      * inv A. exfalso. eapply NOTPRE. simpl. eauto.
      * destruct s0; simpl in A; try congruence.
        -- destruct (update_stmt body1_1 sel2 s) eqn: B; try congruence.
           inv A. simpl. exists s1. split; auto. apply stmt_memb_eq_refl. 
        -- destruct (update_stmt body1_2 sel2 s) eqn: B; try congruence.
           inv A. simpl. eapply IHsel1; eauto.
           intro. intro. subst. eapply NOTPRE. simpl. f_equal.
    + destruct sel2; simpl in A; try congruence.
      (* contradition: sel2 must not be empty *)
      * inv A. exfalso. eapply NOTPRE. simpl. eauto.
      * destruct s0; simpl in A; try congruence.
        -- destruct (update_stmt body1 sel2 s) eqn: B; try congruence.
           inv A. simpl. eapply IHsel1; eauto.
           intro. intro. subst. eapply NOTPRE. simpl. f_equal.
Qed.    

(* For a selector sel1, set a selector sel2 witch is not the
   prefix of sel1, then the selection of sel1 is stmt_memb_eq to
   the original result *)
Lemma set_stmt_not_prefix_memb_eq: forall sel1 sel2 body1 body2 s s1 pc
  (NOTPRE: forall l, sel2 ++ l <> sel1)
  (SET: set_stmt pc body1 sel2 s = OK body2)
  (SEL: select_stmt body1 sel1 = Some s1),
  exists s2, select_stmt body2 sel1 = Some s2
              /\ stmt_memb_eq s1 s2.
Proof.
  intros.
  unfold set_stmt in SET. destruct (update_stmt body1 sel2 s) eqn: A; try congruence.
  inv SET.
  eapply update_stmt_not_prefix_memb_eq; eauto.
Qed.

(* Auxilary function for transl_on_cfg_unchanged_statement_member,
proved by induction on instrs *)
Lemma transl_on_instrs_unchanged_statement_member: forall instrs body1 body2 sel s
  (TR: fold_left transl instrs (OK body1) = OK body2)
  (SEL: select_stmt body1 sel = Some s)
  (NOTIN: forall pc sel1 l n1, In (pc, Isel sel1 n1) instrs ->
                          sel1 ++ l <> sel),
  exists s', select_stmt body2 sel = Some s'
        /\ stmt_memb_eq s s'.
Proof.
  induction instrs; intros; simpl in *.
  - inv TR. exists s. split; auto.
    destruct s; red; auto.
  - destruct (transl_on_instr body1 (fst a) (snd a)) eqn: A.
    2: {  erewrite transl_on_instrs_error in TR. inv TR. }
    destruct a. simpl in A.
    destruct i; simpl in *. 
    + inv A. eapply IHinstrs; eauto.
    + destruct (select_stmt body1 s1) eqn: B.
      2: inv A.
      destruct transl_stmt eqn: TR1 in A; try congruence.
      assert (NOTPRE: forall l, s1 ++ l <> sel).
      { intros. eapply NOTIN; eauto. }
      exploit set_stmt_not_prefix_memb_eq; eauto.
      intros (s4 &  SEL2 & SEQ).          
      exploit IHinstrs. eauto. eapply SEL2.
      intros. eapply NOTIN. eauto.
      intros (s' & SEL3 & SEQ1). exists s'.
      split; auto.
      eapply stmt_memb_eq_trans; eauto.
    + Errors.monadInv A. eapply IHinstrs; eauto.
    + inv A. eapply IHinstrs; eauto.
Qed.

      
(* If the selector and its parent are not in the graph, then
   translating the AST based on this graph does not change the member
    (e.g., conditional expression in Sifthenelse) of the element in
    this selector *)
Lemma transl_on_cfg_unchanged_statement_member: forall body1 body2 g sel s
  (TR: transl_on_cfg body1 (st_code g) = OK body2)
  (SEL: select_stmt body1 sel = Some s)
  (NOTIN: forall pc sel1 l n1, (st_code g) ! pc = Some (Isel sel1 n1) ->
                          sel1 ++ l <> sel),
  exists s', select_stmt body2 sel = Some s'
        /\ stmt_memb_eq s s'.
Proof.
  intros. unfold transl_on_cfg in TR.
  rewrite PTree.fold_spec in TR.
  eapply transl_on_instrs_unchanged_statement_member; eauto.
  intros. eapply NOTIN.
  eapply PTree.elements_complete. eauto.
Qed.  
  
(** Key proof of transl_on_cfg_meet_spec  *)
Lemma transl_on_cfg_charact: forall s body1 body2 n succ cont brk nret sel g g' R
  (* similar to transl_stmt_charact *)
  (TRSTMT: RustIRcfg.transl_stmt nret s sel succ cont brk g = Res n g' R)
  (SEL: select_stmt body1 sel = Some s)
  (* transl_on the updated cfg (st_code g') *)
  (TRANSL: transl_on_cfg body1 (st_code g') = OK body2)
  (DISJOINT: forall pc sel1 n, (st_code g) ! pc = Some (Isel sel1 n) ->
                          selector_disjoint sel sel1)
  (* norepet of g' (in the top level theorem use
  transl_stmt_sel_norepet to prove this premise) *)
  (NOREP: list_sel_norepet (itosels (PTree.elements (st_code g')))),
  (* list_norepet_app *)
  exists ts,
    select_stmt body2 sel = Some ts
    /\ match_stmt body1 (st_code g') s ts n succ cont brk nret.
Proof.
  induction s; intros; simpl in TRSTMT.

  (* atomic statement *)
  2-9: exploit add_instr_charact; eauto;
  intros (ts & A1 & A2 & A3);
  exists ts; split; auto;
  econstructor; eauto.
  
  - inv TRSTMT.        
    exists Sskip. split.
    eapply transl_on_cfg_unchanged; eauto.
    econstructor.
  (* Ssequence *)
  - monadInv TRSTMT.
    assert (NOREP2: list_sel_norepet (itosels (PTree.elements (st_code g')))).
    { eapply state_incr_norepet; eauto. }
    assert (NOREP1: list_sel_norepet (itosels (PTree.elements (st_code s)))).
    { eapply state_incr_norepet; eauto. }    
    exploit IHs1; eauto. eapply select_stmt_app. eauto. simpl. 
    eapply select_stmt_nil.
    (* prove disjointness: the new selectors in s not in g must be (sel++[Selseqleft]++l)) *)
    intros. generalize INCR as A. intros. inv A.
    generalize (INCL pc). intros [B1|B2].
    exploit transl_stmt_selectors_prefix. eapply EQ. eauto. eauto.
    intros (l & B3). subst.
    eapply selector_disjoint_app1.
    eapply selector_disjoint_app2. econstructor. congruence.
    eapply selector_disjoint_sym.
    eapply selector_disjoint_app1. eapply selector_disjoint_sym.
    eapply DISJOINT; eauto. erewrite <- B2. eauto.
    intros (ts1 & SEL1 & MSTMT1).
    (* use IHs2 *)
    (* first prove that transl_on_cfg s also success *)
    exploit transl_on_cfg_state_incr. eapply TRANSL. eapply INCR1. auto.
    intros (body3 & T1).
    exploit IHs2. eauto. eapply select_stmt_app. eauto. simpl. 
    eapply select_stmt_nil.
    eauto.    
    (* prove disjointness *)
    intros.
    eapply selector_disjoint_sym.
    eapply selector_disjoint_app1. eapply selector_disjoint_sym.
    eapply DISJOINT; eauto. auto.
    intros (ts2 & SEL2 & MSTMT2).
    (* use SEL2 prove that the selection in body2 return the same result *)
    assert (SEL3: select_stmt body2 (sel++[Selseqright]) = Some ts2).
    { eapply transl_on_cfg_state_incr_unchanged.
      eapply T1. eauto. eauto. eauto.
      (* prove disjointness *)
      intros.
      exploit transl_stmt_selectors_prefix. eapply EQ1. eauto. eauto.
      intros (l & A). subst.
      rewrite <- app_assoc. eapply selector_disjoint_app2. econstructor.
      congruence. auto. }
    exploit select_stmt_app_inv. eapply SEL1. intros (b1 & S1 & S2).
    exploit select_stmt_app_inv. eapply SEL3. intros (b2 & S3 & S4).
    rewrite S1 in S3. inv S3. destruct b2; simpl in *; try congruence.
    erewrite select_stmt_nil in *. inv S2. inv S4.
    exists (Ssequence ts1 ts2). split; auto.
    econstructor; eauto.
    (* match_stmt_state_Incr *)
    eapply match_stmt_state_incr; eauto.
  (* Sifthenelse *)
  - monadInv TRSTMT.
    exploit add_instr_at; eauto. intros COND.
    assert (NOREP3: list_sel_norepet (itosels (PTree.elements (st_code s0)))).
    { eapply state_incr_norepet; eauto. }    
    assert (NOREP2: list_sel_norepet (itosels (PTree.elements (st_code s)))).
    { eapply state_incr_norepet; eauto. }
    assert (NOREP1: list_sel_norepet (itosels (PTree.elements (st_code g)))).
    { eapply state_incr_norepet; eauto. }
    (* prove that transl_on_cfg s0 also success (for TRANSL1, adding a
    non-sel instruction does not change the result of
    transl_on_cfg) *)
    assert (TRANSL1: transl_on_cfg body1 (st_code s0) = OK body2).
    { eapply transl_on_cfg_add_non_sel_instr_unchanged_inv. eapply TRANSL. eauto.
      congruence. }
    exploit transl_on_cfg_state_incr. eapply TRANSL1. eapply INCR1. auto.
    intros (body4 & TRANSL2).    
    exploit IHs1; eauto. eapply select_stmt_app. eauto. simpl. 
    eapply select_stmt_nil.
    (* prove disjointness *)
    intros. eapply selector_disjoint_app_left. eauto.
    intros (ts1 & SEL1 & MSTMT1).
    (* use IHs2 *)
    exploit IHs2. eauto. eapply select_stmt_app. eauto. simpl. 
    eapply select_stmt_nil.
    eauto.    
    (* prove disjointness *)
    intros. generalize INCR. intros. inv INCR5.
    destruct (INCL pc).
    exploit transl_stmt_selectors_prefix. eapply EQ. eauto. eauto.
    intros (l & A). subst. rewrite <- app_assoc. eapply selector_disjoint_app2.
    econstructor. congruence.
    eapply selector_disjoint_app_left.
    eapply DISJOINT. erewrite <- H0. eauto. auto.
    intros (ts2 & SEL2 & MSTMT2).
    (* selection of the then and else branches remain the same in body2 *)
    (* assert (SEL3: select_stmt body2 (sel++[Selifelse]) = Some ts2). *)
    (* { eapply transl_on_cfg_state_incr_unchanged. *)
    (*   eapply TRANSL1. eauto. eauto. eauto. *)
    (*   (* prove disjointness *) *)
    (*   intros. *)
    (*   unfold add_instr in EQ0. inv EQ0. simpl in *. *)
    (*   erewrite PTree.gsspec in H0. destruct peq in H0; try congruence. *)
    (*   auto. } *)
    assert (SEL4: select_stmt body2 (sel++[Selifthen]) = Some ts1).
    { (* eapply transl_on_cfg_state_incr_unchanged. *)
      (* eapply TRANSL1. eauto. eauto. *)
      eapply transl_on_cfg_state_incr_unchanged.
      eapply TRANSL2. eauto. auto. auto.
      (* prove disjointness *)
      intros. exploit transl_stmt_selectors_prefix. eapply EQ1.
      1-2: eauto. intros (l & A). subst.
      rewrite <- app_assoc.
      eapply selector_disjoint_app2. econstructor. congruence.
      auto.
      (* intros. *)
      (* unfold add_instr in EQ0. inv EQ0. simpl in *. *)
      (* erewrite PTree.gsspec in H0. destruct peq in H0; try congruence. *)
      (* auto.  *)
    }
    (* how to prove that the condition expression is unchanged?? *)
    
    (* All the selectors in s0 are not prefixes of sel *)
    assert (SELNOTIN: forall pc sel1 l n1,
               (st_code s0) ! pc = Some (Isel sel1 n1) ->
               sel1 ++ l <> sel).
    { intros. intro.
      generalize INCR1. intros. inv INCR5.
      edestruct (INCL pc).
      (* sel1 not in s but in s0: impossible because sel1 must be longer then itself *)
      - exploit transl_stmt_selectors_prefix. eapply EQ1. eauto. eauto.
        intros (l1 & A1). rewrite <- !app_assoc in A1.
        erewrite (app_nil_end sel1) in A1 at 2.
        eapply app_inv_head in A1. destruct l; inv A1.
      (* sel1 is in s *)
      - rewrite H in H0. symmetry in H0.
        generalize INCR. intros. inv INCR5.
        destruct (INCL0 pc).
        (* sel1 not in g but in s *)
        * exploit transl_stmt_selectors_prefix. eapply EQ. eauto. eauto.
          intros (l1 & A1). rewrite <- !app_assoc in A1.
          erewrite (app_nil_end sel1) in A1 at 2.
          eapply app_inv_head in A1. destruct l; inv A1.
        * erewrite H0 in H1. symmetry in H1.
          eapply DISJOINT in H1.
          eapply selector_disjoint_not_prefix. eauto. }          
    (* prove the conditional expr in sel of body2 is the same as in that of body1 *)
    exploit transl_on_cfg_unchanged_statement_member. eapply TRANSL1. eauto.
    auto. intros (s' & A1 & A2). destruct s'; simpl in A2; try congruence. subst.
    (* show that s'1 = ts1 and s'2 = ts2 *)
    exploit select_stmt_app_inv. eapply SEL2. intros (b1 & S1 & S2).
    exploit select_stmt_app_inv. eapply SEL4. intros (b2 & S3 & S4).
    rewrite S1 in S3. inv S3. destruct b2; simpl in *; try congruence.
    erewrite select_stmt_nil in *. inv S2. inv S4.
    rewrite A1 in S1. inv S1.
    exists (Sifthenelse e ts1 ts2). split; auto.
    econstructor; eauto.
    eapply match_stmt_state_incr; eauto.
    eapply match_stmt_state_incr; eauto.
    (* check_expr succeeds. Maybe we should lift it to a lemma? *)
    exploit add_instr_at. eauto. intros B1.
    exploit PTree.elements_remove. eauto. intros (l1 & l2 & B2 & B3).
    unfold transl_on_cfg in TRANSL. rewrite PTree.fold_spec in TRANSL.
    rewrite B2 in TRANSL. rewrite fold_left_app in TRANSL.
    fold transl in TRANSL.
    destruct (fold_left transl l1 (OK body1)) eqn: C1.
    2: { rewrite transl_on_instrs_error in TRANSL. inv TRANSL. }
    simpl in TRANSL.
    destruct ((do _ <- check_expr (get_an ae n) e; OK s3)) eqn: C2.
    2: { rewrite transl_on_instrs_error in TRANSL. inv TRANSL. }
    Errors.monadInv C2. auto. destruct x1. auto.
  (* Sloop *)
  - monadInv TRSTMT.
    exploit update_instr_at; eauto. intros LOOPSTART.
    assert (NOREP1: list_sel_norepet (itosels (PTree.elements (st_code s1)))).
    { eapply state_incr_norepet; eauto. }
    assert (TRANSL1: transl_on_cfg body1 (st_code s1) = OK body2).
    { eapply transl_on_cfg_update_non_sel_instr_unchanged_inv. eapply TRANSL. eauto.
      congruence. }    
    exploit IHs. eapply EQ1. eauto.
    eapply select_stmt_app. eauto. simpl. apply select_stmt_nil.
    eauto.
    (* disjointness *)
    intros. unfold reserve_instr in EQ. inv EQ. simpl in *.
    eapply selector_disjoint_app_left. eauto. auto.
    intros (ts & SEL1 & MSTMT).
    exploit select_stmt_app_inv. eapply SEL1. intros (b1 & S1 & S2).
    destruct b1; simpl in S2; try congruence.
    erewrite select_stmt_nil in S2. inv S2.
    exists (Sloop ts). split; auto.
    econstructor; eauto.
    eapply match_stmt_state_incr; eauto.
  (* Sbreak *)
  - destruct brk. 2: inv TRSTMT.
    inv TRSTMT.
    exists Sbreak. split.
    eapply transl_on_cfg_unchanged; eauto.
    econstructor.
  (* Continue *)
  - destruct cont. 2: inv TRSTMT.
    inv TRSTMT.
    exists Scontinue. split.
    eapply transl_on_cfg_unchanged; eauto.
    econstructor.
  (* Sreturn *)
  - exploit add_instr_charact; eauto;
    intros (ts & A1 & A2 & A3);
    exists ts; split; auto;
    econstructor; eauto.
Qed.
  
Lemma transl_on_cfg_meet_spec: forall f ts cfg entry
    (CFG: generate_cfg (fn_body f) = OK (entry, cfg))
    (TRANSL: transl_on_cfg (fn_body f) cfg = OK ts),
  exists nret, match_stmt (fn_body f) cfg (fn_body f) ts entry nret None None nret
          /\ cfg ! nret = Some Iend.
Proof.  
  intros. unfold generate_cfg in CFG.
  destruct (generate_cfg' (fn_body f) init_state) eqn: GENCFG; try congruence.
  unfold generate_cfg' in GENCFG.
  monadInv GENCFG. inv CFG.
  assert (NOTSEL: forall pc sel n, (st_code s0) ! pc <> Some (Isel sel n)).
  { intros. intro.
    unfold add_instr in EQ. inv EQ. simpl in *.
    (* if pc = x  *)
    erewrite PTree.gsspec in H. destruct peq in H; try congruence.
    erewrite PTree.gempty  in H. inv H. }   
  exploit transl_on_cfg_charact; eauto.
  eapply select_stmt_nil.
  (* disjointness *)
  intros. exfalso. eapply NOTSEL. eauto.
  (* list_sel_norepet *)
  eapply transl_stmt_sel_norepet. 2: eauto.
  generalize INCR. intros. inv INCR1.
  (* prove st_code s0 has only one elements *)
  unfold add_instr in EQ. inv EQ. simpl in *.
  unfold itosels. simpl. econstructor.
  (* disjointnesss *)
  intros. exfalso. eapply NOTSEL. eauto.  
  intros (ts1 & SEL & MSTMT). erewrite select_stmt_nil in SEL. inv SEL.
  exists x.
  split; auto.
  (* prove cfg!nret = Some Iend *)
  clear EQ0.
  eapply instr_at_incr. eauto.
  eapply add_instr_at. eauto.
Qed.

End SPEC.

End TRANSL.
