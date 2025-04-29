Require Import Coqlib.
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import CKLR.

(** * Semantic interface of languages *)

Structure language_interface :=
  mk_language_interface {
    query: Type;
    reply: Type;
    entry: query -> val;
  }.

Arguments entry {_}.

(** ** Basic interfaces *)

(** The null language interface defined below is used as the outgoing
  interface for closed semantics. *)

Definition li_null :=
  {|
    query := Empty_set;
    reply := Empty_set;
    entry q := match q with end;
  |}.

(** The whole-program interface is used as the incoming interface for
  closed semantics and characterizes whole-program execution: the
  query [tt : unit] invokes the [main()] function and the reply of
  type [int] gives the program's exit status. *)

Definition li_wp :=
  {|
    query := unit;
    reply := Integers.int;
    entry q := Vundef;
  |}.

(** * Calling conventions *)

(** ** Definition *)

Record callconv {li1 li2} :=
  mk_callconv {
    ccworld : Type;
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
        Genv.valid_for sk se1 <->
        Genv.valid_for sk se2;
  }.

Arguments callconv: clear implicits.
Declare Scope cc_scope.
Delimit Scope cc_scope with cc.
Bind Scope cc_scope with callconv.
Local Obligation Tactic := cbn; eauto.

(** ** Identity *)

Program Definition cc_id {li}: callconv li li :=
  {|
    ccworld := unit;
    match_senv w := eq;
    match_query w := eq;
    match_reply w := eq;
  |}.
Solve All Obligations with
  cbn; intros; subst; try split; auto.

Notation "1" := cc_id : cc_scope.

(** ** Composition *)

Program Definition cc_compose {li1 li2 li3} (cc12: callconv li1 li2) (cc23: callconv li2 li3) :=
  {|
    ccworld := Genv.symtbl * ccworld cc12 * ccworld cc23;
    match_senv '(se2, w12, w23) se1 se3 :=
      match_senv cc12 w12 se1 se2 /\
      match_senv cc23 w23 se2 se3;
    match_query '(se2, w12, w23) q1 q3 :=
      exists q2,
        match_query cc12 w12 q1 q2 /\
        match_query cc23 w23 q2 q3;
    match_reply '(se2, w12, w23) r1 r3 :=
      exists r2,
        match_reply cc12 w12 r1 r2 /\
        match_reply cc23 w23 r2 r3;
  |}.
Next Obligation.
  intros li1 li2 li3 cc12 cc23 [[se2 w12] w23] se1 se3 (H12 & H23) id.
  etransitivity; eauto using match_senv_public_preserved.
Qed.
Next Obligation.
  intros li1 li2 li3 cc12 cc23 [[se2 w12] w23] se1 se3 sk [Hse12 Hse23].
  split; intros H.
  erewrite <- match_senv_valid_for. 2: eauto.
  erewrite <- match_senv_valid_for; eauto.
  eapply match_senv_valid_for; eauto.
  eapply match_senv_valid_for; eauto.
Qed.

Infix "@" := cc_compose (at level 30, right associativity) : cc_scope.

(** * C-like languages *)

(** ** Interface *)

Record c_query :=
  cq {
    cq_vf: val;
    cq_sg: signature;
    cq_args: list val;
    cq_mem: mem;
  }.

Record c_reply :=
  cr {
    cr_retval: val;
    cr_mem: mem;
  }.

Canonical Structure li_c :=
  {|
    query := c_query;
    reply := c_reply;
    entry := cq_vf;
  |}.

(** ** Simulation conventions *)

(** Every CKLR defines as simulation convention for the C language
  interface in the following way. This is used in particular to show
  that key languages (Clight and RTL) self-simulate under any CKLR.
  In [some other place], we show that instances for the [inj] and
  [injp] CKLRs are equivalent to the corresponding simulation
  conventions used to verify the compiler. *)

Inductive cc_c_query R (w: world R): relation c_query :=
  | cc_c_query_intro vf1 vf2 sg vargs1 vargs2 m1 m2:
      Val.inject (mi R w) vf1 vf2 ->
      Val.inject_list (mi R w) vargs1 vargs2 ->
      match_mem R w m1 m2 ->
      vf1 <> Vundef ->
      cc_c_query R w (cq vf1 sg vargs1 m1) (cq vf2 sg vargs2 m2).

Inductive cc_c_reply R (w: world R): relation c_reply :=
  | cc_c_reply_intro vres1 vres2 m1' m2':
      Val.inject (mi R w) vres1 vres2 ->
      match_mem R w m1' m2' ->
      cc_c_reply R w (cr vres1 m1') (cr vres2 m2').

Program Definition cc_c (R: cklr): callconv li_c li_c :=
  {|
    ccworld := world R;
    match_senv := match_stbls R;
    match_query := cc_c_query R;
    match_reply := (<> cc_c_reply R)%klr;
  |}.
Next Obligation.
  intros. eapply match_stbls_proj in H. eapply Genv.mge_public; eauto.
Qed.
Next Obligation.
  intros. split.
  intros. erewrite <- Genv.valid_for_match; eauto.
  eapply match_stbls_proj in H. eauto.
  intros. 
  eapply Genv.valid_for_match; eauto.
  eapply match_stbls_proj in H. eauto.
Qed.
