Require Import Coqlib Errors Events Globalenvs Ctypes AST Memory Values Integers Asm.
Require Import LanguageInterface.
Require Import Smallstep SmallstepClosed.
Require Import ValueAnalysis.
Require Import MultiLibs CMulti AsmMulti.
Require Import InjectFootprint CA.
Require Import CallconvBig Injp CAnew Composition ThreadLinking.

Check Clight.semantics_receptive.
Check Asm.semantics_determinate.

Lemma Concur_sem_c_receptive : forall L,
    receptive L -> Closed.receptive (Concur_sem_c L).
Proof.
  intros L H. unfold receptive in H.
  generalize (H (Closed.symbolenv (Concur_sem_c L))). intro H1.
  inv H1. constructor; eauto.
  - intros. admit.
  - red. unfold single_events in sr_traces. intros. eapply sr_traces; eauto.
Admitted.


Lemma Concur_sem_asm_determinate : forall L,
    determinate L -> Closed.determinate (Concur_sem_asm L).
Admitted.
                                      
Theorem Flip_Globalsim : forall p tp,
    let OpenC := Clight.semantics1 p in let OpenA := Asm.semantics tp in
    GS.forward_simulation cc_compcert OpenC OpenA ->
    Closed.backward_simulation (Concur_sem_c OpenC) (Concur_sem_asm OpenA).
Proof.
  intros.
  eapply Closed.forward_to_backward_simulation.
  eapply Opensim_to_Globalsim; eauto.
  eapply Concur_sem_c_receptive. eapply Clight.semantics_receptive.
  eapply Concur_sem_asm_determinate. eapply Asm.semantics_determinate.
Qed.

