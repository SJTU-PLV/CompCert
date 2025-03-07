Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Errors.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Integers.
Require Import Smallstep.
Require Import SmallstepClosed.
Require Import Values Maps Memory AST.

Require Import Asm MultiLibs.
Require Import Conventions1.
  

Section MultiThread.
  
  Variable OpenS: Smallstep.semantics li_asm li_asm.

  Definition local_state := Smallstep.state OpenS.
  
  (* Definition thread_state : Type := local_state + regset. *)
  
  Inductive thread_state : Type :=
  |Local : forall (ls : local_state), thread_state
  |Initial : forall (rs : regset), thread_state
  |Returny : forall (ls: local_state) (rs: regset), thread_state
  |Returnj : forall (ls : local_state) (rs : regset) , thread_state
  |Final : forall (res: val), thread_state.

  Definition initial_se := Genv.symboltbl (skel OpenS).

  Definition OpenLTS := activate OpenS initial_se.

  Record state : Type := mk_gstate_asm
      {
        threads : NatMap.t (option thread_state);
        cur_tid : nat;
        next_tid : nat;
      }.

  Definition empty_threads : NatMap.t (option thread_state) := NatMap.init None.

  Definition initial_gstate (s : local_state) :=
    mk_gstate_asm (NatMap.set 1%nat (Some (Local s)) empty_threads) 1 2.
  
  Definition update_threads (s: state) (t: NatMap.t (option thread_state)) :=
    mk_gstate_asm t (cur_tid s) (next_tid s) .

  Definition update_thread (s: state) (tid : nat) (ls: thread_state) :=
    mk_gstate_asm (NatMap.set tid (Some ls) (threads s)) (cur_tid s) (next_tid s).

  Definition update_cur_thread (s: state) (ls : thread_state) := update_thread s (cur_tid s) ls.
  
  Definition get_thread (s: state) (tid: nat) :=
    NatMap.get tid (threads s).

  
  Definition get_cur_thread (s: state) := get_thread s (cur_tid s).
  
  Definition update_cur_tid (s: state) (tid : nat) :=
    mk_gstate_asm (threads s) tid (next_tid s).

  Definition update_next_tid (s: state) (tid: nat) :=
    mk_gstate_asm (threads s) (cur_tid s) tid.

  (* Fixpoint yield_strategy' (threads: NatMap.t (option thread_state)) (next: nat) :=
    match next with
    |O | S O => 1%nat (*next should be >= 2, this is meaningless*)
    |S n => (* n is the max valid thread id*)
       match NatMap.get n threads with
       | Some (Initial _) | Some (Return _ _) => n
       | _ => yield_strategy' threads n
       end
    end.
  
  Definition yield_strategy (s:state) := yield_strategy' (threads s) (next_tid s).
  *)
(*  Variable yield_strategy : state -> nat.
  Axiom yield_strategy_range : forall s, (1 < yield_strategy s < (next_tid s))%nat.
*)
  (** Here we need to update both the states of current thread and target thread *)
  (** 
      For target thread, the new local_state should come from [initial_state] or [after_external]
      For current thread, we should record the current regset and local_state as 
      [Return rs ls], therefore we can do [after_external ls (rs,m) ls'] using returned global memory
      [m] to get an updated local state ls'.

   *)
  Definition yield_state_asm (s: state) (ls_new: thread_state) (target: nat): state :=
    let s' := update_cur_tid s target in
    update_thread s' target ls_new.

  (* We add a new thread with its initial query without memory,
      we also update the running memory by adding a new list of positives *)
  Definition pthread_create_state (s: state) (regs: regset) (ls' : thread_state): state :=
    let ntid := (next_tid s) in let ctid := (cur_tid s) in
    let s' := update_next_tid s (S ntid) in
    let s'' := update_thread s' ntid (Initial regs) in
    update_thread s'' ctid ls'.
    
  Definition genvtype := Smallstep.genvtype OpenLTS.

  (*Variable initial_query : query li_asm.
  Variable final_reply : int -> reply li_asm -> Prop. *)


  (** maybe we should change Vnullptr*)
  Definition main_id := prog_main (skel OpenS).
  Definition initial_regset (pc : val) (sp: val):=
    (Pregmap.init Vundef) # PC <- pc
                          # RA <- Vnullptr
                          # RSP <- sp.
                                            
  Inductive initial_state : state -> Prop :=
  |initial_state_intro : forall ls main_b m0 rs0 m0' sb,
      Genv.find_symbol initial_se main_id = Some main_b ->
      Genv.init_mem (skel OpenS) = Some m0 ->
      Mem.alloc m0 0 0 = (m0', sb) ->
      rs0 = initial_regset (Vptr main_b Ptrofs.zero) (Vptr sb Ptrofs.zero)->
      (Smallstep.initial_state OpenLTS) (rs0,m0') ls ->
      initial_state (initial_gstate ls).

  (** Final state of Concurrent semantics *)
  Inductive final_state : state -> int -> Prop :=  
  |final_state_intro : forall ls i s rs m,
      cur_tid s = 1%nat ->
      get_cur_thread s = Some (Local ls) ->
      rs # PC = Vnullptr ->
      rs # RAX = Vint i ->
      (Smallstep.final_state OpenLTS) ls (rs,m)->
      final_state s i.

  
  (** * Operations about dealing with queries *)


  (* We should not define it like this, it's tautology
  Inductive query_is_yield_asm : query li_asm -> Prop :=
  |yield_intro : forall rs m q_c,
      query_is_yield qc ->
      cc_c_asm_mq (caw yield_sig rs m) qc (rs,m) ->
      query_is_yield (rs, m). *)

  (* Print yield_sig.
     yield_sig = {| sig_args := nil; sig_res := Tvoid; sig_cc := cc_default |}
     : signature
   *)


  Inductive query_is_yield_asm : query li_asm -> nat -> Prop :=
  |yield_intro_asm : forall rs m b next,
      Genv.find_symbol initial_se yield_id = Some b ->
      rs # PC = Vptr b Ptrofs.zero ->
      Mem.next_tid (Mem.support m) = next ->
      query_is_yield_asm (rs, m) next.

  Inductive query_is_pthread_create_asm : query li_asm -> reply li_asm -> query li_asm -> Prop :=
  |pthread_create_intro :
    forall m b_ptc b_the ofs_the b_start b_arg ofs_arg m1 rs rs_r rs_q start_id new_tid P1 m2 m3 sp P2 m4
      (FINDPTC: Genv.find_symbol initial_se pthread_create_id = Some b_ptc)
      (FINDSTR: Genv.find_symbol initial_se start_id = Some b_start)
      (INITSTR: exists s, Smallstep.initial_state OpenLTS (rs_q,m3) s)
      (RS_PC: rs # PC = Vptr b_ptc Ptrofs.zero)
      (RS_RDI : rs # RDI = Vptr b_the ofs_the)
      (RS_RSI : rs # RSI = Vptr b_start Ptrofs.zero)
      (RS_RDX : rs # RDX = Vptr b_arg ofs_arg)
      (RSR: rs_r = (rs # PC <- (rs RA) # RAX <- (Vint (Int.one))))
      (RSQ: rs_q = (rs # PC <- (Vptr b_start Ptrofs.zero) # RDI <- (Vptr b_arg ofs_arg) #RSP <- (Vptr sp Ptrofs.zero)))
      (* (RSQ_PC : rs_q # PC = Vptr b_start Ptrofs.zero)
      (RSQ_RDI : rs_q # RDI = Vptr b_arg ofs_arg)
      (RSQ_RSP: rs_q # RSP = Vptr sp Ptrofs.zero) *)
      (** We may need more requirements of rs' here *)
      (MEM_CREATE: Mem.thread_create m = (m1, new_tid))
      (MEM_YIELD: Mem.yield m1 new_tid P1 = m2)
      (MEM_ALLOCSP: Mem.alloc m2 0 0 = (m3, sp))
      (MEM_YB: Mem.yield m3 (Mem.tid (Mem.support m)) P2 = m4),
      query_is_pthread_create_asm (rs,m) (rs_r,m4) (rs_q, m3).
  
  Inductive query_is_pthread_join_asm: query li_asm -> nat -> val -> Prop :=
  |pthread_join_intro_asm: forall rs m b_ptj i v_vptr ofs_vptr
      (FINDPTJ: Genv.find_symbol initial_se pthread_join_id = Some b_ptj)
      (RS_PC: rs # PC = Vptr b_ptj Ptrofs.zero)
      (RS_RDI: rs # RDI = Vint i)
      (RS_RSI: rs # RSI = Vptr v_vptr ofs_vptr),
      query_is_pthread_join_asm (rs, m) (int_to_nat i) (Vptr v_vptr ofs_vptr).
  
  Theorem yield_loc :
    loc_arguments yield_sig = nil.
  Proof.
    simpl.  simpl. unfold yield_sig. unfold loc_arguments.
    replace Archi.ptr64 with true by reflexivity.
    rewrite not_win. simpl. reflexivity.
  Qed.

  Inductive switch_out : state -> state -> nat -> mem -> Prop :=
  |switch_out_yield : forall s s' ls rs_q m_q target p gmem'
      (GET_C: get_cur_thread s = Some (Local ls))
      (AT_E: Smallstep.at_external OpenLTS ls (rs_q,m_q))
      (Q_YIE: query_is_yield_asm (rs_q,m_q) (next_tid s))
      (MEM_YIELD: Mem.yield m_q target p = gmem')
      (SET_C: update_cur_thread s (Returny ls rs_q) = s'),
      switch_out s s' target gmem'
  |switch_out_join : forall s s' ls rs_q m_q wait vptr target p gmem'
      (GET_C: get_cur_thread s = Some (Local ls))
      (AT_E: Smallstep.at_external OpenLTS ls (rs_q,m_q))
      (Q_JOIN: query_is_pthread_join_asm (rs_q,m_q) wait vptr)
      (MEM_YIELD: Mem.yield m_q target p = gmem')
      (SET_C: update_cur_thread s (Returnj ls rs_q) = s'),
      switch_out s s' target gmem'
  |switch_out_final : forall s s' ls res (rs_r : regset) gmem target p gmem'
      (SUB_THREAD: (cur_tid s <> 1)%nat)
      (GET_C: get_cur_thread s = Some (Local ls))
      (FINAL: Smallstep.final_state OpenLTS ls (rs_r,gmem))
      (RETVAL: res = rs_r # RAX)
      (MEM_YIELD: Mem.yield gmem target p = gmem')
      (SET_C: update_cur_thread s (Final res) = s'),
      switch_out s s' target gmem'.

  Inductive switch_in : state -> state -> nat -> mem -> Prop :=
  |switch_in_yield : forall s' s'' target gmem' ls1 ls1' rs1 rs1'
      (GET_T: get_thread s' target = Some (Returny ls1 rs1))
      (AFT_E: Smallstep.after_external OpenLTS ls1 (rs1', gmem') ls1')
      (** Maybe we need more operations here *)
      (SET_RS: rs1' = Pregmap.set PC (rs1 RA) rs1)
      (YIELD_ST: yield_state_asm s' (Local ls1') target = s''),
     switch_in s' s'' target gmem'
  |switch_in_join : forall s' s'' target gmem' ls1 ls1' wait gmem'' rs1 i res rs1'
      (GET_T: get_thread s' target = Some (Returnj ls1 rs1))
      (WAIT_THE: rs1 # RDI = Vint i /\ int_to_nat i = wait)
      (RNG_WAIT: (1 <= wait < next_tid s') %nat)
      (GET_WAIT: get_thread s' wait = Some (Final res))
      (MEM_RES: Mem.storev Many64 gmem' (rs1 # RSI) res = Some gmem'')
      (AFT_E: Smallstep.after_external OpenLTS ls1 (rs1', gmem'') ls1')
      (SET_RS: rs1' = Pregmap.set RAX (Vint Int.one)(Pregmap.set PC (rs1 RA) rs1))
      (YIELD_ST: yield_state_asm s' (Local ls1') target = s''),
      switch_in s' s'' target gmem'
  |switch_in_initial : forall s' s'' rs0 ls1' target gmem'
      (GET_T: get_thread s' target = Some (Initial rs0)) (* the target thread is just created *)
      (INITIAL: Smallstep.initial_state OpenLTS (rs0, gmem') ls1')
      (YIELD_ST: yield_state_asm s' (Local ls1') target = s''),
     switch_in s' s'' target gmem'.

  Inductive step : genvtype -> state -> trace -> state -> Prop :=
  |step_local : forall ge ls1 t ls2 s s',
      get_cur_thread s = Some (Local ls1) ->
      Smallstep.step OpenLTS ge ls1 t ls2 ->
      update_thread s (cur_tid s) (Local ls2) = s' ->
      step ge s t s'
  |step_thread_create : forall ge s s' q_ptc r_ptc q_str ls ls',
      get_cur_thread s = Some (Local ls) -> (* get the current local state *)
      Smallstep.at_external OpenLTS ls q_ptc -> (* get the query to pthread_create *)
      query_is_pthread_create_asm q_ptc r_ptc q_str -> (* get the reply to [pthread_create] and query to start_routine *)
      Smallstep.after_external OpenLTS ls r_ptc ls' ->
      (* the current thread completes the primitive, regsets are unchanged *)
      pthread_create_state s (fst q_str) (Local ls') = s' ->
      step ge s E0 s'
  |step_switch : forall ge s s' s'' target gmem',
      switch_out s s' target gmem' ->
      switch_in s' s'' target gmem' ->
      step ge s (Event_switch target :: nil) s''.

  Definition globalenv := Smallstep.globalenv OpenLTS.
  
  Definition Concur_sem_asm : Closed.semantics :=
    Closed.ClosedSemantics_gen step initial_state final_state globalenv initial_se.
  
End MultiThread.   
