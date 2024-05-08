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

Require Import Asm CMulti.
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
  Definition initial_regset (pc : val) :=
    (Pregmap.init Vundef) # PC <- pc
                          # RA <- Vnullptr
                          # RSP <- Vnullptr.
                                            
  Inductive initial_state : state -> Prop :=
  |initial_state_intro : forall ls main_b m0 rs0,
      Genv.find_symbol initial_se main_id = Some main_b ->
      Genv.init_mem (skel OpenS) = Some m0 ->
      rs0 = initial_regset (Vptr main_b Ptrofs.zero) ->
      (Smallstep.initial_state OpenLTS) (rs0,m0) ls ->
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

  Axiom not_win : Archi.win64 = false.
  
  (* the ptr to start_routine is in RSI, the pointer to its argument is in RDX *)
  Lemma pthread_create_locs :
    loc_arguments pthread_create_sig = One (Locations.R Machregs.DI) :: One (Locations.R Machregs.SI) :: One (Locations.R Machregs.DX) :: nil.
  Proof.
    simpl. unfold pthread_create_sig. unfold loc_arguments.
    replace Archi.ptr64 with true by reflexivity.
    rewrite not_win. simpl. reflexivity.
  Qed.

  (* the pointer to the arg of start_routine should be placed in RDI for new thread regs *)
  Theorem start_routine_loc :
    loc_arguments start_routine_sig = One (Locations.R Machregs.DI) :: nil.
  Proof.
    simpl.  simpl. unfold pthread_create_sig. unfold loc_arguments.
    replace Archi.ptr64 with true by reflexivity.
    rewrite not_win. simpl. reflexivity.
  Qed.

  Theorem pthread_join_locs :
    loc_arguments pthread_join_sig = One (Locations.R Machregs.DI) :: One (Locations.R Machregs.SI) :: nil.
  Proof.
    simpl. unfold pthread_create_sig. unfold loc_arguments.
    replace Archi.ptr64 with true by reflexivity.
    rewrite not_win. simpl. reflexivity.
  Qed.

  Inductive query_is_yield_asm : query li_asm -> nat -> Prop :=
  |yield_intro_asm : forall rs m b next,
      Genv.find_symbol initial_se yield_id = Some b ->
      rs # PC = Vptr b Ptrofs.zero ->
      Mem.next_tid (Mem.support m) = next ->
      query_is_yield_asm (rs, m) next.

  Inductive query_is_pthread_create_asm : query li_asm -> query li_asm -> Prop :=
  |pthread_create_intro :
    forall m b_ptc b_the ofs_the b_start b_arg ofs_arg m' rs rs' start_id new_tid
      (FINDPTC: Genv.find_symbol initial_se pthread_create_id = Some b_ptc)
      (FINDSTR: Genv.find_symbol initial_se start_id = Some b_start)
      (RS_PC: rs # PC = Vptr b_ptc Ptrofs.zero)
      (RS_RDI : rs # RDI = Vptr b_the ofs_the)
      (RS_RSI : rs # RSI = Vptr b_start Ptrofs.zero)
      (RS_RDX : rs # RDX = Vptr b_arg ofs_arg)
      (RS'_PC : rs' # PC = Vptr b_start Ptrofs.zero)
      (rs'_RDI : rs' # RDI = Vptr b_arg ofs_arg)
      (** We may need more requirements of rs' here *)
      (MEM_CREATE: Mem.thread_create m = (m', new_tid)),
      query_is_pthread_create_asm (rs,m) (rs', m').
  
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
  |switch_out_yield : forall s s' ls rs_q m_q target p gmem',
      get_cur_thread s = Some (Local ls) ->
      Smallstep.at_external OpenLTS ls (rs_q,m_q) ->
      query_is_yield_asm (rs_q,m_q) (next_tid s)->
      Mem.yield m_q target p = gmem' ->
      update_cur_thread s (Returny ls rs_q) = s' ->
      switch_out s s' target gmem'
  |switch_out_join : forall s s' ls rs_q m_q wait vptr target p gmem',
      get_cur_thread s = Some (Local ls) ->
      Smallstep.at_external OpenLTS ls (rs_q,m_q) ->
      query_is_pthread_join_asm (rs_q,m_q) wait vptr ->
      Mem.yield m_q target p = gmem' ->
      update_cur_thread s (Returnj ls rs_q) = s' ->
      switch_out s s' target gmem'
  |switch_out_final : forall s s' ls res (rs_r : regset) gmem target p gmem',
      get_cur_thread s = Some (Local ls) ->
      Smallstep.final_state OpenLTS ls (rs_r,gmem) ->
      res = rs_r # RAX ->
      Mem.yield gmem target p = gmem' ->
      update_cur_thread s (Final res) = s' ->
      switch_out s s' target gmem'.

  Inductive switch_in : state -> state -> nat -> mem -> Prop :=
  |switch_in_yield : forall s' s'' target gmem' ls1 ls1' rs1 rs1',
      get_thread s' target = Some (Returny ls1 rs1) -> (* the target thread is waiting for reply *)
      Smallstep.after_external OpenLTS ls1 (rs1', gmem') ls1' ->
      (** Maybe we need more operations here *)
      rs1' = Pregmap.set PC (rs1 RA) rs1 ->
      yield_state_asm s' (Local ls1') target = s'' ->
     switch_in s' s'' target gmem'
  |switch_in_join : forall s' s'' target gmem' ls1 ls1' wait gmem'' rs1 i res rs1',
      get_thread s' target = Some (Returnj ls1 rs1) ->
      rs1 # RDI = Vint i ->
      int_to_nat i = wait -> (* the thread [target] is waiting for thread [wait] *)
      (* the "wait" thread is already finished *)
      get_thread s' wait = Some (Final res) ->
      Mem.storev Many64 gmem' (rs1 # RDX) res = Some gmem'' ->
      Smallstep.after_external OpenLTS ls1 (rs1', gmem'') ls1' ->
      rs1' = Pregmap.set PC (rs1 RA) rs1 ->
      yield_state_asm s' (Local ls1') target = s'' ->
      switch_in s' s'' target gmem'
  |switch_in_initial : forall s' s'' rs0 ls1' target gmem',
      get_thread s' target = Some (Initial rs0) -> (* the target thread is just created *)
      Smallstep.initial_state OpenLTS (rs0, gmem') ls1' ->
      yield_state_asm s' (Local ls1') target = s'' ->
     switch_in s' s'' target gmem'.

  Inductive step : genvtype -> state -> trace -> state -> Prop :=
  |step_local : forall ge ls1 t ls2 s s',
      get_cur_thread s = Some (Local ls1) ->
      Smallstep.step OpenLTS ge ls1 t ls2 ->
      update_thread s (cur_tid s) (Local ls2) = s' ->
      step ge s t s'
  |step_thread_create : forall ge s s' q_ptc rs_str rs gm0 gmem ls ls',
      get_cur_thread s = Some (Local ls) -> (* get the current local state *)
      Smallstep.at_external OpenLTS ls (rs, gm0) -> (* get the query to pthread_create *)
      query_is_pthread_create_asm q_ptc (rs_str, gmem) -> (* get the query to start_routine *)
      Smallstep.after_external OpenLTS ls ((rs # PC <- (rs RA) # RAX <- (Vint (Int.one))), gmem) ls' ->
      (* the current thread completes the primitive, regsets are unchanged *)
      pthread_create_state s rs_str (Local ls') = s' ->
      step ge s E0 s'
  |step_switch : forall ge s s' s'' target gmem',
      switch_in s s' target gmem' ->
      switch_out s' s'' target gmem' ->
      step ge s E0 s''.

  Definition globalenv := Smallstep.globalenv OpenLTS.
  
  Definition Concur_sem_asm : Closed.semantics :=
    Closed.ClosedSemantics_gen step initial_state final_state globalenv initial_se.
  
End MultiThread.   
