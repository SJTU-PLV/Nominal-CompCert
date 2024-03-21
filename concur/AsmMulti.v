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
  |Return : forall (ls : local_state) (rs : regset), thread_state.

  Definition initial_se := Genv.symboltbl (skel OpenS).

  Definition OpenLTS := activate OpenS initial_se.

  Record state : Type := mk_gstate_asm
      {
        threads : NatMap.t (option thread_state);
        cur_tid : nat;
        next_tid : nat;
      }.

  Definition empty_threads : NatMap.t (option thread_state) := NatMap.init None.
  
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

  Fixpoint yield_strategy' (threads: NatMap.t (option thread_state)) (next: nat) :=
    match next with
    |O | S O => 1%nat (*next should be >= 2, this is meaningless*)
    |S n => (* n is the max valid thread id*)
       match NatMap.get n threads with
       | Some (Initial _) | Some (Return _ _) => n
       | _ => yield_strategy' threads n
       end
    end.
  
  Definition yield_strategy (s:state) := yield_strategy' (threads s) (next_tid s).
  
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
  Definition yield_state_asm (s: state) (ls_cur ls_new: thread_state): state :=
    let tid' := yield_strategy s in
    let s' := update_cur_thread s ls_cur in
    let s'' := update_cur_tid s' tid' in
    update_thread s'' tid' ls_new.

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
  |initial_state_intro : forall ls s main_b m0 rs0,
      cur_tid s = 1%nat -> next_tid s = 2%nat ->
      get_cur_thread s = Some (Local ls) ->
      Genv.find_symbol initial_se main_id = Some main_b ->
      Genv.init_mem (skel OpenS) = Some m0 ->
      rs0 = initial_regset (Vptr main_b Ptrofs.zero) ->
      (Smallstep.initial_state OpenLTS) (rs0,m0) ls ->
      initial_state s.

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


  (* We should not define it like this, it's tautoloty
  Inductive query_is_yield_asm : query li_asm -> Prop :=
  |yield_intro : forall rs m q_c,
      query_is_yield qc ->
      cc_c_asm_mq (caw yield_sig rs m) qc (rs,m) ->
      query_is_yield (rs, m). *)

  (* Print yield_sig.
     yield_sig = {| sig_args := nil; sig_res := Tvoid; sig_cc := cc_default |}
     : signature
   *)

  Inductive query_is_yield_asm : query li_asm -> Prop :=
  |yield_intro_asm : forall rs m b,
      Genv.find_symbol initial_se yield_id = Some b ->
      rs # PC = Vptr b Ptrofs.zero ->
      query_is_yield_asm (rs, m).

  (*
  pthread_create_sig = 
{| sig_args := Tlong :: Tlong :: nil; sig_res := Tint; sig_cc := cc_default |}
     : signature
 *)

  Axiom not_win : Archi.win64 = false.
  
  (* the ptr to start_routine is in RDI, the pointer to its argument is in RSI *)
  Theorem pthread_create_locs :
    loc_arguments pthread_create_sig = One (Locations.R Machregs.DI) :: One (Locations.R Machregs.SI) :: nil.
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
  
  Inductive query_is_pthread_create_asm : query li_asm -> query li_asm -> Prop :=
  |pthread_create_intro :
    forall m b_ptc b_start b_arg ofs m' rs rs'
      (FINDPTC: Genv.find_symbol initial_se pthread_create_id = Some b_ptc)
      (RS_PC: rs # PC = Vptr b_ptc Ptrofs.zero)
      (RS_RDI : rs # RDI = Vptr b_start Ptrofs.zero)
      (RS_RSI : rs # RSI = Vptr b_arg ofs)
      (RS'_PC : rs' # PC = Vptr b_start Ptrofs.zero)
      (rs'_RDI : rs' # RDI = Vptr b_arg ofs)
      (** We may need more requirements of rs' here *)
      (MEM_CREATE: Mem.thread_create m = m'),
      query_is_pthread_create_asm (rs,m) (rs', m').
  
  Inductive step : genvtype -> state -> trace -> state -> Prop :=
  |step_local : forall ge ls1 t ls2 s s',
      get_cur_thread s = Some (Local ls1) ->
      Smallstep.step OpenLTS ge ls1 t ls2 ->
      update_thread s (cur_tid s) (Local ls2) = s' ->
      step ge s t s'
  |step_thread_create : forall ge s s' q_ptc rs_str gmem ls ls',
      get_cur_thread s = Some (Local ls) -> (* get the current local state *)
      Smallstep.at_external OpenLTS ls q_ptc -> (* get the query to pthread_create *)
      query_is_pthread_create_asm q_ptc (rs_str, gmem) -> (* get the query to start_routine *)
      Smallstep.after_external OpenLTS ls (fst q_ptc, gmem) ls' ->
      (* the current thread completes the primitive, regsets are unchanged *)
      pthread_create_state s rs_str (Local ls') = s' ->
      step ge s E0 s'
  (** yield to a thread which is waiting for the reply of its own [yield()] *)
  |step_thread_yield_to_yield : forall ge s s' tid' rs_q m_q gmem' p ls ls1 ls1' rs1 rs',
      get_cur_thread s = Some (Local ls) ->
      Smallstep.at_external OpenLTS ls (rs_q,m_q) ->
      query_is_yield_asm (rs_q,m_q) ->
      yield_strategy s = tid' ->
      (*the proof p may be a problem, provided from the invariant between state and the support in gmem *)
      Mem.yield m_q tid' p = gmem' ->
      get_thread s (tid') = Some (Return ls1 rs1) -> (* the target thread is waiting for reply *)
      Smallstep.after_external OpenLTS ls1 (rs1, gmem') ls1' ->
      (* Caution: it seems not correct here to directly use rs1, some RA -> PC things should be done *)
      (** Maybe we need more operations here *)
      rs' = Pregmap.set RA (rs_q PC) rs_q ->
      yield_state_asm s (Return ls rs_q) (Local ls1') = s' ->
      step ge s E0 s'
  (** yield to a thread which has not been initialized from a query *)
  |step_thread_yield_to_initial : forall ge s s' tid' rs_q m_q gmem' p ls rs0 ls1' rs',
      get_cur_thread s = Some (Local ls) ->
      Smallstep.at_external OpenLTS ls (rs_q, m_q) ->
      query_is_yield_asm (rs_q, m_q) ->
      yield_strategy s = tid' ->
      Mem.yield m_q tid' p = gmem' ->
      get_thread s (tid') = Some (Initial rs0) -> (* the target thread is just created *)
      Smallstep.initial_state OpenLTS (rs0, gmem') ls1' ->
      rs' = Pregmap.set RA (rs_q PC) rs_q ->
      yield_state_asm s (Return ls rs_q) (Local ls1') = s' ->
      step ge s E0 s'.

  Definition globalenv := Smallstep.globalenv OpenLTS.
  
  Definition Concur_sem_asm : Closed.semantics :=
    Closed.ClosedSemantics_gen step initial_state final_state globalenv initial_se.
  
End MultiThread.   
