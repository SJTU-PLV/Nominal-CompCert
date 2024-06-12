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

Require Import MultiLibs.

Section MultiThread.

  Variable OpenS : semantics li_c li_c.

  Definition local_state := state OpenS.

  Record cq_vals : Type := cqv {cqv_vf : val; cqv_sg : signature; cqv_args : list val}.

  Definition get_query (cqv : cq_vals) (m: mem) :=
    cq (cqv_vf cqv) (cqv_sg cqv) (cqv_args cqv) m.

  Definition get_cqv (q: c_query) :=
    cqv (cq_vf q) (cq_sg q) (cq_args q).

  Inductive thread_state : Type :=
  |Local : forall (ls : local_state), thread_state
  |Initial : forall (cqv : cq_vals), thread_state
  |Returny : forall (ls : local_state), thread_state
  |Returnj : forall (ls : local_state) (target: nat) (vptr : val) , thread_state
  |Final : forall (res : val), thread_state.
    
  Definition initial_se := Genv.symboltbl (skel OpenS).
  
  Definition OpenLTS := activate OpenS initial_se.
  
  (** * Definition and operations of global state *)

    Record state : Type := mk_gstate
    {
      threads: NatMap.t (option thread_state);
      cur_tid : nat;
      next_tid : nat;
      (* atom_bit : bool; *)


      (* *)
      (* tid_gmem : exists ls, NatMap.get cur_tid threads = Some ls /\
                         tid_mem (get_gmem ls) = cur_tid /\
                         length (stacks_mem (get_gmem ls)) = next_tid; *)
    }.

  Definition empty_threads : NatMap.t (option thread_state) := NatMap.init None.
    
  Definition initial_gstate (s : local_state) :=
    mk_gstate (NatMap.set 1%nat (Some (Local s)) empty_threads) 1 2.
  
  Definition update_threads (s: state) (t: NatMap.t (option thread_state)) :=
    mk_gstate t (cur_tid s) (next_tid s) .

  Definition update_thread (s: state) (tid : nat) (ls: thread_state) :=
    mk_gstate (NatMap.set tid (Some ls) (threads s)) (cur_tid s) (next_tid s).

  Definition update_cur_thread (s: state) (ls : thread_state) := update_thread s (cur_tid s) ls.
  
  Definition get_thread (s: state) (tid: nat) :=
    NatMap.get tid (threads s).

  Definition get_cur_thread (s: state) := get_thread s (cur_tid s).
  
  Definition update_cur_tid (s: state) (tid : nat) :=
    mk_gstate (threads s) tid (next_tid s).

  Definition update_next_tid (s: state) (tid: nat) :=
    mk_gstate (threads s) (cur_tid s) tid.

  Definition genvtype := Smallstep.genvtype OpenLTS.
  
  (** Initial state of Concurrent semantics *)

  (** Construct the initial memory *)
  Definition main_id := prog_main (skel OpenS).
  Definition main_sig := AST.mksignature nil (AST.Tret AST.Tint) AST.cc_default.
  
  Inductive initial_state : state -> Prop :=
  |initial_state_intro : forall ls main_b m0,
      Genv.find_symbol initial_se main_id = Some main_b ->
      Genv.init_mem (skel OpenS) = Some m0 ->
      (Smallstep.initial_state OpenLTS)
        (cq (Vptr main_b Ptrofs.zero) main_sig nil m0) ls ->
      (* (Closed.initial_state ClosedS) ls -> *)
      initial_state (initial_gstate ls).

  (** Final state of Concurrent semantics *)
  Inductive final_state : state -> int -> Prop :=  
  |final_state_intro : forall ls i s m,
      cur_tid s = 1%nat ->
      get_cur_thread s = Some (Local ls) ->
      (Smallstep.final_state OpenLTS) ls (cr (Vint i) m)->
      final_state s i.

  (** * Definitions about the primitive yield *)

  Inductive query_is_yield : query li_c -> nat -> Prop :=
  |yield_intro : forall b m next,
    Genv.find_symbol initial_se yield_id = Some b ->
    Mem.next_tid (Mem.support m) = next ->
    query_is_yield (cq (Vptr b Ptrofs.zero) yield_sig nil m) next.

  Definition yield_state (s: state) (ls_new: thread_state) (target: nat): state :=
    (* let tid' := yield_strategy s in *)
    let s' := update_cur_tid s target in
    update_thread s' target ls_new.


  (** * Definitions about the primitive pthread_create *)

  Inductive query_is_pthread_create : query li_c -> query li_c -> Prop :=
  |pthread_create_intro :
    forall m arglist b_ptc b_start b_arg ofs_arg b_t ofs_t m' start_id tid m''
      (FINDPTC: Genv.find_symbol initial_se pthread_create_id = Some b_ptc)
      (FINDSTR: Genv.find_symbol initial_se start_id = Some b_start)
      (ARGLIST: arglist = (Vptr b_t ofs_t) :: (Vptr b_start Ptrofs.zero) :: (Vptr b_arg ofs_arg) :: nil)
      (MEM_CREATE: Mem.thread_create m = (m', tid))
      (NMAX: (tid < 1000)%nat)
      (THREAD_V: Mem.storev Mint64 m' (Vptr b_t ofs_t) (Vint (nat_to_int tid NMAX)) = Some m''),
      query_is_pthread_create
        (cq (Vptr b_ptc Ptrofs.zero) pthread_create_sig arglist m)
        (cq (Vptr b_start Ptrofs.zero) start_routine_sig ((Vptr b_arg ofs_arg)::nil) m').

  (* We add a new thread with its initial query without memory,
     we also update the running memory by adding a new list of positives *)
  Definition pthread_create_state (s: state) (cqv : cq_vals) (ls' : thread_state): state :=
    let ntid := (next_tid s) in let ctid := (cur_tid s) in
    let s' := update_next_tid s (S ntid) in
    let s'' := update_thread s' ntid (Initial cqv) in
    update_thread s'' ctid ls'.
    

  (** * Definitions about the primitive join *)

  Definition pthread_join_id := 1003%positive.
  (** int pthread_join (int * thread, void ** value_ptr) *)
  Definition pthread_join_sig := mksignature (Tint :: Tlong :: nil) Tint cc_default.

  Inductive query_is_pthread_join : query li_c -> nat -> val -> Prop :=
  |pthread_join_intro :
    forall m arglist b_ptj target_id b_vptr ofs_vptr i
      (FINDPTJ: Genv.find_symbol initial_se pthread_join_id = Some b_ptj)
      (ARGLIST: arglist = (Vint i) :: (Vptr b_vptr ofs_vptr) :: nil)
      (TARGETID: target_id = int_to_nat i),
      query_is_pthread_join
        (cq (Vptr b_ptj Ptrofs.zero) pthread_join_sig arglist m) target_id (Vptr b_vptr ofs_vptr).

  (** Definitions about the primitives lock and unlock *)

  Definition pthread_mutex_lock_id := 1004%positive.
  (** int lock (int *mutex); *)
  Definition pthread_mutex_lock_sig := mksignature (Tint :: nil) Tvoid cc_default.

  

  

  (*

                                                           Pr & con
                                                              <=
  [producer.c] + [consumer.c]   --(thread linking)-->  [Closed semantics]


                                                         <= ...
                                                       assembly implementation (using OS primitives)
  
  distribute clock
   *)

  Inductive initial_state : 
  Inductive switch_out : state -> state -> nat -> mem -> Prop :=
  |switch_out_yield : forall s s' ls q target p gmem'
      (GET_C: get_cur_thread s = Some (Local ls))
      (AT_E: Smallstep.at_external OpenLTS ls q)
      (Q_YIE: query_is_yield q (next_tid s))
      (MEM_YIELD: Mem.yield (cq_mem q) target p = gmem')
      (SET_C:update_cur_thread s (Returny ls) = s'),
      switch_out s s' target gmem'
  |switch_out_join : forall s s' ls q wait vptr target p gmem'
      (GET_C: get_cur_thread s = Some (Local ls))
      (AT_E: Smallstep.at_external OpenLTS ls q)
      (Q_JOIN: query_is_pthread_join q wait vptr)
      (MEM_YIELD: Mem.yield (cq_mem q) target p = gmem')
      (SET_C: update_cur_thread s (Returnj ls wait vptr) = s'),
      switch_out s s' target gmem'
  |switch_out_final : forall s s' ls res gmem target p gmem'
      (SUB_THREAD: (cur_tid s <> 1)%nat)
      (GET_C: get_cur_thread s = Some (Local ls))
      (FINAL: Smallstep.final_state OpenLTS ls (cr res gmem))
      (MEM_YIELD: Mem.yield gmem target p = gmem')
      (SET_C: update_cur_thread s (Final res) = s'),
      switch_out s s' target gmem'.

  Inductive switch_in : state -> state -> nat -> mem -> Prop :=
  |switch_in_yield : forall s' s'' target gmem' ls1 ls1'
     (GET_T: get_thread s' target = Some (Returny ls1))
   (* the target thread is waiting for reply *)
     (AFT_E: Smallstep.after_external OpenLTS ls1 (cr Vundef gmem') ls1')
     (YIE_ST: yield_state s' (Local ls1') target = s''),
     switch_in s' s'' target gmem'
  |switch_in_join : forall s' s'' target gmem' ls1 ls1' tar' vptr res gmem''
     (GET_T: get_thread s' target = Some (Returnj ls1 tar' vptr))
     (RNG_WAIT: (1 <= tar' < next_tid s') %nat)
     (GET_WAIT: get_thread s' tar' = Some (Final res))
      (* store the return value of tar' thread *)
     (MEM_RES: Mem.storev Many64 gmem' vptr res = Some gmem'')
     (AFT_E: Smallstep.after_external OpenLTS ls1 (cr (Vint Int.one) gmem'') ls1')
     (YIELD_ST: yield_state s' (Local ls1') target = s''),
      switch_in s' s'' target gmem'
  |switch_in_initial : forall s' s'' cqv ls1' target gmem'
     (GET_T: get_thread s' target = Some (Initial cqv)) 
     (INITIAL: Smallstep.initial_state OpenLTS (get_query cqv gmem') ls1')
     (YIELD_ST: yield_state s' (Local ls1') target = s''),
     switch_in s' s'' target gmem'.
  
  Inductive step : genvtype -> state -> trace -> state -> Prop :=
  |step_local : forall ge ls1 t ls2 s s',
      get_cur_thread s = Some (Local ls1) ->
      Smallstep.step OpenLTS ge ls1 t ls2 ->
      update_thread s (cur_tid s) (Local ls2) = s' ->
      step ge s t s'
  |step_thread_create : forall ge s s' q_ptc q_str gmem ls ls' cqv,
      get_cur_thread s = Some (Local ls) -> (* get the current local state *)
      Smallstep.at_external OpenLTS ls q_ptc -> (* get the query to pthread_create *)
      query_is_pthread_create q_ptc q_str -> (* get the query to start_routine *)
      (* The global memory is already updated from q_ptc to q_str *)
      cq_mem q_str = gmem -> (* the updated memory, difference is the #threads and the thread variable *)
      get_cqv q_str = cqv -> (*the initial query without memory, is stored as initial state in new thread *)
      Smallstep.after_external OpenLTS ls (cr (Vint Int.one) gmem) ls' -> (* the current thread completes the primitive*)
      pthread_create_state s cqv (Local ls') = s' ->
      step ge s E0 s'
  |step_at_external :

  |step_after_external :
    
  |step_switch : forall ge s s' s'' target gmem',
      switch_out s s' target gmem' ->
      switch_in s' s'' target gmem' ->
      step ge s E0 s''.
  
  Definition globalenv := Smallstep.globalenv OpenLTS.
  
  Definition Concur_sem_c : Closed.semantics :=
    Closed.ClosedSemantics_gen step initial_state final_state globalenv initial_se.

End MultiThread.
