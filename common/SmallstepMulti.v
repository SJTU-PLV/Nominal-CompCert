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

Module NatIndexed.
    Definition t := nat.

    Fixpoint index (n : nat) : positive :=
      match n with
      |O => 1%positive
      |S n => 1 + index n
      end.

    (*wrong, fix it later*)
    Definition index_rev (p:positive) : nat :=
      Pos.to_nat p.

    Lemma t_positive_t : forall (n:nat), index_rev (index n) = n.
    Admitted.

    Lemma positive_t_positive : forall (p:positive), index(index_rev p) = p.
    Admitted.

    Lemma index_inj : forall (x y : nat), index x = index y -> x = y.
    Admitted.

    Definition eq := Nat.eq_dec.
End NatIndexed.

Module NatMap := IRMap(NatIndexed).
    
Section MultiThread.

  Context {OpenS : semantics li_c li_c}.

  Definition local_state := state OpenS.

  (* Maybe should be somehow added into open semantics *)
  Variable initial_query : query li_c.
  Variable final_reply : int -> reply li_c -> Prop.

  (* should be derived from skel of OpenS

     and allocate blocks for pthread primitives
  *)
  Variable initial_se : Genv.symtbl.
  
  Definition OpenLTS := activate OpenS initial_se.
  Definition ClosedS := Closed.close_semantics initial_query final_reply OpenS initial_se.
  
  (* The global state of concurrent semantics *)

  (* problem : how to deal with "thread variable" *)

  (* Definition state := list local_state. *)


  Variable get_gmem : local_state -> mem.
  Variable set_gmem : mem -> local_state -> local_state.

  Definition tid_mem (m:mem) : nat :=
    Mem.tid (Mem.support m).

  Definition stacks_mem (m:mem) :=
    Mem.stacks (Mem.support m).

  (* Definition and operations of global state *)

    Record state : Type := mk_gstate
    {
      threads: NatMap.t (option local_state);
      cur_tid : nat;
      next_tid : nat;
      (* atom_bit : bool; *)

      (* tid_gmem : exists ls, NatMap.get cur_tid threads = Some ls /\
                         tid_mem (get_gmem ls) = cur_tid /\
                         length (stacks_mem (get_gmem ls)) = next_tid; *)
    }.

  Definition empty_threads : NatMap.t (option local_state) := NatMap.init None.
  (* Definition initial_threads (ls :local_state) := NatMap.set 1%nat (Some ls) empty_threads.
  Program Definition single_state (ls: local_state) := mk_gstate (initial_threads ls) 1%nat 2%nat false. *)

  
  Definition update_threads (s : state) (t: NatMap.t (option local_state)) :=
    mk_gstate t (cur_tid s) (next_tid s) .

  Variable yield_strategy : state -> nat.
  Axiom yield_strategy_range : forall s, (1 < yield_strategy s < (next_tid s))%nat.
  (*some other properties may be added here, such as only point to active threads *)

  (* We transfer to thread tid' and update its local_state to ls (synchronize the global memory for it) *)
  Definition yield_state (s : state) (ls : local_state): state :=
    match s with
      mk_gstate threads cid nid =>
        let tid' := yield_strategy s in
        let threads' := NatMap.set tid' (Some ls) threads in
      mk_gstate threads' tid' nid
    end.

  
  (* problem here, we need some proofs about initial local_state for this initial gstate
   *)

  Definition genvtype := Smallstep.genvtype OpenLTS.
  
  (** Initial state of Concurrent semantics *)

  (* We need a "query" to the main function of the semantics *)
  (* Including the initial global memory*)

  Inductive initial_state : state -> Prop :=
  |initial_state_intro : forall ls s,
      cur_tid s = 1%nat -> next_tid s = 2%nat ->
      NatMap.get 1%nat (threads s) = Some ls ->
      (Closed.initial_state ClosedS) ls ->
      initial_state s.

  (** Final state of Concurrent semantics *)
  Inductive final_state : state -> int -> Prop :=  
  |final_state_intro : forall ls i s,
      cur_tid s = 1%nat ->
      NatMap.get 1%nat (threads s) = Some ls ->
      final_state s i.

  Definition yield_id := 1001%positive.
  Definition yield_sig := mksignature nil Tvoid cc_default.
  
  Inductive query_is_yield : query li_c -> Prop :=
  |yield_intro : forall b m,
    Genv.find_symbol initial_se yield_id = Some b ->
    query_is_yield (cq (Vptr b Ptrofs.zero) yield_sig nil m).
  
  Inductive step : genvtype -> state -> trace -> state -> Prop :=
  |step_local : forall ge ls1 t ls2 tid s s' threads',
      let threads := threads s in
      NatMap.get tid threads = Some ls1 ->
      Smallstep.step OpenLTS ge ls1 t ls2 ->
      threads' = NatMap.set tid (Some ls2) threads ->
      s' = update_threads s threads ->
      step ge s t s'
  |step_thread_yield : forall ge s tid s' tid' gmem ls ls1 ls1' q,
      NatMap.get tid (threads s) = Some ls ->
      at_external OpenLTS ls q ->
      query_is_yield q ->
      cq_mem q = gmem ->
      NatMap.get tid' (threads s) = Some ls1 ->
      set_gmem gmem ls1 = ls1' ->
      yield_strategy s = tid' ->      
      yield_state s ls1' = s' ->
      step ge s E0 s'.
  |step_thread_create : ge s tid s' q,
      NatMap.get tid (threads s) = Some ls ->
      at_external OpenLTS ls q ->
      query_is_create q ->
      
      
      step ge s E0 s'.
           
      
  (* problem : how to simultaneously update the memory for all threads *)
  |Step_lock
  |Step_unlock
  |Step_thread_create
     
  |Step_thread_join
   
  
