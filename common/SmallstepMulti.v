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

    Definition index (n : nat) : positive :=
      match n with
      |O => 1%positive
      |_ => 1 + Pos.of_nat n
      end.

    Definition index_rev (p:positive) : nat :=
      match p with
      |xH => O
      |_ => Pos.to_nat p -1
    end.

    Lemma t_positive_t : forall (n:nat), index_rev (index n) = n.
    Proof.
      intros.
      destruct (index n) eqn:Hn; unfold index_rev; destruct n; unfold index in *; lia.
    Qed.

    Lemma positive_t_positive : forall (p:positive), index(index_rev p) = p.
    Proof.
      intros. destruct (index_rev p) eqn:Hp; unfold index; destruct p; unfold index_rev in *; lia.
    Qed.

    Lemma index_inj : forall (x y : nat), index x = index y -> x = y.
    Proof.
      destruct x; destruct y; unfold index in *; lia.
    Qed.
    
    Definition eq := Nat.eq_dec.
End NatIndexed.

Module NatMap := IRMap(NatIndexed).

(** Unchecked concern: Do we need to define new events for [yield] and [pthread_create] ? Can we keep the internal events?
    Now this two points are implemented differernt with CASCompCert *)
Section MultiThread.

  Context {OpenS : semantics li_c li_c}.

  Definition local_state := state OpenS.

  Record cq_vals : Type := cqv {cqv_vf : val; cqv_sg : signature; cqv_args : list val}.

  Definition get_query (cqv : cq_vals) (m: mem) :=
    cq (cqv_vf cqv) (cqv_sg cqv) (cqv_args cqv) m.

  Definition get_cqv (q: c_query) :=
    cqv (cq_vf q) (cq_sg q) (cq_args q).
  
  Definition thread_state :Type := local_state + cq_vals.
  
  (* Maybe should be somehow added into open semantics *)
  Variable initial_query : query li_c.
  Variable final_reply : int -> reply li_c -> Prop.

  (* should be derived from skel of OpenS

     and allocate blocks for pthread primitives
  *)
  Variable initial_se : Genv.symtbl.
  
  Definition OpenLTS := activate OpenS initial_se.
  Definition ClosedS := Closed.close_semantics initial_query final_reply OpenS initial_se.

  (* We need an interface to get and set global memory from local_state *)
  (* Not sure if this is proper, maybe need some lemmas about these operations *)

  (*Variable get_gmem : local_state -> mem.
  Variable set_gmem : mem -> local_state -> local_state. *)

  (*
  Definition tid_mem (m:mem) : nat :=
    Mem.tid (Mem.support m).

  Definition stacks_mem (m:mem) :=
    Mem.stacks (Mem.support m).
   *)
  
  (** * Definition and operations of global state *)

    Record state : Type := mk_gstate
    {
      threads: NatMap.t (option thread_state);
      cur_tid : nat;
      next_tid : nat;
      (* atom_bit : bool; *)

      (* tid_gmem : exists ls, NatMap.get cur_tid threads = Some ls /\
                         tid_mem (get_gmem ls) = cur_tid /\
                         length (stacks_mem (get_gmem ls)) = next_tid; *)
    }.

  Definition empty_threads : NatMap.t (option thread_state) := NatMap.init None.
  
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
  
  Variable yield_strategy : state -> nat.
  Axiom yield_strategy_range : forall s, (1 < yield_strategy s < (next_tid s))%nat.
  (*some other properties may be added here, such as only point to active threads *)

  (* We transfer to thread tid' and update
     its local_state with an updated memory *)

  Definition yield_state (s: state) (ls: thread_state): state :=
    let tid' := yield_strategy s in
    let s' := update_cur_tid s tid' in
    update_thread s' tid' ls.

  (* We add a new thread with its initial query without memory,
      we also update the running memory by adding a new list of positives *)
  Definition pthread_create_state (s: state) (cqv : cq_vals) (ls' : thread_state): state :=
    let ntid := (next_tid s) in let ctid := (cur_tid s) in
    let s' := update_next_tid s (S ntid) in
    let s'' := update_thread s' ntid (inr cqv) in
    update_thread s'' ctid ls'.
    
  Definition genvtype := Smallstep.genvtype OpenLTS.
  
  (** Initial state of Concurrent semantics *)

  (* We need a "query" to the main function of the semantics *)
  (* Including the initial global memory*)

  Inductive initial_state : state -> Prop :=
  |initial_state_intro : forall ls s,
      cur_tid s = 1%nat -> next_tid s = 2%nat ->
      get_cur_thread s = Some (inl ls) ->
      (Closed.initial_state ClosedS) ls ->
      initial_state s.

  (** Final state of Concurrent semantics *)
  Inductive final_state : state -> int -> Prop :=  
  |final_state_intro : forall ls i s,
      cur_tid s = 1%nat ->
      get_cur_thread s = Some (inl ls) ->
      (Closed.final_state ClosedS) ls i->
      final_state s i.

  (** * Definitions about the primitive yield *)

  Definition yield_id := 1001%positive.
  Definition yield_sig := mksignature nil Tvoid cc_default.

  (* Definition func_yield_external : fundef :=
    External (EF_external "yield" yield_sig).  *)
  
  Inductive query_is_yield : query li_c -> Prop :=
  |yield_intro : forall b m,
    Genv.find_symbol initial_se yield_id = Some b ->
    query_is_yield (cq (Vptr b Ptrofs.zero) yield_sig nil m).

  (** * Definitions about the primitive pthread_create *)

  Definition pthread_create_id := 1002%positive.
  
  (* int pthread_create (void * (*start_routine) (void*), void* arg) *)
  (* TODO: not quite sure to use Tlong or Tany64 here, we used Tlong for function pointer in the Client-Server example *)
  Definition pthread_create_sig := mksignature (Tlong :: Tlong :: nil) Tint cc_default.

  
  (** Problem here: the type of start_routine here may not be accecpted by [initial_state] in Clight semantics. *)
  (** Maybe we have to do sth more to support such void* (*f) (void*) prototype, maybe not using cc_default *)
  Definition start_routine_sig := mksignature (Tlong :: nil) Tlong cc_default.


  (* turns a call to pthread_create into a call to the start_routine, the initial memory is updated in 2nd query *)
  Inductive query_is_pthread_create : query li_c -> query li_c -> Prop :=
  |pthread_create_intro :
    forall m arglist b_ptc b_start b_arg ofs m'
      (FINDPTC: Genv.find_symbol initial_se pthread_create_id = Some b_ptc)
      (ARGLIST: arglist = (Vptr b_start Ptrofs.zero) :: (Vptr b_arg ofs) :: nil)
      (MEM_CREATE: Mem.thread_create m = m'),
      query_is_pthread_create
        (cq (Vptr b_ptc Ptrofs.zero) pthread_create_sig arglist m)
        (cq (Vptr b_start Ptrofs.zero) start_routine_sig ((Vptr b_arg ofs)::nil) m').

  
  Inductive step : genvtype -> state -> trace -> state -> Prop :=
  |step_local : forall ge ls1 t ls2 s s',
      get_cur_thread s = Some (inl ls1) ->
      Smallstep.step OpenLTS ge ls1 t ls2 ->
      update_thread s (cur_tid s) (inl ls2) = s' ->
      step ge s t s'
  |step_thread_create : forall ge s s' q_ptc q_str gmem ls ls' cqv,
      get_cur_thread s = Some (inl ls) -> (* get the current local state *)
      Smallstep.at_external OpenLTS ls q_ptc -> (* get the query to pthread_create *)
      query_is_pthread_create q_ptc q_str -> (* get the query to start_routine *)
      (* The global memory is already updated from q_ptc to q_str *)
      cq_mem q_str = gmem -> (* the updated memory, only difference is the #threads *)
      get_cqv q_str = cqv -> (*the initial query without memory, is stored as initial state in new thread *)
      Smallstep.after_external OpenLTS ls (cr (Vint Int.one) gmem) ls' -> (* the current thread completes the primitive*)
      pthread_create_state s cqv (inl ls') = s' ->
      step ge s E0 s'
  (** yield to a thread which is waiting for the reply of its own [yield()] *)
  |step_thread_yield_to_yield : forall ge s s' tid' q gmem' p ls ls1 ls1',
      get_cur_thread s = Some (inl ls) ->
      Smallstep.at_external OpenLTS ls q ->
      query_is_yield q ->
      yield_strategy s = tid' ->
      (*the proof p may be a problem, provided from the invariant between state and the support in gmem *)
      Mem.yield (cq_mem q) tid' p = gmem' ->
      get_thread s (tid') = Some (inl ls1) -> (* the target thread is waiting for reply *)
      Smallstep.after_external OpenLTS ls1 (cr Vundef gmem') ls1' ->
      yield_state s (inl ls1') = s' ->
      step ge s E0 s'
  (** yield to a thread which has not been initialized from a query *)
  |step_thread_yield_to_initial : forall ge s s' tid' q gmem' p ls cqv ls1',
      get_cur_thread s = Some (inl ls) ->
      Smallstep.at_external OpenLTS ls q ->
      query_is_yield q ->
      yield_strategy s = tid' ->
      Mem.yield (cq_mem q) tid' p = gmem' ->
      get_thread s (tid') = Some (inr cqv) -> (* the target thread is waiting for reply *)
      Smallstep.initial_state OpenLTS (get_query cqv gmem') ls1' ->
      yield_state s (inl ls1') = s' ->
      step ge s E0 s'.
  
End MultiThread.   
  
