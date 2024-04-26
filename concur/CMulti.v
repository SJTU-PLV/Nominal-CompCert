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
  |Returnj : forall (ls : local_state) (target: nat)(vptr : val) , thread_state
  |Final : forall (res : val), thread_state.
    
  Definition initial_se := Genv.symboltbl (skel OpenS).
  
  Definition OpenLTS := activate OpenS initial_se.
  
  (* We need an interface to get and set global memory from local_state *)
  (* Not sure if this is proper, maybe need some lemmas about these operations *)

  (*Variable get_gmem : local_state -> mem.
  Variable set_gmem : mem -> local_state -> local_state. *)
  
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

  Definition yield_id := 1001%positive.
  Definition yield_sig := mksignature nil Tvoid cc_default.

  Inductive query_is_yield : query li_c -> nat -> Prop :=
  |yield_intro : forall b m next,
    Genv.find_symbol initial_se yield_id = Some b ->
    Mem.next_tid (Mem.support m) = next ->
    query_is_yield (cq (Vptr b Ptrofs.zero) yield_sig nil m) next.

  (* Fixpoint yield_strategy' (threads: NatMap.t (option thread_state)) (next: nat) :=
    match next with
    |O | S O => 1%nat (*next should be >= 2, this is meaningless*)
    |S n => (* n is the max valid thread id*)
       match NatMap.get n threads with
       | Some (Initial _) | Some (Return _) => n
       | _ => yield_strategy' threads n
       end
    end.
  
  Definition yield_strategy (s:state) := yield_strategy' (threads s) (next_tid s).
  *)
  (* Axiom yield_strategy_range : forall s, (1 < yield_strategy s < (next_tid s))%nat. *)
  (*some other properties may be added here, such as only point to active threads *)

  (* We transfer to thread tid' and update
     its local_state with an updated memory *)

  Definition yield_state (s: state) (ls_new: thread_state) (target: nat): state :=
    (* let tid' := yield_strategy s in *)
    let s' := update_cur_tid s target in
    update_thread s' target ls_new.


  (** * Definitions about the primitive pthread_create *)

  Definition pthread_create_id := 1002%positive.
  

  (* TODO: not quite sure to use Tlong or Tany64 here, we used Tlong for function pointer in the Client-Server example *)
  (** int pthread_create (int * thread, void * (*start_routine) (void*), void* arg) *)
  Definition pthread_create_sig := mksignature (Tlong :: Tlong :: Tlong :: nil) Tint cc_default.

  
  (** Problem here: the type of start_routine here may not be accecpted by [initial_state] in Clight semantics. *)
  (** Maybe we have to do sth more to support such void* (*f) (void*) prototype, maybe not using cc_default *)
  Definition start_routine_sig := mksignature (Tlong :: nil) Tlong cc_default.

  
  (* turns a call to pthread_create into a call to the start_routine, the initial memory is updated in 2nd query *)

  (* trans between Vint and nat *)

  Definition int_to_nat (i : int) := Z.to_nat (Int.intval i).
  
  Program Definition nat_to_int (n : nat) (nmax: (n < 1000)%nat) : int := Int.mkint (Z.of_nat n) _.
  Next Obligation.
    change Int.modulus with 4294967296.
    split. lia. lia.
  Qed.

  
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

  (** 1. Shound we define these [functions] as primitives here? 
      or we should use EntAtom and ExtAtom similar to
      CASCC

      2. Whether we try to define a lock/unlock or EntAtom/ExtAtom here,
      does it matter? The only difference is that
      a yield function in critical section will become STUCK, right?

   
   *)
  
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
  (** yield to a thread which is waiting for the reply of its own [yield()] *)
  |step_thread_yield_to_yield : forall ge s s' s'' target q gmem' p ls ls1 ls1',
      get_cur_thread s = Some (Local ls) ->
      Smallstep.at_external OpenLTS ls q ->
      query_is_yield q (next_tid s) ->
     (* (1 <= target < next_tid s) -> *)
     (*  yield_strategy s = tid' -> *)
      (*the proof p may be a problem, provided from the invariant between state and the support in gmem *)
      Mem.yield (cq_mem q) target p = gmem' ->
      update_cur_thread s (Returny ls) = s' ->
      get_thread s' target = Some (Returny ls1) -> (* the target thread is waiting for reply *)
      Smallstep.after_external OpenLTS ls1 (cr Vundef gmem') ls1' ->
      yield_state s' (Local ls1') target = s'' ->
      step ge s E0 s''
    |step_thread_yield_to_join : forall ge s s' s'' target tar' vptr res q gmem' gmem'' p ls ls1 ls1',
      get_cur_thread s = Some (Local ls) ->
      Smallstep.at_external OpenLTS ls q ->
      query_is_yield q (next_tid s) ->
      Mem.yield (cq_mem q) target p = gmem' ->
      update_cur_thread s (Returny ls) = s' ->
      (* the target thread is waiting for a target thread to finish *)
      get_thread s' target = Some (Returnj ls1 tar' vptr) ->
      (* and the tar' thread is finished already *)
      get_thread s' tar' = Some (Final res) ->
      (* store the return value of tar' thread *)
      Mem.storev Many64 gmem' vptr res = Some gmem'' ->
      Smallstep.after_external OpenLTS ls1 (cr (Vint Int.one) gmem'') ls1' ->
      yield_state s' (Local ls1') target = s' ->
      step ge s E0 s''
  (** yield to a thread which has not been initialized from a query *)
  |step_thread_yield_to_initial : forall ge s s' s'' target q gmem' p ls cqv ls1',
      get_cur_thread s = Some (Local ls) ->
      Smallstep.at_external OpenLTS ls q ->
      query_is_yield q (next_tid s)->
      update_cur_thread s (Returny ls) = s' ->
      (* yield_strategy s = tid' -> *)
      Mem.yield (cq_mem q) target p = gmem' ->
      get_thread s' target = Some (Initial cqv) -> (* the target thread is waiting for reply *)
      Smallstep.initial_state OpenLTS (get_query cqv gmem') ls1' ->
      yield_state s' (Local ls1') target = s'' ->
      step ge s E0 s''
  |step_thread_join_to_yield : forall ge s s' s'' target q gmem' p ls ls1 ls1' wait vptr,
      get_cur_thread s = Some (Local ls) ->
      Smallstep.at_external OpenLTS ls q ->
      query_is_pthread_join q wait vptr ->
      update_cur_thread s (Returnj ls wait vptr) = s'->
      Mem.yield (cq_mem q) target p = gmem' ->
      get_thread s' target = Some (Returny ls1) -> (* the target thread is waiting for reply *)
      Smallstep.after_external OpenLTS ls1 (cr Vundef gmem') ls1' ->
      yield_state s' (Local ls1') target = s'' ->
      step ge s E0 s''
    (* this step can handle a direct "successful" join which does not switch out *)
    |step_thread_join_to_join : forall ge s s' s'' wait target tar' vptr res' vptr' q gmem' gmem'' p ls ls1 ls1',
      get_cur_thread s = Some (Local ls) ->
      Smallstep.at_external OpenLTS ls q ->
      query_is_pthread_join q wait vptr->
      Mem.yield (cq_mem q) target p = gmem' ->
      update_cur_thread s (Returnj ls wait vptr) = s' ->
      (* the target thread is waiting for a target thread to finish *)
      get_thread s' target = Some (Returnj ls1 tar' vptr') ->
      (* and the tar' thread is finished already *)
      get_thread s' tar' = Some (Final res') ->
      (* store the return value of tar' thread *)
      Mem.storev Many64 gmem' vptr' res' = Some gmem'' ->
      Smallstep.after_external OpenLTS ls1 (cr (Vint Int.one) gmem'') ls1' ->
      yield_state s' (Local ls1') target = s'' ->
      step ge s E0 s''
  (** yield to a thread which has not been initialized from a query *)
  |step_thread_join_to_initial : forall ge s s' s'' vptr wait target q gmem' p ls cqv ls1',
      get_cur_thread s = Some (Local ls) ->
      Smallstep.at_external OpenLTS ls q ->
      query_is_pthread_join q wait vptr ->
      (* yield_strategy s = tid' -> *)
      Mem.yield (cq_mem q) target p = gmem' ->
      update_cur_thread s (Returnj ls wait vptr) = s'->
      get_thread s' target = Some (Initial cqv) -> (* the target thread is waiting for reply *)
      Smallstep.initial_state OpenLTS (get_query cqv gmem') ls1' ->
      yield_state s' (Local ls1') target = s'' ->
      step ge s E0 s''
  |step_final_to_initial : forall ge s s' s'' target res gmem gmem' p ls cqv ls1',
      get_cur_thread s = Some (Local ls) ->
      Smallstep.final_state OpenLTS ls (cr res gmem) ->
      Mem.yield gmem target p = gmem' ->
      update_cur_thread s (Final res) = s' ->
      get_thread s' target = Some (Initial cqv) -> (* the target thread is waiting for reply *)
      Smallstep.initial_state OpenLTS (get_query cqv gmem') ls1' ->
      yield_state s' (Local ls1') target = s'' ->
      step ge s E0 s''
  |step_final_to_yield : forall ge s s' s'' target res gmem gmem' p ls ls1 ls1',
      get_cur_thread s = Some (Local ls) ->
      Smallstep.final_state OpenLTS ls (cr res gmem) ->
      Mem.yield gmem target p = gmem' ->
      update_cur_thread s (Final res) = s' ->
      get_thread s' target = Some (Returny ls1) -> (* the target thread is waiting for reply *)
      Smallstep.after_external OpenLTS ls1 (cr Vundef gmem') ls1' ->
      yield_state s' (Local ls1') target = s'' ->
      step ge s E0 s''
    |step_final_to_join : forall ge s s' s'' target tar' vptr (res: val) gmem res gmem' gmem'' p ls ls1 ls1' res',
      get_cur_thread s = Some (Local ls) ->
      Smallstep.final_state OpenLTS ls (cr res gmem) ->
      Mem.yield gmem target p = gmem' ->
      update_cur_thread s (Final res) = s' ->
      get_thread s' target = Some (Returnj ls1 tar' vptr) ->
      (* and the tar' thread is finished already *)
      get_thread s' tar' = Some (Final res') ->
      (* store the return value of tar' thread *)
      Mem.storev Many64 gmem' vptr res' = Some gmem'' ->
      Smallstep.after_external OpenLTS ls1 (cr (Vint Int.one) gmem'') ls1' ->
      yield_state s' (Local ls1') target = s'' ->
      step ge s E0 s''.
  
  Definition globalenv := Smallstep.globalenv OpenLTS.
  
  Definition Concur_sem_c : Closed.semantics :=
    Closed.ClosedSemantics_gen step initial_state final_state globalenv initial_se.

End MultiThread.
