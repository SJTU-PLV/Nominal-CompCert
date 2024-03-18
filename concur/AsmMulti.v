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

Require Import Asm SmallstepMulti.

Section MultiThread.
  
  Context {OpenS: Smallstep.semantics li_asm li_asm}.

  Definition local_state := Smallstep.state OpenS.

  Definition thread_state : Type := local_state + regset.

  Variable initial_query : query li_asm.
  Variable final_reply : int -> reply li_asm -> Prop.

  Variable initial_se : Genv.symtbl.

  Definition OpenLTS := activate OpenS initial_se.
  Definition ClosedS := Closed.close_semantics initial_query final_reply OpenS initial_se.

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
  
  Variable yield_strategy : state -> nat.
  Axiom yield_strategy_range : forall s, (1 < yield_strategy s < (next_tid s))%nat.

  Definition yield_state (s: state) (ls: thread_state): state :=
    let tid' := yield_strategy s in
    let s' := update_cur_tid s tid' in
    update_thread s' tid' ls.

  (* We add a new thread with its initial query without memory,
      we also update the running memory by adding a new list of positives *)
  Definition pthread_create_state (s: state) (regs: regset) (ls' : thread_state): state :=
    let ntid := (next_tid s) in let ctid := (cur_tid s) in
    let s' := update_next_tid s (S ntid) in
    let s'' := update_thread s' ntid (inr regs) in
    update_thread s'' ctid ls'.
    
  Definition genvtype := Smallstep.genvtype OpenLTS.
  
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

  Require Import Conventions1.
  
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
      get_cur_thread s = Some (inl ls1) ->
      Smallstep.step OpenLTS ge ls1 t ls2 ->
      update_thread s (cur_tid s) (inl ls2) = s' ->
      step ge s t s'
  |step_thread_create : forall ge s s' q_ptc rs_str gmem ls ls',
      get_cur_thread s = Some (inl ls) -> (* get the current local state *)
      Smallstep.at_external OpenLTS ls q_ptc -> (* get the query to pthread_create *)
      query_is_pthread_create_asm q_ptc (rs_str, gmem) -> (* get the query to start_routine *)
      Smallstep.after_external OpenLTS ls (fst q_ptc, gmem) ls' ->
      (* the current thread completes the primitive, regsets are unchanged *)
      pthread_create_state s rs_str (inl ls') = s' ->
      step ge s E0 s'.
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
