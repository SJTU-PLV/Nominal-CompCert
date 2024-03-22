Require Import Coqlib Errors Events Globalenvs Ctypes AST Memory Values Integers Asm.
Require Import LanguageInterface.
Require Import Smallstep SmallstepClosed.
Require Import ValueAnalysis.
Require Import CMulti AsmMulti.
Require Import InjectFootprint CA Compiler.

Section ConcurSim.

  (** Hypothesis *)
  Variable OpenC : semantics li_c li_c.

  Variable OpenA : semantics li_asm li_asm.

  (* Hypothesis OpenSim : forward_simulation cc_c_asm_injp cc_c_asm_injp OpenC OpenA. *)

  
  (** * Get the concurrent semantics *)

  Let ConcurC := Concur_sem_c OpenC.
  Let ConcurA := Concur_sem_asm OpenA.

  (** * Initialization *)
  Let se := CMulti.initial_se OpenC.
  Let tse := initial_se OpenA.

  (*Definition main_id := prog_main (skel OpenA).
  
  Definition rs0 :=
    (Pregmap.init Vundef) # PC <- (Genv.symbol_address tse (main_id) Ptrofs.zero)
                          # RA <- Vnullptr
                          # RSP <- Vnullptr.
   *)
  Section FSIM.

    Variable fsim_index : Type.
    Variable fsim_order : fsim_index -> fsim_index -> Prop.
    Variable fsim_match_states : Genv.symtbl -> Genv.symtbl -> cc_cainjp_world -> fsim_index ->
                                 Smallstep.state OpenC -> Smallstep.state OpenA -> Prop.
    Hypothesis fsim_skel : skel OpenC = skel OpenA.
    Hypothesis fsim_lts : forall (se1 se2 : Genv.symtbl) (wB : ccworld cc_c_asm_injp),
        match_senv cc_c_asm_injp wB se1 se2 ->
        Genv.valid_for (skel OpenC) se1 ->
        fsim_properties cc_c_asm_injp cc_c_asm_injp se1 se2 wB (OpenC se1) 
          (OpenA se2) fsim_index fsim_order (fsim_match_states se1 se2 wB).
    
    Hypothesis fsim_order_wf : well_founded fsim_order.
    
    (** Utilizing above properties *)
    Definition match_local_states := fsim_match_states se tse.

    Lemma MSE : se = tse.
    Proof.
      unfold se, tse. destruct OpenC, OpenA.
      unfold CMulti.initial_se. unfold initial_se.
      simpl in *. congruence.
    Qed.

    Lemma valid_se : Genv.valid_for (skel OpenC) se.
    Proof.
      unfold se. unfold CMulti.initial_se. red.
      intros.
      apply Genv.find_info_symbol in H. destruct H as [b [A B]].
      exists b,g. split. auto. split. auto.
      apply Linking.linkorder_refl.
    Qed.
    
    (** Definition of match_state *)
    Let thread_state_C := CMulti.thread_state OpenC.
    Let thread_state_A := AsmMulti.thread_state OpenA.
    
    Inductive match_thread_states : cc_cainjp_world -> fsim_index -> thread_state_C -> thread_state_A -> Prop :=
    |match_local : forall w i sc sa,
        match_local_states w i sc sa ->
        match_thread_states w i (CMulti.Local OpenC sc) (Local OpenA sa)
    |match_initial : forall w i cqv rs m tm,
        match_query cc_c_asm_injp w (get_query cqv m) (rs,tm) ->
        match_thread_states w i (CMulti.Initial OpenC cqv) (Initial OpenA rs)
    |match_return : forall w i sc sa qc rs tm,
        match_local_states w i sc sa ->
        (* match_query cc_c_asm_injp w ( )-> *)
        query_is_yield OpenC qc ->
        query_is_yield_asm OpenA (rs, tm) ->
        match_query cc_c_asm_injp w qc (rs, tm) ->
        match_thread_states w i (CMulti.Return OpenC sc) (Return OpenA sa rs).

    (* Definition worlds : Type := NatMap.t (option cc_cainjp_world). *)
    Definition empty_worlds : NatMap.t (option cc_cainjp_world) := NatMap.init None.
    Definition initial_worlds (w: cc_cainjp_world) := NatMap.set 1%nat (Some w) empty_worlds.
    
    Inductive match_states : fsim_index -> CMulti.state OpenC -> state OpenA -> Prop :=
    |global_match_intro : forall threadsC threadsA i cur next worlds
      (THREADS: forall n, (1 <= n < next)%nat -> exists w lsc lsa i',
            NatMap.get n worlds = Some w /\
              NatMap.get n threadsC = Some lsc /\
              NatMap.get n threadsA = Some lsa /\
              match_thread_states w i' lsc lsa /\
              fsim_order i' i),
        match_states i (mk_gstate OpenC threadsC cur next) (mk_gstate_asm OpenA threadsA cur next).

    Theorem Concur_Sim : Closed.forward_simulation ConcurC ConcurA.
    Proof.
      econstructor. instantiate (3:= fsim_index). instantiate (2:= fsim_order).
      instantiate (1:= match_states).
      constructor. auto.
      - intros. inv H.
        
      Admitted.

  End FSIM.

  Lemma SIM : forward_simulation cc_c_asm_injp cc_c_asm_injp OpenC OpenA ->
    Closed.forward_simulation ConcurC ConcurA.
  Proof.
    intro. inv H. inv X. eapply Concur_Sim; eauto.
  Qed.

End ConcurSim.

Theorem Opensim_to_Globalsim : forall OpenC OpenA,
    forward_simulation cc_c_asm_injp cc_c_asm_injp OpenC OpenA ->
    Closed.forward_simulation (Concur_sem_c OpenC) (Concur_sem_asm OpenA).
Proof.
  intros. eapply SIM; eauto.
Qed.
