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

    Lemma match_se_initial : forall m skel,
      Genv.init_mem skel = Some m ->
      Genv.match_stbls (Mem.flat_inj (Mem.support m)) (Genv.symboltbl skel) (Genv.symboltbl skel).
    Proof.
      intros. exploit Genv.init_mem_genv_sup; eauto. intro SUP.
      constructor; intros; eauto.
      - rewrite <- SUP. unfold Mem.flat_inj. rewrite pred_dec_true; eauto.
      - rewrite <- SUP. exists b2. unfold Mem.flat_inj. rewrite pred_dec_true; eauto.
      - unfold Mem.flat_inj in H0. destruct Mem.sup_dec in H0; inv H0. reflexivity.
      - unfold Mem.flat_inj in H0. destruct Mem.sup_dec in H0; inv H0. reflexivity.
      - unfold Mem.flat_inj in H0. destruct Mem.sup_dec in H0; inv H0. reflexivity.
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

    Section Initial.

      Variable m0 : mem.
      Variable main_b : block.

      Definition main_id := prog_main (skel OpenC).
      
      Hypothesis INITM: Genv.init_mem (skel OpenC) = Some m0.
      Hypothesis FINDMAIN: Genv.find_symbol se main_id = Some main_b.

      Let j0 := Mem.flat_inj (Mem.support m0).
      Let Hm0 := Genv.initmem_inject (skel OpenC) INITM.
      Definition wj0 := injpw j0 m0 m0 Hm0.
      Let rs0 := initial_regset (Vptr main_b Ptrofs.zero).
      Definition init_w := cajw wj0 main_sig rs0.

    End Initial.
                              
      
    Definition empty_worlds : NatMap.t (option cc_cainjp_world) := NatMap.init None.
    Definition initial_worlds (w: cc_cainjp_world) := NatMap.set 1%nat (Some w) empty_worlds.

    (** * We shall add more and more invariants about global states here *)
    Inductive match_states : fsim_index -> CMulti.state OpenC -> state OpenA -> Prop :=
    |global_match_intro : forall threadsC threadsA i cur next worlds w0 m0 main_b
      (CUR_VALID: (1 <= cur < next)%nat)
      (INITMEM: Genv.init_mem (skel OpenC) = Some m0)
      (FINDMAIN: Genv.find_symbol se main_id = Some main_b)
      (INITW: w0 = init_w m0 main_b INITMEM)
      (MAIN_THREAD_INITW: NatMap.get 1%nat worlds = Some w0)
      (THREADS: forall n, (1 <= n < next)%nat -> exists w lsc lsa i',
              NatMap.get n worlds = Some w /\
              injp_match_stbls (cajw_injp w) se tse /\
              NatMap.get n threadsC = Some lsc /\
              NatMap.get n threadsA = Some lsa /\
              match_thread_states w i' lsc lsa),
        match_states i (mk_gstate OpenC threadsC cur next) (mk_gstate_asm OpenA threadsA cur next).

    Lemma foo {A: Type} (n: nat) (map : NatMap.t (option A)) (a b: A) :
      NatMap.get n map = Some a -> NatMap.get n map = Some b -> a = b.
    Proof.
      intros. congruence.
    Qed.
      
    Theorem Concur_Sim : Closed.forward_simulation ConcurC ConcurA.
    Proof.
      econstructor. instantiate (3:= fsim_index). instantiate (2:= fsim_order).
      instantiate (1:= match_states).
      constructor. auto.
      - intros. inv H.
        (* Genv.initmem_inject. *)
        apply Genv.initmem_inject in H1 as Hm0.
        exploit Genv.init_mem_genv_sup; eauto. intro SUP.
        (* set (j0 := Mem.flat_inj (Mem.support m0)).
        set (wj0 := injpw j0 m0 m0 Hm0). *)
        set (w0 := init_w m0 main_b H1). unfold init_w, wj0 in w0.
        generalize valid_se. intro VALID.
        simpl in fsim_lts.
        assert (MSE': injp_match_stbls (cajw_injp w0) se tse).
        constructor.  rewrite <- MSE. apply match_se_initial; eauto.
        unfold se, CMulti.initial_se. rewrite SUP. eauto with mem. rewrite <- MSE.
        unfold se, CMulti.initial_se. rewrite SUP. eauto with mem.
        specialize (fsim_lts se tse w0 MSE' VALID) as FSIM.
        set (rs0 := initial_regset (Vptr main_b Ptrofs.zero)).
        set (q2 := (rs0,m0)).
        set (q1 := {| cq_vf := Vptr main_b Ptrofs.zero; cq_sg := main_sig; cq_args := nil; cq_mem := m0 |}).
        assert (MQ: match_query cc_c_asm_injp w0 q1 q2).
        { (* match initial query *)
          assert (NONEARG: Conventions1.loc_arguments main_sig = nil).
          unfold main_sig. unfold Conventions1.loc_arguments. destruct Archi.ptr64; simpl; eauto.
          destruct Archi.win64; simpl; eauto.
          econstructor.
          - rewrite NONEARG. simpl. constructor.
          - econstructor. unfold Mem.flat_inj. rewrite pred_dec_true.
            reflexivity.  rewrite <- SUP.
            eapply Genv.genv_symb_range; eauto. reflexivity.
          - intros. unfold Conventions.size_arguments in H.
            rewrite NONEARG in H. simpl in H. inv H.
          - admit.
          - admit.
          - admit.
          - econstructor. simpl. red.
            unfold Conventions.size_arguments. rewrite NONEARG.
            reflexivity.
          - congruence.
          - admit.
        }
        eapply fsim_match_initial_states in FSIM as FINI; eauto.
        destruct FINI as [i [ls2 [A B]]].
        exists i. eexists. split.
        + econstructor. unfold AsmMulti.main_id, initial_se.
          unfold CMulti.initial_se, CMulti.main_id in H0.
          rewrite <- fsim_skel. eauto. rewrite <- fsim_skel. eauto.
          reflexivity.  eauto. 
        + econstructor; eauto. instantiate (3:= initial_worlds w0).
          instantiate (1:= H1). reflexivity.
          intros.
          assert (n=1)%nat. lia. subst. 
          exists w0, (CMulti.Local OpenC ls), (Local OpenA ls2), i.
          repeat apply conj; eauto. simpl.
          constructor. unfold match_local_states. eauto.
      - (* final *)
        intros. inv H0. inv H.
        simpl in *. subst cur.
        unfold CMulti.get_cur_thread, CMulti.get_thread in H2. simpl in H2.
        specialize (THREADS 1%nat CUR_VALID).
        destruct THREADS as (w & lsc & lsa & i' & GETW & MSEw & GETC & GETA & MS).
        assert (lsc = CMulti.Local OpenC ls).
        eapply foo; eauto. subst lsc. inv MS.
        specialize (fsim_lts se tse w MSEw valid_se) as FSIM.
        inversion FSIM. unfold match_local_states in H4.
        exploit fsim_match_final_states. eauto.
        eauto. intros [r2 [FIN MR]]. destruct r2.
        inv MR.
        econstructor; eauto. admit. (*the same as initial*)
        simpl.
        assert (sg = main_sig).
        {
          rewrite GETW in MAIN_THREAD_INITW.
          inv MAIN_THREAD_INITW. reflexivity.
        }
        subst. unfold tres in H6. simpl in H6.
        unfold Conventions1.loc_result, main_sig in H6. simpl in H6.
        destruct Archi.ptr64; simpl in H6. inv H6. eauto. inv H6. eauto.
      - (* step *)
        intros. inv H.
        + (* Local *)
          inv H0. simpl in *.
          admit.
        + (* pthread_create *)
          admit.
        + (* yield_to_yield *)
          admit.
        + (* yield_to_initial *)
          admit.
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
