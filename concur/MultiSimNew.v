Require Import Coqlib Errors Events Globalenvs Ctypes AST Memory Values Integers Asm.
Require Import LanguageInterface.
Require Import Smallstep SmallstepClosed.
Require Import ValueAnalysis.
Require Import CMulti AsmMulti.
Require Import InjectFootprint CA Compiler.
Require Import CallconvNew.


(** * TODOs after completing this : Generalization *)

(**
  1. generalize the callconv in this file :
  forall cc : lic <-> liasm , sim cc cc OpenC OpenA -> concur_sim OpenC OpenA

  2. generalize the language interface? can we?

  3. Implementing the primitives using assembly code... do a semantics -> syntantic sim

    [|a.asm|]_O -> [|a.asm]_G

    sim?

    [|a.asm + pthreads.asm|]_Closed

  4. Complete coroutine, non-preemptive, thread_join (thread variable), lock, unlock, condition variable

  5. preeptive, more primitives

  6. C++ atomics, SC consistency, Concurrent things

 *)


(** Properties about outgoing_argument *)
Lemma argument_size_range : forall ofsl ofs ty sig i,                      
    In (Locations.S Locations.Outgoing ofs ty) (regs_of_rpairs (Conventions1.loc_arguments sig)) ->
    Ptrofs.unsigned (Ptrofs.add ofsl (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs))) <= i <
      Ptrofs.unsigned (Ptrofs.add ofsl (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs))) +
        size_chunk (chunk_of_type ty) ->
    Mach.offset_sarg ofsl 0 <= i < Mach.offset_sarg ofsl (Conventions.size_arguments sig).
Admitted. (** ok *)


Lemma outgoing_arguments_injp_valid: forall j sig j' args Vsp m tm tm' rs,
                    Val.inject_list j args
                      (map (fun p : rpair Locations.loc => Locations.Locmap.getpair p (make_locset_rs rs tm Vsp))
                         (Conventions1.loc_arguments sig)) ->
                       inject_incr j j' ->
                       Mem.unchanged_on (loc_out_of_reach j m) tm tm' ->
                       (forall b ofs, Mach.loc_init_args (Conventions.size_arguments sig) Vsp b ofs ->
                                 loc_out_of_reach j m b ofs) ->
                       Val.inject_list j' args
                         (map (fun p : rpair Locations.loc => Locations.Locmap.getpair p (make_locset_rs rs tm' Vsp))
                            (Conventions1.loc_arguments sig)).
Admitted. (** ok but annoying *)



(** Good point : we can allow 'public' stack-allocated data shared between threads *)



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

    (* GS.fsim_components. *)
    (* Variable GS: GS.fsim_components cc_c_asm_injp_new OpenC OpenA.  *)

    Variable fsim_index : Type.
    Variable fsim_order : fsim_index -> fsim_index -> Prop.
    Variable fsim_match_states : Genv.symtbl -> Genv.symtbl -> cc_cainjp_world -> injp_world -> fsim_index ->
                                 Smallstep.state OpenC -> Smallstep.state OpenA -> Prop.
    Hypothesis fsim_skel : skel OpenC = skel OpenA.
    Hypothesis fsim_lts : forall (se1 se2 : Genv.symtbl) (wB : ccworld cc_c_asm_injp),
        GS.match_senv cc_c_asm_injp_new wB se1 se2 ->
        Genv.valid_for (skel OpenC) se1 ->
        GS.fsim_properties cc_c_asm_injp_new se1 se2 wB (OpenC se1) 
          (OpenA se2) fsim_index fsim_order (fsim_match_states se1 se2 wB).
    
    Hypothesis fsim_order_wf : well_founded fsim_order.

    (** Utilizing above properties *)
    
    Definition match_local_states := fsim_match_states se tse.

    Lemma SE_eq : se = tse.
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

    (* Definition worlds : Type := NatMap.t (option cc_cainjp_world). *)


    (** Global index *)

    Definition global_index : Type := list fsim_index.
    
    Inductive global_order : global_index -> global_index -> Prop :=
    |gorder_hd : forall fi1 fi2 tl, fsim_order fi1 fi2 -> global_order (fi1 :: tl) (fi2 :: tl)
    |gorder_tl : forall fi tl1 tl2, global_order tl1 tl2 -> global_order (fi :: tl1) (fi :: tl2).

    Theorem global_index_wf : well_founded global_order.
    Proof.
      red.
      eapply (well_founded_induction fsim_order_wf).
    Admitted. (** Should be correct, but how to prove...*)

        (** * Lemmas about nth_error. *)
    Fixpoint set_nth_error {A:Type} (l: list A) (n: nat) (a: A) : option (list A) :=
      match n with
      |O => match l with
           |nil => None
           |hd :: tl => Some (a :: tl)
           end
      |S n' => match l with
           |nil => None
              |hd :: tl => match (set_nth_error tl n' a) with
                         |Some tl' => Some (hd :: tl')
                         |None => None
                         end
              end
      end.

    Lemma set_nth_error_length : forall {A: Type} (l l' : list A) n a,
        set_nth_error l n a = Some l' ->
        length l' = length l.
    Proof.
      induction l; intros.
      - destruct n; simpl in H; inv H.
      - destruct n; simpl in H. inv H. reflexivity.
        destruct set_nth_error eqn:SET in H; inv H.
        simpl. erewrite IHl; eauto.
    Qed.

    Lemma get_nth_set : forall {A: Type} (n:nat) (l: list A) (a b: A),
        nth_error l n = Some a ->
        exists l', set_nth_error l n b = Some l'
              /\ nth_error l' n = Some b
              /\ forall n0 : nat, (n0 <> n)%nat -> nth_error l n0 = nth_error l' n0.
    Proof.
      induction n; intros.
      - destruct l. inv H. exists (b :: l).
        split. reflexivity. split. reflexivity. intros.
        destruct n0. extlia. reflexivity.
      - simpl in H. destruct l. inv H.
        specialize (IHn l a b H). destruct IHn as (l' & X & Y & Z).
        exists (a0 :: l'). repeat apply conj; eauto. simpl. rewrite X. reflexivity.
        intros. destruct n0. simpl. reflexivity. simpl. apply Z. lia.
    Qed.

    
    Lemma global_order_decrease : forall i i' li li' n,
        nth_error i n = Some li ->
        set_nth_error i n li' = Some i' ->
        fsim_order li' li ->
        global_order i' i.
    Admitted.
    
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
    Definition empty_gworlds : NatMap.t (option injp_world) := NatMap.init None.
    Definition initial_worlds (w: cc_cainjp_world) := NatMap.set 1%nat (Some w) empty_worlds.
    Definition initial_gworlds (w: injp_world) := NatMap.set 1%nat (Some w) empty_gworlds.
    Definition initial_indexs (i: fsim_index) := i :: nil.
    
    (** * We shall add more and more invariants about global states here *)

    (** Discuss : we may need to store [two] worlds for each thread, one is the
        initial wB, the another is for the latest (if exists) [yield], is the wA,
        waiting for replies related by wA's accessibility.

        The current world should be [legal] accessibility of all threads waiting
        at [yield()], therefore they can be resumed.

GS.fsim_lts.
     *)

   (** Maybe the thread_state needs to be further extended fsim_match_external *)
    Inductive match_thread_states : cc_cainjp_world -> (option cc_cainjp_world) -> injp_world -> fsim_index -> thread_state_C -> thread_state_A -> Prop :=
    |match_local : forall wB i sc sa wp,
        match_local_states wB wp i sc sa ->
        match_thread_states wB None wp i (CMulti.Local OpenC sc) (Local OpenA sa)
    |match_initial : forall wB i cqv rs m tm,
        match_query cc_c_asm_injp wB (get_query cqv m) (rs,tm) ->
        match_thread_states wB None (get wB)i (CMulti.Initial OpenC cqv) (Initial OpenA rs)
    |match_return : forall wB wA i sc sa wp wp'
        (M_STATES: match_local_states wB wp i sc sa)
        (WA_SIG : cajw_sg wA = yield_sig)
        (GET: get wA = wp')
        (ACC1: wp *-> wp')
        (M_REPLIES: forall r1 r2 sc' wp'',
            get wA o-> wp'' ->
            GS.match_reply cc_c_asm_injp_new (set wA wp'') r1 r2 ->
            (after_external (OpenC se)) sc r1 sc' ->
            exists i' sa', (after_external (OpenA tse)) sa r2 sa' /\
                        (exists wp''', wp'' *-> wp''' /\
                                    match_local_states wB wp''' i' sc' sa')),
        (* match_query cc_c_asm_injp w ( )-> *)
        (* query_is_yield OpenC qc ->
        query_is_yield_asm OpenA (rs, tm) ->
        match_query cc_c_asm_injp w qc (rs, tm) -> *)
        
        match_thread_states wB (Some wA) wp' i (CMulti.Return OpenC sc) (Return OpenA sa (cajw_rs wA)).

    Inductive match_states : global_index -> CMulti.state OpenC -> state OpenA -> Prop :=
    |global_match_intro : forall threadsC threadsA cur next worldsA worldsB worldsP gi w0 m0 main_b wPcur
      (CUR_VALID: (1 <= cur < next)%nat)
      (INDEX_LENGTH : length gi = (next -1)%nat)                      
      (INITMEM: Genv.init_mem (skel OpenC) = Some m0)
      (FINDMAIN: Genv.find_symbol se main_id = Some main_b)
      (INITW: w0 = init_w m0 main_b INITMEM)
      (INITVALID: forall cqv, ~ NatMap.get 1%nat threadsC = Some (CMulti.Initial OpenC cqv))
      (MAIN_THREAD_INITW: NatMap.get 1%nat worldsB = Some w0)
      (CUR_INJP_WORLD: NatMap.get cur worldsP = Some wPcur)
      (THREADS: forall n, (1 <= n < next)%nat -> exists wB owA wP lsc lsa i,
            NatMap.get n worldsB = Some wB /\
              nth_error gi (n-1)%nat = Some i /\
              injp_match_stbls (cajw_injp wB) se tse /\
              NatMap.get n threadsC = Some lsc /\
              NatMap.get n threadsA = Some lsa /\
              NatMap.get n worldsA = owA /\
              match_thread_states wB owA wP i lsc lsa /\
              NatMap.get n worldsP = Some wP /\
              (n <> cur -> injp_accg wP wPcur)
              ),
        match_states gi (mk_gstate OpenC threadsC cur next) (mk_gstate_asm OpenA threadsA cur next).

    Lemma foo {A: Type} (n: nat) (map : NatMap.t (option A)) (a b: A) :
      NatMap.get n map = Some a -> NatMap.get n map = Some b -> a = b.
    Proof.
      intros. congruence.
    Qed.

    Lemma concur_initial_states :
      forall s1, Closed.initial_state ConcurC s1 ->
            exists i s2, Closed.initial_state ConcurA s2 /\ match_states i s1 s2.
    Proof.
      intros. inv H.
        (* Genv.initmem_inject. *)
        apply Genv.initmem_inject in H1 as Hm0.
        exploit Genv.init_mem_genv_sup; eauto. intro SUP.
        (* set (j0 := Mem.flat_inj (Mem.support m0)).
        set (wj0 := injpw j0 m0 m0 Hm0). *)
        set (w0 := init_w m0 main_b H1). unfold init_w, wj0 in w0.
        generalize valid_se. intro VALID.
        simpl in fsim_lts.
        assert (MSE': injp_match_stbls (cajw_injp w0) se tse).
        constructor.  rewrite <- SE_eq. apply match_se_initial; eauto.
        unfold se, CMulti.initial_se. rewrite SUP. eauto with mem. rewrite <- SE_eq.
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
        eapply GS.fsim_match_initial_states in FSIM as FINI; eauto.
        destruct FINI as [i [ls2 [A B]]].
        exists (initial_indexs i). eexists. split.
        + econstructor. unfold AsmMulti.main_id, initial_se.
          unfold CMulti.initial_se, CMulti.main_id in H0.
          rewrite <- fsim_skel. eauto. rewrite <- fsim_skel. eauto.
          reflexivity.  eauto.
        + econstructor; eauto. intros. simpl. rewrite NatMap.gss. congruence.
          instantiate (3:= initial_worlds w0).
          instantiate (1:= H1). reflexivity.
          instantiate (2:= initial_gworlds (cajw_injp w0)). reflexivity.
          (* intros.
          simpl in H. unfold initial_gworlds in H. rewrite NatMap.gsspec in H.
          destruct NatIndexed.eq in H. inv H. reflexivity. inv H. *)
          instantiate (1:= empty_worlds). 
          intros.
          assert (n=1)%nat. lia. subst. 
          exists w0, None, (get w0), (CMulti.Local OpenC ls), (Local OpenA ls2), i.
          repeat apply conj; eauto. simpl.
          constructor. unfold match_local_states. eauto.
          congruence.
    Admitted. (** The Vunllptr issue *)

    Lemma concur_final_states: forall i s1 s2 r,
            match_states i s1 s2 -> Closed.final_state ConcurC s1 r -> Closed.final_state ConcurA s2 r.
    Proof.
      intros. inv H0. inv H.
        simpl in *. subst cur.
        unfold CMulti.get_cur_thread, CMulti.get_thread in H2. simpl in H2.
        specialize (THREADS 1%nat CUR_VALID).
        destruct THREADS as (wB & owA & wP & lsc & lsa & i' & GETWB & GETi & MSEw & GETC & GETA & GETWA & MS & GETP).
        assert (lsc = CMulti.Local OpenC ls).
        eapply foo; eauto. subst lsc. inv MS.
        specialize (fsim_lts se tse wB MSEw valid_se) as FSIM.
        inversion FSIM. unfold match_local_states in H6.
        exploit fsim_match_final_states. eauto.
        eauto. intros [r2 [FIN MR]]. destruct r2.
        inv MR.
        econstructor; eauto. admit. (*the same as initial*)
        simpl.
        assert (sg = main_sig).
        {
          rewrite GETWB in MAIN_THREAD_INITW.
          inv MAIN_THREAD_INITW. unfold set_injp in H.
          simpl in H. inv H.
          reflexivity.
        }
        subst. unfold tres in H8. simpl in H8.
        unfold Conventions1.loc_result, main_sig in H8. simpl in H8.
        destruct Archi.ptr64; simpl in H8. inv H8. eauto. inv H8. eauto.
    Admitted. (** The Vnullptr issue*)


    (** Seems straight forward *)
    Lemma local_plus : forall gs t sa1 sa2,
        Plus (OpenA tse) sa1 t sa2 ->
        NatMap.get (cur_tid OpenA gs) (threads OpenA gs)  = Some (Local OpenA sa1) ->
        plus (step OpenA) (globalenv OpenA) gs t (update_cur_thread OpenA gs (Local OpenA sa2)).
    Proof.
    Admitted.

    Lemma local_star : forall gs t sa1 sa2,
        Star (OpenA tse) sa1 t sa2 ->
        NatMap.get (cur_tid OpenA gs) (threads OpenA gs)  = Some (Local OpenA sa1) ->
        star (step OpenA) (globalenv OpenA) gs t (update_cur_thread OpenA gs (Local OpenA sa2)).
    Proof.
    Admitted.


    Lemma thread_create_inject : forall j m tm,
            Mem.inject j m tm ->
            Mem.inject j (Mem.thread_create m) (Mem.thread_create tm).
    Proof.
      intros. inv H. constructor; eauto.
      - inv mi_thread. simpl. red. unfold Mem.sup_create. simpl.
        rewrite !app_length. split; congruence.
      - clear - mi_inj.
        inv mi_inj. constructor; eauto.
      - intros. eapply mi_freeblocks. unfold Mem.valid_block in *.
        simpl in H.
        rewrite Mem.sup_create_in. eauto.
      - intros. unfold Mem.valid_block. simpl. rewrite <- Mem.sup_create_in.
        eapply mi_mappedblocks; eauto.
    Qed.

    Lemma yield_inject : forall j m tm n p tp,
        Mem.inject j m tm ->
        Mem.inject j (Mem.yield m n p) (Mem.yield tm n tp).
    Proof.
      intros. unfold Mem.yield. inv H.
      constructor; simpl; eauto.
      - inv mi_thread. simpl. unfold Mem.sup_yield. red. split; eauto.
      - inv mi_inj.
        constructor; eauto.
      - unfold Mem.valid_block. simpl.
        intros. rewrite <- Mem.sup_yield_in in H. eauto.
      - unfold Mem.valid_block. simpl.
        intros. rewrite <- Mem.sup_yield_in.
        eapply mi_mappedblocks; eauto.
    Qed.

   Inductive worlds_ptc_str : cc_cainjp_world -> cc_cainjp_world -> Prop :=
    | ptc_str_intro : forall j m tm Hm0 Hm1 rs,
        worlds_ptc_str
        (cajw (injpw j m tm Hm0) pthread_create_sig rs)
        (cajw (injpw j (Mem.thread_create m) (Mem.thread_create tm) Hm1) start_routine_sig (rs # PC <- (rs RDI) # RDI <- (rs RSI))).
        
    Lemma trans_pthread_create__start_routine: forall q_ptc q_str qa_ptc wA,
        query_is_pthread_create OpenC q_ptc q_str ->
        match_query cc_c_asm_injp wA q_ptc qa_ptc ->
        injp_match_stbls (cajw_injp wA) se tse ->
        exists wA' qa_str, query_is_pthread_create_asm OpenA qa_ptc qa_str /\
                        match_query cc_c_asm_injp wA' q_str qa_str /\
                        worlds_ptc_str wA wA'.
    Proof.
      intros until wA. intros H H0 MSE.
      inv H. inv H0.
      subst tvf targs. rewrite pthread_create_locs in H4. simpl in H4.
      inv H4. inv H9. inv H11. inv H3.
      set (rs' := rs # PC <- (rs RDI) # RDI <- (rs RSI)).
      assert (INJPTC: j b_ptc = Some (b_ptc, 0)).
      {
        inv MSE. inv H9.
        exploit mge_dom; eauto. eapply Genv.genv_symb_range. apply FINDPTC.
        intros (b3 & INJ).
        exploit mge_symb; eauto.
        intro HH. apply HH in FINDPTC as FINDPTC'.
        rewrite <- SE_eq in FINDPTC'. fold se in FINDPTC. setoid_rewrite FINDPTC in FINDPTC'.
        inv FINDPTC'. eauto.
      }
      assert (PC: rs PC = Vptr b_ptc Ptrofs.zero).
      inv H5. rewrite H9 in INJPTC. inv INJPTC. reflexivity.
      assert (INJSTR: j b_start = Some (b_start, 0)).
      {
        inv MSE. inv H9.
        exploit mge_dom; eauto. eapply Genv.genv_symb_range. apply FINDSTR. eauto.
        intros (b3 & INJ).
        exploit mge_symb; eauto.
        intro HH. apply HH in FINDSTR as FINDSTR'.
        rewrite <- SE_eq in FINDSTR'. fold se in FINDSTR. setoid_rewrite FINDSTR in FINDSTR'.
        inv FINDSTR'. eauto.
      }
      assert (RSI: rs RDI = Vptr b_start Ptrofs.zero).
      inv H2. rewrite H9 in INJSTR. inv INJSTR. reflexivity.
      exploit thread_create_inject; eauto.
      intros Hm1.
      exists (cajw (injpw j (Mem.thread_create m) (Mem.thread_create tm) Hm1) start_routine_sig rs').
      eexists. repeat apply conj.
      - fold se in FINDPTC. rewrite SE_eq in FINDPTC.
        fold se in FINDSTR. rewrite SE_eq in FINDSTR.
        econstructor. 
        eapply FINDPTC. eapply FINDSTR.  eauto. eauto. eauto.
        instantiate (1:= rs'). unfold rs'. rewrite Pregmap.gso. rewrite Pregmap.gss.
        eauto. congruence.
        unfold rs'. rewrite Pregmap.gss. eauto. eauto.
      -
        econstructor; eauto. rewrite start_routine_loc. simpl.
        constructor. unfold rs'. rewrite Pregmap.gss. rewrite <- H1.
        econstructor; eauto. constructor. unfold Conventions.size_arguments.
        rewrite start_routine_loc. simpl. intros. inv H. extlia.
        unfold rs'. repeat rewrite Pregmap.gso.
        subst tsp. inv H10. constructor. simpl. rewrite <- Mem.sup_create_in. auto.
        congruence. congruence.
        econstructor. unfold Conventions.tailcall_possible, Conventions.size_arguments.
        rewrite start_routine_loc. simpl. reflexivity. congruence.
      - constructor.
    Qed.

    (** Properties of yield strategy *)

    Lemma yield_range_c : forall gsc, (1 <= CMulti.yield_strategy OpenC gsc < (CMulti.next_tid OpenC gsc))%nat.
    Admitted.

    Lemma yield_range_asm : forall gsa, (1 <= yield_strategy OpenA gsa < (next_tid OpenA gsa))%nat.
    Admitted.

    Lemma yield_target_ms : forall i gsc gsa, match_states i gsc gsa ->
                                         CMulti.yield_strategy OpenC gsc = yield_strategy OpenA gsa.
    Admitted.

    (** maybe should be released, add a yield_to_self which is similar to pthread create *)
    Lemma yield_not_cur_c : forall gsc, CMulti.yield_strategy OpenC gsc <> (CMulti.cur_tid OpenC gsc).
    Admitted.

    Lemma yield_not_cur_asm : forall gsa, yield_strategy OpenA gsa <> (cur_tid OpenA gsa).
    Admitted.

      
    (** Properties need to be added in SIMCONV *)
    Lemma match_q_nid: forall qc qa w,
        GS.match_query cc_c_asm_injp_new w qc qa ->
        Mem.next_tid (Mem.support (cq_mem qc)) = Mem.next_tid (Mem.support (snd qa)).
    Admitted.



    
    Lemma match_senv_id : forall j b b' d id, Genv.match_stbls j se se ->
                                         j b = Some (b',d) ->
                                         Genv.find_symbol se id = Some b ->
                                         b' = b /\ d = 0.
    Proof.
      intros. inv H. split.
      exploit mge_symb; eauto. intro HH. apply HH in H1 as H2.
      setoid_rewrite H1 in H2. inv H2. eauto.
      exploit mge_dom; eauto. eapply Genv.genv_symb_range; eauto.
      intros [b2 A]. rewrite H0 in A. inv A. reflexivity.
    Qed.

    Lemma injp_accg_acci_accg : forall w1 w2 w3,
        injp_accg w1 w2 -> injp_acci w2 w3 -> injp_accg w1 w3.
    Proof.
      intros. destruct w1 as [j1 m1 tm1 Htm1]. destruct w2 as [j2 m2 tm2 Htm2].
      destruct w3 as [j3 m3 tm3 Htm3].
      inv H. inv H0. destruct H11 as [S11 H11]. destruct H12 as [S12 H12].
      destruct H18 as [[A B] H18]. destruct H19 as [[C D] H19].
      constructor; eauto.
      - eapply Mem.ro_unchanged_trans; eauto. inversion H11. eauto.
      - eapply Mem.ro_unchanged_trans; eauto. inversion H12. eauto.
      -  intros b ofs p Hb ?.
         eapply H9, H16; eauto using Mem.valid_block_unchanged_on.
      - intros b ofs p Hb ?.
        eapply H10, H17; eauto using Mem.valid_block_unchanged_on.
      - split. congruence.
        eapply mem_unchanged_on_trans_implies_valid; eauto.
        unfold loc_unmapped, Mem.thread_external_P. simpl.
        intros b1 _ [Hb Hb0] Hb1. split.
        destruct (j2 b1) as [[b2 delta] | ] eqn:Hb'; eauto.
        edestruct H14; eauto. contradiction. congruence.
      - split. congruence.
        eapply mem_unchanged_on_trans_implies_valid; eauto.
        unfold loc_out_of_reach, Mem.thread_external_P. simpl.
        intros b2 ofs2 [Hb2 Hb2'] Hv. split. intros b1 delta Hb'.
        destruct (j1 b1) as [[xb2 xdelta] | ] eqn:Hb.
        * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
            by (eapply H13 in Hb; split; congruence); subst.
        specialize (Hb2 b1 delta Hb). intro. apply Hb2.
        eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
        * edestruct H14; eauto.
        * congruence.
      - eapply inject_incr_trans; eauto.
      - intros b1 b2 delta Hb Hb''.
      destruct (j2 b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply H20 in Hb'; split; congruence); subst.
        eapply H14; eauto.
      * edestruct H21; eauto.
        intuition eauto using Mem.valid_block_unchanged_on.
    Qed.
    
    Theorem Concur_Sim : Closed.forward_simulation ConcurC ConcurA.
    Proof.
      econstructor. instantiate (3:= global_index). instantiate (2:= global_order).
      instantiate (1:= match_states).
      constructor. auto.
      - eapply global_index_wf.
      - eapply concur_initial_states.
      - eapply concur_final_states.
      - (* step *)
        intros. inv H.
        + (* Local *)
          inversion H0. subst. simpl in *.
          specialize (THREADS cur CUR_VALID) as THR_CUR.
          destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
          assert (lsc = CMulti.Local OpenC ls1).
          eapply foo; eauto. subst lsc. inv MS.
          specialize (fsim_lts se tse wB MSEw valid_se) as FSIM.
          inversion FSIM.
          clear fsim_match_initial_states
            fsim_match_final_states fsim_match_external.
          exploit fsim_simulation; eauto. intros (li' & s2' & STEP & wp' & GW_ACC & MATCH).
          specialize (get_nth_set (cur-1) i li li' GETi) as SETi.
          destruct SETi as (i' & SETi & Newi & OTHERi). exists i'.
          set (worldsP' := NatMap.set cur (Some wp') worldsP).
          destruct STEP.
          -- eexists. split. left.
             eapply local_plus; eauto. unfold update_cur_thread.
             {
               simpl. econstructor. simpl; eauto. simpl.
               erewrite set_nth_error_length; eauto. eauto.
               eauto.
               intros. destruct (Nat.eq_dec 1 cur). subst.
               rewrite NatMap.gss. congruence.
               rewrite NatMap.gso; eauto.
               eauto.
               instantiate (2:= worldsP'). simpl. unfold worldsP'.
               rewrite NatMap.gss. reflexivity.
               intros. instantiate (1:= worldsA).
               destruct (Nat.eq_dec n cur).
               - subst.
                 exists wB, None, wp', (CMulti.Local OpenC ls2), (Local OpenA s2'), li'.
                 repeat apply conj; eauto. rewrite NatMap.gss. reflexivity.
                 rewrite NatMap.gss. reflexivity. simpl. constructor. eauto.
                 unfold worldsP'. rewrite NatMap.gss. eauto. simpl. congruence.
               - (* clear - THREADS H3 OTHERi n0. *)
                 destruct (THREADS n H3) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
                 exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto. rewrite <- OTHERi; eauto. lia.
                 rewrite NatMap.gso. simpl. eauto. lia.
                 rewrite NatMap.gso. simpl. eauto. lia.
                 unfold worldsP'. rewrite NatMap.gso. simpl. eauto. lia.
                 assert (wP = wPcur). congruence. subst.
                 simpl. intros. specialize (J H5).
                 eapply injp_accg_acci_accg; eauto.
             }
          -- destruct H. eexists. split. right. split. eapply local_star; eauto.
             eapply global_order_decrease; eauto.
             {
               simpl. econstructor. simpl; eauto. simpl.
               erewrite set_nth_error_length; eauto.
               eauto. eauto.
               intros. destruct (Nat.eq_dec 1 cur). subst.
               rewrite NatMap.gss. congruence.
               rewrite NatMap.gso; eauto.
               eauto. instantiate (2:= worldsP'). simpl. unfold worldsP'.
               rewrite NatMap.gss. reflexivity.
               intros.
               destruct (Nat.eq_dec n cur).
               - subst.
                 exists wB, None, wp', (CMulti.Local OpenC ls2), (Local OpenA s2'), li'.
                 repeat apply conj; eauto. rewrite NatMap.gss. reflexivity.
                 rewrite NatMap.gss. reflexivity. simpl. constructor. eauto.
                 unfold worldsP'. rewrite NatMap.gss. reflexivity. simpl. congruence.
               - (* clear - THREADS H3 OTHERi n0. *)
                 destruct (THREADS n H5) as (wn & ownA & wp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
                 exists wn, ownA, wp, lscn,lsan,lin. repeat apply conj; eauto. rewrite <- OTHERi; eauto. lia.
                 rewrite NatMap.gso. simpl. eauto. lia.
                 rewrite NatMap.gso. simpl. eauto. simpl. lia.
                 unfold worldsP'. rewrite NatMap.gso. eauto. lia.
                 assert (wP = wPcur). congruence. subst.
                 simpl. intros. specialize (J H6).
                 eapply injp_accg_acci_accg; eauto.
             }
        + (* pthread_create *)
          inversion H0. subst.
          specialize (THREADS cur CUR_VALID) as THR_CUR.
          destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA &GETWa & MS & GETWp & ACC).
          assert (lsc = CMulti.Local OpenC ls).
          eapply foo; eauto. subst lsc. inv MS.
          specialize (fsim_lts se tse wB MSEw valid_se) as FSIM.
          inversion FSIM.
          clear fsim_match_initial_states
            fsim_match_final_states fsim_simulation.
          exploit fsim_match_external. eauto. eauto.
          intros (wA & qa_ptc & AT_PTC & wp' & APP & GET & MQ_PTC & MS & MR).
          exploit trans_pthread_create__start_routine; eauto.
          intros (wA'c & qa_str & PTR_TO_STR_ASM & MQ_STR & WORLDS).
          inv WORLDS.
          set (wP' := injpw j m tm Hm0).
          set (wA_ptc :=  {| cajw_injp := wP'; cajw_sg := pthread_create_sig; cajw_rs := rs |}).
          set (wP'' := injpw j (Mem.thread_create m) (Mem.thread_create tm) Hm1).
          assert (ACC2: injp_acce wP' wP'').
          {
            unfold wP', wP''.
            econstructor; try red; intros; eauto.
            - split. simpl. eauto.
              constructor. red. simpl. intros. rewrite <- Mem.sup_create_in. eauto.
              intros. simpl. reflexivity. intros. reflexivity.
            - split. simpl. eauto.
              constructor. red. simpl. intros. rewrite <- Mem.sup_create_in. eauto.
              intros. simpl. reflexivity. intros. reflexivity.
            - congruence.
          }
          set (wA_str := {|
             cajw_injp := wP'';
             cajw_sg := start_routine_sig;
             cajw_rs := (rs # PC <- (rs RDI)) # RDI <- (rs RSI) |}).
          destruct qa_str as [rs_qastr m_qastr].
          set (rs' := rs # PC <- (rs RA) # RAX <- (Vint Int.one)).
          set (ra_ptc := (rs', m_qastr)).
          inversion MQ_PTC. subst. inversion MQ_STR. subst.
          assert (MR_PTC : GS.match_reply cc_c_asm_injp_new (set wA_ptc wP'') (cr (Vint Int.one) (Mem.thread_create m)) ra_ptc).
          {
            econstructor. unfold Conventions1.loc_result. unfold pthread_create_sig.
            replace Archi.ptr64 with true by reflexivity. simpl. 
            unfold rs'. rewrite Pregmap.gss. constructor.
            intros. unfold rs'.
            destruct r; simpl in H; inv H; repeat rewrite Pregmap.gso;
              simpl; try congruence; try reflexivity.
            unfold rs'. repeat rewrite Pregmap.gso; try congruence.
            unfold rs'. rewrite Pregmap.gso; try congruence. rewrite Pregmap.gss. reflexivity.
            (* intros. unfold Conventions.size_arguments in H. rewrite pthread_create_locs in H.
            simpl in H. inv H. extlia. *)
          }
          exploit MR; eauto. intros (li' & lsa' & AFTERa & wP''' & ACC3 & MSla).
          specialize (get_nth_set (cur-1) i li li' GETi).
          intros (i' & SETi' & GETi' & OTHERi).
          set (i'' := i' ++ (li::nil)). (** li for new thread is useless, also no effect? hopefully*)
          exists i''. eexists. split.
          -- left. eapply plus_one.
             eapply step_thread_create; eauto. 
          -- simpl.
             set (worlds' := NatMap.set next (Some wA_str) worldsB).
             set (worldsP' := NatMap.set next (Some wP'') (NatMap.set cur (Some wP''') worldsP)).
             assert (LENGTHi'' :Datatypes.length i'' = next).
             unfold i''. rewrite app_length.
             simpl. erewrite set_nth_error_length; eauto. lia.
             econstructor. simpl. lia.
             simpl. lia.
             eauto. eauto. simpl. unfold get_cqv. simpl.
             intros. destruct (Nat.eq_dec 1 cur). subst.
               rewrite NatMap.gss. congruence.
               rewrite NatMap.gso; eauto.
               rewrite NatMap.gso. eauto. lia.
             instantiate (3:= worlds'). unfold worlds'.
             rewrite NatMap.gso. eauto. lia.
             simpl. instantiate (2:= worldsP').
             unfold worldsP'. rewrite NatMap.gso. rewrite NatMap.gss. reflexivity. lia.
             simpl. intros. destruct (Nat.eq_dec n next).
             ++ (* the new thread *) subst.
                instantiate (1:= NatMap.set (Datatypes.length i'') None worldsA).
               exists wA_str. exists None. exists wP''. eexists. eexists. eexists. repeat apply conj.
               unfold worlds'. rewrite NatMap.gss. reflexivity.
               unfold i''.
               rewrite nth_error_app2. rewrite app_length.
               simpl. replace (Datatypes.length i' + 1 - 1 - Datatypes.length i')%nat with 0%nat by lia.
               reflexivity. rewrite app_length. simpl. lia.
               simpl in MS. unfold wA_str. simpl.
               clear - MS. inv MS. constructor; eauto.
               red. intros. simpl. rewrite <- Mem.sup_create_in. eauto.
               red. intros. simpl. rewrite <- Mem.sup_create_in. eauto.
               rewrite NatMap.gso. rewrite NatMap.gss. reflexivity. lia.
               rewrite NatMap.gso. rewrite NatMap.gss. reflexivity. lia.
               rewrite NatMap.gss. reflexivity.
               econstructor.
               instantiate (1:= Mem.thread_create tm).
               instantiate (1:= Mem.thread_create m).
               unfold get_cqv, get_query. simpl. eauto.
               unfold worldsP'. rewrite NatMap.gss. reflexivity.
               admit. (** we should give the new thread a world such that has its own threadid in memory? check this again in yield_to_initial branch*)
             ++ destruct (Nat.eq_dec n cur).
          * (*the executing thread *) subst.
            exists wB, None, wP''', (CMulti.Local OpenC ls'),(Local OpenA lsa'), li'.
            repeat apply conj; eauto.
            unfold worlds'. rewrite NatMap.gso. eauto. lia.
            unfold i''. rewrite nth_error_app1. eauto. unfold i'' in CUR_VALID.
            rewrite app_length in CUR_VALID. simpl in CUR_VALID. lia.
            rewrite NatMap.gss. reflexivity.
            rewrite NatMap.gss. reflexivity.
            rewrite NatMap.gso. eauto. congruence.
            constructor. eauto.
            unfold worldsP'. rewrite NatMap.gso. rewrite NatMap.gss. reflexivity. lia.
            congruence.
          * (* uneffected threads *)
            assert (Hr: (1 <= n < next)%nat). lia.
            destruct (THREADS n Hr) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
            exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto.
            unfold worlds'. rewrite NatMap.gso. eauto. lia.
            unfold i''. rewrite nth_error_app1.
            rewrite <- OTHERi; eauto. lia. erewrite set_nth_error_length; eauto. lia.
            repeat rewrite NatMap.gso; eauto.
            repeat rewrite NatMap.gso; eauto.
            repeat rewrite NatMap.gso; eauto. congruence.
            unfold worldsP'. repeat rewrite NatMap.gso; eauto.
            assert (wP = wPcur). congruence. subst wP.
            intros. specialize (J H4). admit.
            (** this can be proved*)
        + (* yield_to_yield *)
          unfold Mem.range_prop in p. rename p into yield_range.
          set (target :=  CMulti.yield_strategy OpenC s1).
          assert ( NEXT_EQ: Mem.next_tid (Mem.support (cq_mem q)) = CMulti.next_tid OpenC s1).
          {
            inv H3. eauto.
          }
          inversion H0. subst.
          specialize (THREADS cur CUR_VALID) as THR_CUR.
          destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa& MS & GETWp & ACC).
          assert (wP = wPcur). congruence. subst.
          assert (lsc = CMulti.Local OpenC ls).
          eapply foo; eauto. subst lsc. inv MS.
          specialize (fsim_lts se tse wB MSEw valid_se) as FSIM.
          inversion FSIM.
          clear fsim_match_initial_states
            fsim_match_final_states fsim_simulation.
          exploit fsim_match_external. eauto. eauto.
          intros (w_CUR & qa & AT_YIE & wP' & ACC1 & GET & MQ_YIE & MS & MR).
          assert (TAR_VALID:(1 <= target < next)%nat).
          {
            eapply yield_range_c; eauto.
          }
          specialize (THREADS target TAR_VALID) as THR_TAR.
          destruct THR_TAR as (wBt & wAt & wPt & lscT & lsaT & liT & GETWT & GETiT & MSEwT & GETCT & GETAT & GETWaT & MST &GetWpT & ACCT).
          assert (lscT = (CMulti.Return OpenC) ls1).
          eapply foo; eauto. subst lscT. inv MST. rename wA into wAt.
          specialize (fsim_lts se tse wBt MSEwT valid_se) as FSIMt.
          inversion FSIMt.
          clear fsim_match_initial_states
            fsim_match_final_states fsim_simulation.
          assert (Mem.next_tid (Mem.support (cq_mem q)) = Mem.next_tid (Mem.support (snd qa))).
          eapply match_q_nid; eauto.
          assert (yield_range_a : (1 <=
                 yield_strategy OpenA
                   {| threads := threadsA; cur_tid := cur; next_tid := next |} <
                                     Mem.next_tid (Mem.support (snd qa)))%nat).
          {
            rewrite <- H4. rewrite NEXT_EQ. simpl.
            apply yield_range_asm.
          }
          assert (targeteq: target = yield_strategy OpenA
                                                    {| threads := threadsA; cur_tid := cur; next_tid := next |}).
          unfold target. eapply yield_target_ms; eauto.
          assert (targetdif : target <> cur). eapply yield_not_cur_c; eauto.
          subst. rewrite <- targeteq in *.
          fold target in H6, H7.
          destruct qa as [qy_rs qy_m].
          set (m_t := Mem.yield (cq_mem q) target yield_range).
          set (tm_t := Mem.yield (qy_m) target yield_range_a).
          set (rs' := (cajw_rs wAt) # PC <- ((cajw_rs wAt) RA)).
          inversion MQ_YIE. subst.
          assert (Hm_t: Mem.inject j m_t tm_t). eapply yield_inject; eauto.
          set (wP' := injpw j m qy_m Hm).
          simpl in ACC1.
          set (wP'' := injpw j m_t tm_t Hm_t).
          (* assert (ACC2: injp_acc wP' wP'').
          {
            constructor; try red; intros; eauto.
            split. simpl. 
            constructor; simpl; eauto.
            red. intros. rewrite <- Mem.sup_yield_in. auto.
            unfold Mem.yield, Mem.perm. simpl. intros. reflexivity.
            constructor; simpl; eauto.
            red. intros. rewrite <- Mem.sup_yield_in. auto.
            unfold Mem.yield, Mem.perm. simpl. intros. reflexivity.
            congruence.
          } *)
          assert (ACCE: injp_acce (get wAt) wP'').
          admit. (** NEED a LEMMA here*)
          assert (MATCH_YIELD_R: GS.match_reply cc_c_asm_injp_new (set wAt wP'') (cr Vundef m_t) (rs', tm_t)).
          {
            destruct wAt. simpl. unfold wP''.
            econstructor; eauto.
            intros. unfold rs'.
            destruct r; simpl in H; inv H; repeat rewrite Pregmap.gso;
              simpl; try congruence; try reflexivity.
          }
          exploit M_REPLIES. 2: eauto. eauto.
          eauto. simpl. 
          intros (liT' & sa' & AFTERa & wP''' & ACC3 & MSaT).
          specialize (get_nth_set (target-1) i liT liT' GETiT) as SETiT.
          destruct SETiT as (i' & SETiT & NewiT & OTHERiT). exists i'.
          eexists. split. left. apply plus_one.
          eapply step_thread_yield_to_yield.
           7: eauto.
          eauto. eauto.
          {
            (* clear - H3 MQ_YIE. *)
            inv MQ_YIE. inv H3. econstructor; eauto.
            instantiate (1:= b). fold tse. rewrite <- SE_eq. eauto.
            subst tvf. inv H12.
            exploit match_senv_id; eauto. inv MS. rewrite <- SE_eq in H19.
            eauto. intros [A B]. subst. reflexivity.
            simpl in H4. rewrite <- H4. simpl. eauto.
          }
          instantiate (1:= target). eauto. instantiate (1:= yield_range_a). reflexivity.
          unfold get_thread. simpl. eauto. reflexivity. reflexivity.
          (*match_states*)
          {
            unfold yield_state, yield_state_asm.
            rewrite <- targeteq. fold target. unfold CMulti.update_cur_tid, update_cur_tid.
            simpl. unfold CMulti.update_thread, update_thread. simpl.
            set (w_CUR := {| cajw_injp := injpw j m qy_m Hm; cajw_sg := sg; cajw_rs := qy_rs |} ).
            set (worldsA' := NatMap.set target None (NatMap.set cur (Some w_CUR) worldsA)).
            set (worldsP' := NatMap.set target (Some wP''') (NatMap.set cur (Some wP') worldsP)).
            econstructor. eauto. erewrite set_nth_error_length; eauto.
            eauto. eauto. simpl.
            intros. destruct (Nat.eq_dec 1 target).
            rewrite NatMap.gsspec, pred_dec_true. congruence. auto.
            rewrite NatMap.gso; eauto.
            destruct (Nat.eq_dec 1 cur). subst cur.
            rewrite NatMap.gss. congruence.
            rewrite NatMap.gso; eauto.
            eauto. instantiate (2:= worldsP').
            unfold worldsP'. rewrite NatMap.gss. reflexivity.
            intros.
            (** the invariants for each thread *)
            simpl. intros. destruct (Nat.eq_dec n target).
             ++ (* the target thread *) subst.
               instantiate (1:=  worldsA').
               exists wBt. exists None. eexists. eexists. eexists. eexists.
               repeat apply conj. eauto.
               eauto. eauto. rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity.
               unfold worldsA'. rewrite NatMap.gss. eauto.
               constructor. eauto.
               unfold worldsP'. rewrite NatMap.gss. reflexivity.
               congruence.
             ++ destruct (Nat.eq_dec n cur).
          * (*the executing thread *) subst.
            exists wB, (Some w_CUR). do 4 eexists. 
            repeat apply conj. eauto. 
            erewrite <- OTHERiT; eauto. lia. eauto.
            rewrite NatMap.gso. rewrite NatMap.gss. eauto. eauto.
            rewrite NatMap.gso. rewrite NatMap.gss. eauto. eauto.
            unfold worldsA'. rewrite NatMap.gso. rewrite NatMap.gss. eauto. eauto.
            econstructor. 3: reflexivity. eauto. inv H3. reflexivity.
            unfold w_CUR. simpl. eauto.
            eauto. unfold worldsP'.
            rewrite NatMap.gso. rewrite NatMap.gss. reflexivity. lia.
            intros. simpl. fold wP'. admit.
            (** need a lemma here *)

          * (* uneffected threads *)
            destruct (THREADS n H8) as (wn & owan & wpn & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
            exists wn, owan, wpn, lscn,lsan,lin. repeat apply conj; eauto.
            rewrite <- OTHERiT; eauto. lia.
            repeat rewrite NatMap.gso; eauto.
            repeat rewrite NatMap.gso; eauto.
            unfold worldsA'. repeat rewrite NatMap.gso; eauto.
            unfold worldsP'. repeat rewrite NatMap.gso; eauto.
            intros. specialize (J n1). admit.
          }
        + (** yield_to_initial *)
          unfold Mem.range_prop in p. rename p into yield_range.
          set (target :=  CMulti.yield_strategy OpenC s1).
          assert ( NEXT_EQ: Mem.next_tid (Mem.support (cq_mem q)) = CMulti.next_tid OpenC s1).
          { inv H3. simpl. eauto. }
          inversion H0. subst.
          specialize (THREADS cur CUR_VALID) as THR_CUR.
          destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC1).
          assert (wP = wPcur). congruence. subst.
          assert (lsc = CMulti.Local OpenC ls).
          eapply foo; eauto. subst lsc. inv MS.          
          specialize (fsim_lts se tse wB MSEw valid_se) as FSIM.
          inversion FSIM.
          clear fsim_match_initial_states
            fsim_match_final_states fsim_simulation.
          exploit fsim_match_external. eauto. eauto. clear ACC1.
          intros (w_CUR & qa & AT_YIE & wP' & ACC1 & GET & MQ_YIE & MS & MR).
          clear fsim_match_external.
          assert (TAR_VALID:(1 <= target < next)%nat). eapply yield_range_c; eauto.
          specialize (THREADS target TAR_VALID) as THR_TAR.
          destruct THR_TAR as (wBt & wAt & wPt & lscT & lsaT & liT & GETWT & GETiT & MSEwT & GETCT & GETAT & GETWaT & MST & GETWpT & ACCT).
          assert (lscT = CMulti.Initial OpenC cqv).
          eapply foo; eauto. subst lscT. inv MST.
          assert (Mem.next_tid (Mem.support (cq_mem q)) = Mem.next_tid (Mem.support (snd qa))).
          {
            eapply match_q_nid; eauto.
          }
          assert (yield_range_a : (1 <=
                 yield_strategy OpenA
                   {| threads := threadsA; cur_tid := cur; next_tid := next |} <
                                     Mem.next_tid (Mem.support (snd qa)))%nat).
           {
            rewrite <- H4. rewrite NEXT_EQ. simpl.
            apply yield_range_asm.
          }
          assert (targeteq: target = yield_strategy OpenA
                                                    {| threads := threadsA; cur_tid := cur; next_tid := next |}).
          unfold target. eapply yield_target_ms; eauto.
          assert (targetdif : target <> cur). eapply yield_not_cur_c; eauto.
          subst. rewrite <- targeteq in *.
          fold target in H6, H7.
          destruct qa as [qy_rs qy_m].
          set (m_t := Mem.yield (cq_mem q) target yield_range).
          set (tm_t := Mem.yield (qy_m) target yield_range_a).

          inversion MQ_YIE. subst.
          assert (Hm_t: Mem.inject j m_t tm_t). eapply yield_inject; eauto.
          set (wP' := injpw j m1 qy_m Hm).
          simpl in ACC1.
          set (wP'' := injpw j m_t tm_t Hm_t).
          (* assert (ACC2: injp_acc wP' wP'').
          {
            constructor; try red; intros; eauto.
            constructor; simpl; eauto.
            red. intros. rewrite <- Mem.sup_yield_in. auto.
            unfold Mem.yield, Mem.perm. simpl. intros. reflexivity.
            constructor; simpl; eauto.
            red. intros. rewrite <- Mem.sup_yield_in. auto.
            unfold Mem.yield, Mem.perm. simpl. intros. reflexivity.
            congruence.
          } *)
          set (w_CURt := set wBt wP'' ).
          assert (ACCT_CUR: injp_acc (get wBt) wP'').
          etransitivity. eauto. etransitivity. eauto. eauto.
          assert (MATCH_NEWQ: GS.match_query cc_c_asm_injp_new w_CURt (get_query cqv m_t) (rs, tm_t)
                              /\ GS.match_senv cc_c_asm_injp_new w_CURt se tse).
          {
            clear - H12 MS ACCT_CUR.
            destruct wBt.
            inv H12. unfold w_CURt. simpl.
            unfold get_query. simpl. split. subst tra tvf tsp0.
            inv ACCT_CUR.
            inv H15.
            - (* without stack_allocated argument *)
              red in H.
              econstructor; eauto.
              + (*initial arguments*)
                eapply outgoing_arguments_injp_valid; eauto.
              + intros. rewrite H in H0. simpl in H0. inv H0. extlia.
              + inv H14. constructor.
                inversion H19. eauto.
              + constructor. eauto.
            -
              apply Mem.free_range_perm in H0 as PERM.
              assert (PERMtm_t: Mem.range_perm tm_t sb (Mach.offset_sarg sofs 0)
                                  (Mach.offset_sarg sofs (Conventions.size_arguments (cqv_sg cqv))) Cur Freeable).
                {
                  red. red in PERM. intros.
                  assert (RANGE: Mach.loc_init_args (Conventions.size_arguments (cqv_sg cqv)) (rs RSP) sb ofs).
                  rewrite <- H. constructor; eauto.
                  specialize (H10 _ _ RANGE) as HH.
                  exploit PERM; eauto. intro PERMtm.
                  erewrite <- Mem.unchanged_on_perm; eauto. eauto with mem.
                }
                apply Mem.range_perm_free in PERMtm_t. destruct PERMtm_t as [tm_t' FREE].

              econstructor; eauto.
              + (*initial arguments*)
                eapply outgoing_arguments_injp_valid; eauto.
              + clear - H10 H7 H18 H20 H21 Hm6 Hm'1 H14.
                intros. specialize (H10 _ _ H).
                red in H10.
                red. intros.
                destruct (j0 b0) as [[b' d']|] eqn:Hj.
                -- erewrite H20 in H0; eauto. inv H0.
                   specialize (H10 _ _ Hj). intro. apply H10.
                   apply H7. inv Hm6. destruct (Mem.sup_dec b0 (Mem.support m)).
                   auto. exploit mi_freeblocks; eauto. intro. congruence.
                   unfold m_t in H0. unfold Mem.perm in H0. simpl in H0. eauto.
                -- exploit H21; eauto. intros [A B].
                   inv H. rewrite <- H1 in H14. inv H14.
                   exfalso. apply B. eauto.
              + inv H14. constructor.
                inversion H19. eauto.
              + rewrite <- H.
                eapply CallConv.args_removed_free; eauto.
                intros. exploit H3; eauto. intros [v LOAD].
                exists v. unfold Mach.load_stack in *. unfold Mem.loadv in *.
                unfold Val.offset_ptr in *.
                eapply Mem.load_unchanged_on; eauto.
                intros. eapply H10; eauto.
                rewrite <- H. econstructor.
                eapply argument_size_range; eauto.
            - inv MS. constructor. eauto.
              unfold m_t. unfold Mem.yield. simpl.
              red. intros. rewrite <- Mem.sup_yield_in. eauto.
              unfold tm_t. unfold Mem.yield. simpl.
              red. intros. rewrite <- Mem.sup_yield_in. eauto.
          }
          destruct MATCH_NEWQ as [MATCH_NEWQ MSt].
          specialize (fsim_lts se tse w_CURt MSt valid_se) as FSIMt.
          inversion FSIMt.
          clear fsim_match_external
            fsim_match_final_states fsim_simulation.
          simpl in *.
          exploit fsim_match_initial_states. eauto. eauto. eauto.
          intros (liT' & ls2' & INITIAL_A & MATCH_INI).
          specialize (get_nth_set (target-1) i liT liT' GETiT) as SETiT.
          destruct SETiT as (i' & SETiT & NewiT & OTHERiT). exists i'.
          eexists. split. left. apply plus_one.
          eapply step_thread_yield_to_initial.
          7: eauto.
          eauto. eauto.
          {
            (* clear - H3 MQ_YIE. *)
            inv MQ_YIE. inv H3. econstructor; eauto.
            instantiate (1:= b). fold tse. rewrite <- SE_eq. eauto.
            subst tvf. inv H13. exploit match_senv_id; eauto.
            inv MS. rewrite <- SE_eq in H20. eauto.
            intros [A B]. subst. reflexivity.
          }
          instantiate (1:= target). eauto. instantiate (1:= yield_range_a). reflexivity.
          eauto. reflexivity.
          (*match_states*)
          {
            unfold yield_state, yield_state_asm.
            rewrite <- targeteq. fold target. unfold CMulti.update_cur_tid, update_cur_tid.
            simpl. unfold CMulti.update_thread, update_thread. simpl.
            set (worldsB' := NatMap.set target (Some w_CURt) worldsB).
            set (w_CUR := {| cajw_injp := injpw j m1 qy_m Hm; cajw_sg := sg; cajw_rs := qy_rs |} ).
            set (worldsA' := NatMap.set cur (Some w_CUR) worldsA).
            set (worldsP' := NatMap.set target (Some wP'') (NatMap.set cur (Some wP') worldsP)).
            econstructor. eauto. erewrite set_nth_error_length; eauto.
            eauto. eauto. intros.
             intros. destruct (Nat.eq_dec 1 target).
            rewrite NatMap.gsspec, pred_dec_true. congruence. auto.
            rewrite NatMap.gso; eauto.
            destruct (Nat.eq_dec 1 cur). subst cur.
            rewrite NatMap.gss. congruence.
            rewrite NatMap.gso; eauto.
            instantiate (3:= worldsB'). unfold worldsB'.
            rewrite NatMap.gso. eauto. intro. congruence.
            instantiate (2:= worldsP'). unfold worldsP'.
            rewrite NatMap.gss. reflexivity.
            intros.
            (** the invariants for each thread *)
            simpl. intros. destruct (Nat.eq_dec n target).
             ++ (* the target thread *) subst.
               instantiate (1:=  worldsA').
               exists w_CURt. exists None. do 4 eexists. repeat apply conj.
               unfold worldsB'. rewrite NatMap.gss. reflexivity. eauto. eauto.
               rewrite NatMap.gss. reflexivity. rewrite NatMap.gss. reflexivity.
               unfold worldsA'. rewrite NatMap.gso. eauto. eauto.
               constructor. eauto.
               unfold worldsP'. rewrite NatMap.gss. unfold w_CURt.
               destruct wBt. simpl. reflexivity. unfold w_CURt.
               destruct wBt. reflexivity.
             ++ destruct (Nat.eq_dec n cur).
          * (*the executing thread *) subst.
            exists wB, (Some w_CUR). do 4  eexists. 
            repeat apply conj; eauto.
            unfold worldsB'. rewrite NatMap.gso. eauto. lia. 
            erewrite <- OTHERiT; eauto. lia.
            rewrite NatMap.gso. rewrite NatMap.gss. eauto. eauto.
            rewrite NatMap.gso. rewrite NatMap.gss. eauto. eauto.
            unfold worldsA'. rewrite NatMap.gss. eauto. 
            econstructor. eauto. inv H3. reflexivity. eauto. eauto. eauto.
            unfold worldsP'. rewrite NatMap.gso. rewrite NatMap.gss. reflexivity.
            lia.
          * (* uneffected threads *)
            destruct (THREADS n H5) as (wn & owan & wpn & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
            exists wn, owan, wpn, lscn,lsan,lin. repeat apply conj; eauto.
            unfold worldsB'. rewrite NatMap.gso. eauto. lia.
            rewrite <- OTHERiT; eauto. lia.
            repeat rewrite NatMap.gso; eauto.
            repeat rewrite NatMap.gso; eauto.
            unfold worldsA'. rewrite NatMap.gso. eauto. lia.
            unfold worldsP'. repeat rewrite NatMap.gso; eauto.
            etransitivity. eauto. etransitivity. eauto. eauto.
          }
Qed.

  End FSIM.

  Lemma SIM : GS.forward_simulation cc_c_asm_injp_new OpenC OpenA ->
    Closed.forward_simulation ConcurC ConcurA.
  Proof.
    intro. inv H. inv X. eapply Concur_Sim; eauto.
  Qed.

End ConcurSim.

Theorem Opensim_to_Globalsim : forall OpenC OpenA,
    GS.forward_simulation cc_c_asm_injp_new OpenC OpenA ->
    Closed.forward_simulation (Concur_sem_c OpenC) (Concur_sem_asm OpenA).
Proof.
  intros. eapply SIM; eauto.
Qed.
