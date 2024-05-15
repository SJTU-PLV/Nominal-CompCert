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
    |match_local : forall wB i sc sa wp
        (M_STATES: match_local_states wB wp i sc sa),
        match_thread_states wB None wp i (CMulti.Local OpenC sc) (Local OpenA sa)
    |match_initial : forall wB i cqv rs m tm
        (M_QUERIES: match_query cc_c_asm_injp wB (get_query cqv m) (rs,tm))
        (SG_STR: cqv_sg cqv = start_routine_sig),
        match_thread_states wB None (get wB)i (CMulti.Initial OpenC cqv) (Initial OpenA rs)
    |match_returny : forall wB wA i sc sa wp wp'
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
        match_thread_states wB (Some wA) wp' i (CMulti.Returny OpenC sc) (Returny OpenA sa (cajw_rs wA))
    |match_returnj : forall wB wA i sc sa wp wp' wait vptr int rs
        (RS: rs = cajw_rs wA)                     
        (M_STATES: match_local_states wB wp i sc sa)
        (WAIT: rs # RDI = Vint int /\ int_to_nat int = wait)
        (VPTR: Val.inject (injp_mi (cajw_injp wA)) vptr (rs # RSI))
        (WA_SIG : cajw_sg wA = pthread_join_sig)
        (GET: get wA = wp')
        (ACC1: wp *-> wp')
        (M_REPLIES: forall r1 r2 sc' wp'',
            get wA o-> wp'' ->
            GS.match_reply cc_c_asm_injp_new (set wA wp'') r1 r2 ->
            (after_external (OpenC se)) sc r1 sc' ->
            exists i' sa', (after_external (OpenA tse)) sa r2 sa' /\
                        (exists wp''', wp'' *-> wp''' /\
                                    match_local_states wB wp''' i' sc' sa')),
        match_thread_states wB (Some wA) wp' i (CMulti.Returnj OpenC sc wait vptr) (Returnj OpenA sa rs)
    |match_final_sub : forall wB wp i res tres
      (VRES: Val.inject (injp_mi wp) res tres),
      (* the signature for all sub threads are start_routine_sig *)
      match_thread_states wB None wp i (CMulti.Final OpenC res) (Final OpenA tres).


    Definition injp_tid (w: injp_world) : nat :=
     match w with injpw j m tm Hm => Mem.tid (Mem.support m) end.
                     
    Definition injp_nexttid (w: injp_world) : nat :=
      match w with injpw j m tm Hm => Mem.next_tid (Mem.support m) end.
    
    Inductive match_states : global_index -> CMulti.state OpenC -> state OpenA -> Prop :=
    |global_match_intro : forall threadsC threadsA cur next worldsA worldsB worldsP gi w0 m0 main_b wPcur
      (CUR_VALID: (1 <= cur < next)%nat)
      (INDEX_LENGTH : length gi = (next -1)%nat)                      
      (INITMEM: Genv.init_mem (skel OpenC) = Some m0)
      (FINDMAIN: Genv.find_symbol se main_id = Some main_b)
      (INITW: w0 = init_w m0 main_b INITMEM)
      (INITVALID: forall cqv, ~ NatMap.get 1%nat threadsC = Some (CMulti.Initial OpenC cqv))
      (MAIN_THREAD_INITW: NatMap.get 1%nat worldsB = Some w0)
      (SUB_THREAD_SIG: forall n wB, (n <> 1)%nat -> NatMap.get n worldsB = Some wB -> cajw_sg wB = start_routine_sig )
      (CUR_INJP_WORLD: NatMap.get cur worldsP = Some wPcur)
      (CUR_INJP_TID: cur = injp_tid wPcur /\ next = injp_nexttid wPcur)
      (FIND_TID: forall n wp, NatMap.get n worldsP = Some wp -> injp_tid wp = n)
      (THREADS_DEFAULT: fst threadsA = None)
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


    Lemma advance_next_tid : forall gl s s',
        Genv.advance_next gl s = s' ->
        Mem.tid s' = Mem.tid s.
    Proof.
      induction gl. intros.
      inv H. simpl. reflexivity.
      intros. simpl in H. apply IHgl in H. simpl in H. congruence.
    Qed.
      
    Lemma advance_next_nexttid : forall gl s s',
        Genv.advance_next gl s = s' ->
        Mem.next_tid s' = Mem.next_tid s.
    Proof.
      induction gl. intros.
      inv H. simpl. reflexivity.
      intros. simpl in H. apply IHgl in H. simpl in H.
      unfold Mem.next_tid in *. simpl in H. rewrite Mem.update_list_length in H.
      congruence.
    Qed.
                               
    Lemma init_mem_tid : forall sk m, Genv.init_mem sk = Some m ->
                                 Mem.tid (Mem.support m) = 1%nat.
    Proof.
      intros. unfold Genv.init_mem in H.
      apply Genv.alloc_globals_support in H.
      rewrite H. erewrite advance_next_tid; eauto. unfold Mem.empty.
      reflexivity.
    Qed.

    Lemma init_mem_nexttid : forall sk m, Genv.init_mem sk = Some m ->
                                     Mem.next_tid (Mem.support m) = 2%nat.
    Proof.
      intros. unfold Genv.init_mem in H.
      apply Genv.alloc_globals_support in H.
      rewrite H. erewrite advance_next_nexttid; eauto. unfold Mem.empty.
      reflexivity.
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
          intros. unfold initial_worlds in H3. rewrite NatMap.gso in H3.
          inv H3. auto.
          instantiate (2:= initial_gworlds (cajw_injp w0)). reflexivity.
          simpl. split. erewrite init_mem_tid; eauto.
          erewrite init_mem_nexttid; eauto.
          intros. simpl in H. unfold initial_gworlds in H.
          destruct (Nat.eq_dec n 1). subst. rewrite NatMap.gss in H.
          inv H. simpl. erewrite init_mem_tid; eauto.
          rewrite NatMap.gso in H. inv H. lia.
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
      inversion FSIM. unfold match_local_states in M_STATES.
      exploit fsim_match_final_states. eauto.
      eauto. intros [r2 [FIN [ACCE MR]]]. destruct r2.
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
      subst. unfold tres in H7. simpl in H7.
      unfold Conventions1.loc_result, main_sig in H7. simpl in H7.
      destruct Archi.ptr64; simpl in H7. inv H7. eauto. inv H7. eauto.
    Admitted. (** The Vnullptr issue*)


    (** Seems straight forward *)

    
    Lemma local_star : forall gs t sa1 sa2,
        Star (OpenA tse) sa1 t sa2 ->
        fst (threads OpenA gs) = None ->
        NatMap.get (cur_tid OpenA gs) (threads OpenA gs)  = Some (Local OpenA sa1) ->
        star (step OpenA) (globalenv OpenA) gs t (update_cur_thread OpenA gs (Local OpenA sa2)).
    Proof.
      intros. generalize dependent gs.
      induction H; intros.
      - unfold update_cur_thread, update_thread.
        destruct gs. simpl.
        rewrite NatMap.set3. eapply star_refl. eauto.
        simpl in H0. congruence.
      - eapply star_step; eauto.
        eapply step_local. eauto. eauto. eauto.
        set (gs' := (update_thread OpenA gs (cur_tid OpenA gs) (Local OpenA s2))).
        assert (EQ: update_cur_thread OpenA gs (Local OpenA s3) = update_cur_thread OpenA gs' (Local OpenA s3)).
        unfold gs'. unfold update_cur_thread. simpl. unfold update_thread.
        simpl. rewrite NatMap.set2. reflexivity.
        rewrite EQ.
        eapply IHstar; eauto.
        unfold gs'. simpl. rewrite NatMap.gss. reflexivity.
    Qed.        

    Lemma local_plus : forall gs t sa1 sa2,
        Plus (OpenA tse) sa1 t sa2 ->
        fst (threads OpenA gs) = None ->
        NatMap.get (cur_tid OpenA gs) (threads OpenA gs)  = Some (Local OpenA sa1) ->
        plus (step OpenA) (globalenv OpenA) gs t (update_cur_thread OpenA gs (Local OpenA sa2)).
    Proof.
      intros. inv H.
      econstructor; eauto.
      econstructor. eauto. eauto. eauto.
      set (gs' := update_thread OpenA gs (cur_tid OpenA gs) (Local OpenA s2)).
      assert (EQ: update_cur_thread OpenA gs (Local OpenA sa2) = update_cur_thread OpenA gs' (Local OpenA sa2)).
      unfold gs', update_cur_thread, update_thread. simpl. rewrite NatMap.set2.
      reflexivity.
      rewrite EQ.
      eapply local_star; eauto.
      unfold gs'. simpl. rewrite NatMap.gss. reflexivity.
    Qed.

    Lemma thread_create_inject : forall j m tm m' tm' id tid,
        Mem.inject j m tm ->
        Mem.thread_create m = (m', id) ->
        Mem.thread_create tm = (tm', tid) ->
        Mem.inject j m' tm' /\ id = tid.
    Proof.
      intros. inv H. inv H0. inv H1.
      split. constructor; eauto.
      - inv mi_thread. simpl. red.
        simpl. unfold Mem.sup_create. simpl.
        rewrite !app_length. split; congruence.
      - clear - mi_inj.
        inv mi_inj. constructor; eauto.
      - intros. eapply mi_freeblocks. unfold Mem.valid_block in *.
        simpl in H.
        rewrite Mem.sup_create_in. eauto.
      - intros. unfold Mem.valid_block. simpl. rewrite <- Mem.sup_create_in.
        eapply mi_mappedblocks; eauto.
      - inv mi_thread. unfold Mem.next_tid. eauto.
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


   Inductive injp_acc_thc : injp_world -> injp_world -> Prop :=
     injp_thread_create: forall j m1 m2 Hm m1' m2' Hm' id1 id2
         (Htc1: (m1', id1) = Mem.thread_create m1)
         (Htc2: (m2', id2) = Mem.thread_create m2),
         injp_acc_thc (injpw j m1 m2 Hm) (injpw j m1' m2' Hm').

   Inductive injp_acc_yield : injp_world -> injp_world -> Prop :=
     injp_yield : forall j m1 m2 (n: nat) p tp m1' m2' Hm Hm',
         m1' = Mem.yield m1 n p ->
         m2' = Mem.yield m2 n tp ->
         Mem.tid (Mem.support m1) <> n ->
         injp_acc_yield (injpw j m1 m2 Hm) (injpw j m1' m2' Hm').

   Inductive worlds_ptc_str : cc_cainjp_world -> cc_cainjp_world -> Prop :=
   | ptc_str_intro : forall j m tm id m' tm' Hm0 Hm1 rs
       (Htc1: (m', id) = Mem.thread_create m)
       (Htc2: (tm', id) = Mem.thread_create tm),
       worlds_ptc_str
         (cajw (injpw j m tm Hm0) pthread_create_sig rs)
         (cajw (injpw j m' tm' Hm1) start_routine_sig (rs # PC <- (rs RSI) # RDI <- (rs RDX))).
        
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
      inv H4. inv H9. inv H11. inv H5.
      set (rs' := rs # PC <- (rs RSI) # RDI <- (rs RDX)).
      assert (INJPTC: j b_ptc = Some (b_ptc, 0)).
      {
        inv MSE. inv H11.
        exploit mge_dom; eauto. eapply Genv.genv_symb_range. apply FINDPTC.
        intros (b3 & INJ).
        exploit mge_symb; eauto.
        intro HH. apply HH in FINDPTC as FINDPTC'.
        rewrite <- SE_eq in FINDPTC'. fold se in FINDPTC. setoid_rewrite FINDPTC in FINDPTC'.
        inv FINDPTC'. eauto.
      }
      assert (PCVAL: rs PC = Vptr b_ptc Ptrofs.zero).
      inv H1. rewrite H9 in INJPTC. inv INJPTC. reflexivity.
      assert (INJSTR: j b_start = Some (b_start, 0)).
      {
        inv MSE. inv H11.
        exploit mge_dom; eauto. eapply Genv.genv_symb_range. apply FINDSTR. eauto.
        intros (b3 & INJ).
        exploit mge_symb; eauto.
        intro HH. apply HH in FINDSTR as FINDSTR'.
        rewrite <- SE_eq in FINDSTR'. fold se in FINDSTR. setoid_rewrite FINDSTR in FINDSTR'.
        inv FINDSTR'. eauto.
      }
      assert (RSIVAL: rs RSI = Vptr b_start Ptrofs.zero).
      inv H3. rewrite H11 in INJSTR. inv INJSTR. reflexivity.
      case (Mem.thread_create tm) as [tm' id] eqn:MEM_CREATE'.
      exploit thread_create_inject; eauto. intros [Hm1 eqid]. subst id.
      assert (exists b_t' ofs_t', rs RDI = Vptr b_t' ofs_t').
      inv H2. eauto. destruct H as [b_t' [ofs_t' RDIVAL]].
      assert (exists b_arg' ofs_arg', rs RDX = Vptr b_arg' ofs_arg').
      inv H4. eauto. destruct H as [b_arg' [ofs_arg' RDXVAL]].
      exists (cajw (injpw j m' tm' Hm1) start_routine_sig rs').
      eexists. repeat apply conj.
      - fold se in FINDPTC. rewrite SE_eq in FINDPTC.
        fold se in FINDSTR. rewrite SE_eq in FINDSTR.
        econstructor.
        eapply FINDPTC. eapply FINDSTR. eauto. eauto. eauto. eauto.
        instantiate (1:= rs'). unfold rs'. rewrite Pregmap.gso. rewrite Pregmap.gss.
        eauto. congruence.
        unfold rs'. rewrite Pregmap.gss. eauto. eauto.
      -
        econstructor; eauto. rewrite start_routine_loc. simpl.
        constructor. unfold rs'. rewrite Pregmap.gss. eauto.
        constructor. unfold Conventions.size_arguments.
        rewrite start_routine_loc. simpl. intros. inv H. extlia.
        unfold rs'. repeat rewrite Pregmap.gso.
        subst tsp. inv H10. constructor. simpl.
        inv MEM_CREATE'. simpl.
        rewrite <- Mem.sup_create_in. auto.
        congruence. congruence.
        econstructor. unfold Conventions.tailcall_possible, Conventions.size_arguments.
        rewrite start_routine_loc. simpl. reflexivity. congruence.
      - econstructor; eauto.
    Qed.

    (* 
    (** Properties of yield strategy *)

    Lemma yield_range_c : forall gsc, (1 <= CMulti.yield_strategy OpenC gsc < (CMulti.next_tid OpenC gsc))%nat.

    Lemma yield_range_asm : forall gsa, (1 <= yield_strategy OpenA gsa < (next_tid OpenA gsa))%nat.

    Lemma yield_target_ms : forall i gsc gsa, match_states i gsc gsa ->
                                         CMulti.yield_strategy OpenC gsc = yield_strategy OpenA gsa.

    (** maybe should be released, add a yield_to_self which is similar to pthread create *)
    Lemma yield_not_cur_c : forall gsc, CMulti.yield_strategy OpenC gsc <> (CMulti.cur_tid OpenC gsc).

    Lemma yield_not_cur_asm : forall gsa, yield_strategy OpenA gsa <> (cur_tid OpenA gsa).
     *)
      
    Lemma match_q_nid: forall qc qa w,
        GS.match_query cc_c_asm_injp_new w qc qa ->
        Mem.next_tid (Mem.support (cq_mem qc)) = Mem.next_tid (Mem.support (snd qa)).
    Proof. intros. inv H. inv Hm. inv mi_thread.
           simpl. eauto.
    Qed.
    
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


    (** Lemma about different accessibility relations *)
    Lemma injp_acci_tid : forall w1 w2, injp_acci w1 w2 -> injp_tid w2 = injp_tid w1.
    Proof.
      intros. inv H. inv H4. simpl. inv unchanged_on_thread_i. auto.
    Qed.

    Lemma injp_acci_nexttid : forall w1 w2, injp_acci w1 w2 -> injp_nexttid w2 = injp_nexttid w1.
    Proof.
      intros. inv H. inv H4. simpl. inv unchanged_on_thread_i. auto.
    Qed.

     Lemma injp_acce_tid : forall w1 w2, injp_acce w1 w2 -> injp_tid w2 = injp_tid w1.
    Proof.
      intros. inv H. inv H4. simpl. auto.
    Qed.

    Lemma injp_acc_thc_tid : forall w1 w2, injp_acc_thc w1 w2 -> injp_tid w2 = injp_tid w1.
    Proof.
      intros. inv H.
      simpl. inv Htc1. reflexivity.
    Qed.

    Lemma injp_acc_thc_nexttid : forall w1 w2, injp_acc_thc w1 w2 -> injp_nexttid w2 = S (injp_nexttid w1).
    Proof.
      intros. inv H. simpl. unfold Mem.sup_create. unfold Mem.next_tid.
      inv Htc1. simpl. rewrite app_length. simpl. lia.
    Qed.

    Lemma injp_acc_yield_nexttid : forall w1 w2, injp_acc_yield w1 w2 -> injp_nexttid w2 = injp_nexttid w1.
    Proof.
      intros. inv H. simpl. eauto.
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

    Lemma injp_acc_yield_accg : forall w1 w2, injp_acc_yield w1 w2 -> injp_accg w1 w2.
    Proof.
      intros. inv H. 
      constructor; try red; intros; eauto.
      split. simpl. congruence.
      constructor; try red; intros; eauto.
      simpl. rewrite <- Mem.sup_yield_in; eauto.
      split. simpl. inv Hm.  inv mi_thread. congruence.
      constructor; try red; intros; eauto.
      simpl. rewrite <- Mem.sup_yield_in; eauto.
      congruence.
    Qed.
        
    Lemma pthread_create_accg1 : forall w1 w2 w3,
        injp_acc_yield w1 w2 -> injp_acci w1 w3 -> injp_accg w2 w3.
    Proof.
      intros. inv H.
      inv H0.
      assert (VALID1: forall b, Mem.valid_block m1 b <-> Mem.valid_block (Mem.yield m1 n p) b).
      intros. unfold Mem.valid_block. simpl. apply Mem.sup_yield_in.
      assert (VALID2: forall b, Mem.valid_block m2 b <-> Mem.valid_block (Mem.yield m2 n tp) b).
      intros. unfold Mem.valid_block. simpl. apply Mem.sup_yield_in.
      constructor; eauto.
      - red. intros. exploit H4; eauto. apply VALID1. auto.
      - red. intros. exploit H5; eauto. apply VALID2. eauto.
      - red. intros. exploit H6; eauto. apply VALID1. auto.
      - red. intros. exploit H7; eauto. apply VALID2. auto.
      - destruct H8 as [S8 H8]. inv S8. split. simpl. congruence.
        inv H8. constructor.
        + red. intros. eauto. apply unchanged_on_support. apply VALID1. auto.
        + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m1 b ofs k p0).
          reflexivity. eapply unchanged_on_perm; eauto.
          red. split. auto. simpl in B. congruence. apply VALID1. auto.
        + intros b ofs [A B] Hp. simpl.
          eapply unchanged_on_contents; eauto. split. auto. simpl in B. congruence.
      - destruct H9 as [S9 H9]. inv S9. apply Mem.mi_thread in Hm as Hs. destruct Hs as [X Y].
        split. simpl. congruence.
        inv H9. constructor.
        + red. intros. eauto. apply unchanged_on_support. apply VALID2. auto.
        + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m2 b ofs k p0).
          reflexivity. eapply unchanged_on_perm; eauto.
          red. split. auto. simpl in B. congruence. apply VALID2. auto.
        + intros b ofs [A B] Hp. simpl.
          eapply unchanged_on_contents; eauto. split. auto. simpl in B. congruence.
      - red. intros. rewrite <- VALID1, <- VALID2. eauto.
    Qed.

    Lemma thread_create_inject' : forall j m1 m2,
        Mem.inject j m1 m2 -> exists m1' m2' tid,
          Mem.thread_create m1 = (m1', tid) /\
          Mem.thread_create m2 = (m2', tid) /\
            Mem.inject j m1' m2'.
    Proof.
      intros.
      case (Mem.thread_create m1) as [m1' id1] eqn:H1.
      case (Mem.thread_create m2) as [m2' id2] eqn:H2.
      exploit thread_create_inject; eauto.
      intros [X Y]. subst. exists m1', m2', id2. split; eauto.
    Qed.
    
   Lemma pthread_create_accg2 : forall w1 w2 w3 w4 w5,
       injp_accg w1 w2 -> injp_acci w2 w3 -> injp_acc_thc w3 w4 ->
       injp_acci w4 w5 ->
       injp_accg w1 w5.
   Proof.
     intros. eapply injp_accg_acci_accg.
     2: eauto.
     exploit injp_accg_acci_accg. eauto. eauto.
     intro. clear - H1 H3.
     inv H1. inv H3.
     assert (VALID1: forall b, Mem.valid_block m1 b <-> Mem.valid_block m1' b).
     intros. unfold Mem.valid_block. inv Htc1. simpl. apply Mem.sup_create_in.
     assert (VALID2: forall b, Mem.valid_block m2 b <-> Mem.valid_block m2' b).
     intros. unfold Mem.valid_block. inv Htc2. simpl. apply Mem.sup_create_in.
     inv Htc1. inv Htc2. simpl in *.
     constructor; eauto.
     - destruct H7 as [S7 H7]. split. simpl. congruence.
       inv H7. constructor.
       + red. intros. apply VALID1. eapply unchanged_on_support; eauto.
       + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m1 b ofs k p0).
         eapply unchanged_on_perm; eauto.
         red. split; auto. simpl. reflexivity.
       + intros b ofs [A B] Hp. simpl.
         eapply unchanged_on_contents; eauto. split; auto.
      - destruct H9 as [S9 H9]. apply Mem.mi_thread in Hm as Hs. destruct Hs as [X Y].
        split. simpl. congruence.
        inv H9. constructor.
        + red. intros. eauto. apply VALID2. apply unchanged_on_support. auto.
        + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m2 b ofs k p0).
          eapply unchanged_on_perm; eauto.
          red. split; auto. reflexivity.
        + intros b ofs [A B] Hp. simpl.
          eapply unchanged_on_contents; eauto. split; auto.
   Qed.

   Lemma yield_to_yield_acce: forall w1 w2 w3 w4,
       injp_accg w1 w2 -> injp_acci w2 w3 -> injp_acc_yield w3 w4 ->
       injp_tid w4 = injp_tid w1 -> injp_acce w1 w4.
   Proof.
     intros. exploit injp_accg_acci_accg; eauto. intro.
     clear H H0. inv H3. inv H1. simpl in H2.
     assert (VALID1: forall b, Mem.valid_block m1' b <-> Mem.valid_block (Mem.yield m1' n p) b).
     intros. unfold Mem.valid_block. simpl. apply Mem.sup_yield_in.
     assert (VALID2: forall b, Mem.valid_block m2' b <-> Mem.valid_block (Mem.yield m2' n tp) b).
     intros. unfold Mem.valid_block. simpl. apply Mem.sup_yield_in.
     apply Mem.mi_thread in Hm as Hmi. destruct Hmi as [X Y].
     constructor; eauto.
     - destruct H6 as [S6 H6]. split. simpl. congruence.
        inv H6. constructor.
        + red. intros.  apply VALID1. apply unchanged_on_support. auto.
        + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m1' b ofs k p0).
          eapply unchanged_on_perm; eauto.
          red. split. auto. congruence. reflexivity.
        + intros b ofs [A B] Hp. simpl.
          eapply unchanged_on_contents; eauto. split. auto. auto.
      - destruct H7 as [S7 H7]. 
        split. simpl. congruence.
        inv H7. constructor.
        + red. intros. apply VALID2. apply unchanged_on_support. auto.
        + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m2 b ofs k p0).
          reflexivity. eapply unchanged_on_perm; eauto.
          red. split. auto. simpl in B. congruence.
        + intros b ofs [A B] Hp. simpl.
          eapply unchanged_on_contents; eauto. split; auto.
   Qed.

   Lemma yield_to_yield_accg1 : forall w1 w2 w3,
       injp_acc_yield w1 w2 -> injp_acci w2 w3 -> injp_accg w1 w3.
   Proof.
     intros. inv H. inv H0.
     assert (VALID1: forall b, Mem.valid_block m1 b <-> Mem.valid_block (Mem.yield m1 n p) b).
     intros. unfold Mem.valid_block. simpl. apply Mem.sup_yield_in.
     assert (VALID2: forall b, Mem.valid_block m2 b <-> Mem.valid_block (Mem.yield m2 n tp) b).
     intros. unfold Mem.valid_block. simpl. apply Mem.sup_yield_in.
     apply Mem.mi_thread in Hm as Hmi. destruct Hmi as [X Y].
     constructor; eauto.
     - red. intros. exploit H4; eauto. apply VALID1. auto.
     - red. intros. exploit H5; eauto. apply VALID2. eauto.
     - red. intros. exploit H6; eauto. apply VALID1. auto.
     - red. intros. exploit H7; eauto. apply VALID2. auto.
     - destruct H8 as [S8 H8]. inv S8. simpl in H0. split. simpl. congruence.
       inv H8. constructor.
       + red. intros. eauto. apply unchanged_on_support. apply VALID1. auto.
       + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m1 b ofs k p0).
         reflexivity. eapply unchanged_on_perm; eauto.
         red. split. auto. simpl in B. simpl. congruence. apply VALID1. auto.
       + intros b ofs [A B] Hp. simpl.
         eapply unchanged_on_contents; eauto. split. auto. simpl in B. simpl. congruence.
     - destruct H9 as [S9 H9]. inv S9. apply Mem.mi_thread in Hm as Hs. destruct Hs as [Z Z'].
       split. simpl in *. congruence.
       inv H9. constructor.
       + red. intros. eauto. apply unchanged_on_support. apply VALID2. auto.
       + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m2 b ofs k p0).
         reflexivity. eapply unchanged_on_perm; eauto.
         red. split. auto. simpl in *. congruence. apply VALID2. auto.
       + intros b ofs [A B] Hp. simpl.
         eapply unchanged_on_contents; eauto. split. auto. simpl in *. congruence.
     - red. intros. rewrite VALID1,VALID2. eauto.
   Qed.



   Lemma injp_accg_yield_accg : forall w1 w2 w3,
       injp_accg w1 w2 -> injp_acc_yield w2 w3 ->
       injp_tid w3 <> injp_tid w1 ->
       injp_accg w1 w3.
   Proof.
     intros. rename H1 into Hid. inv H0. inv H.
     assert (VALID1: forall b, Mem.valid_block m1 b <-> Mem.valid_block (Mem.yield m1 n p) b).
     intros. unfold Mem.valid_block. simpl. apply Mem.sup_yield_in.
     assert (VALID2: forall b, Mem.valid_block m2 b <-> Mem.valid_block (Mem.yield m2 n tp) b).
     intros. unfold Mem.valid_block. simpl. apply Mem.sup_yield_in.
     apply Mem.mi_thread in Hm as Hmi. destruct Hmi as [X Y]. simpl in Hid.
     constructor; eauto.
     - destruct H8 as [S8 H8]. split. simpl. congruence.
       inv H8. constructor.
       + red. intros. apply VALID1. apply unchanged_on_support. auto.
       + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m1 b ofs k p0).
         eapply unchanged_on_perm; eauto.
         red. split; auto. reflexivity.
       + intros b ofs [A B] Hp. simpl.
         eapply unchanged_on_contents; eauto. split; auto.
     - destruct H10 as [S10 H10]. split. apply Mem.mi_thread in Hm0 as Hs. destruct Hs as [Z Z'].
       simpl in *. congruence.
       inv H10. constructor.
       + red. intros. apply VALID2. apply unchanged_on_support. auto.
       + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m2 b ofs k p0).
         eapply unchanged_on_perm; eauto.
         red. split; auto. reflexivity.
       + intros b ofs [A B] Hp. simpl.
         eapply unchanged_on_contents; eauto. split; auto.
   Qed.
   
   Lemma yield_to_yield_accg2 : forall w1 w2 w3 w4 w5,
       injp_accg w1 w2 -> injp_acci w2 w3 -> injp_acc_yield w3 w4 -> injp_acci w4 w5 ->
       injp_tid w4 <> injp_tid w1 ->
       injp_accg w1 w5.
   Proof.
     intros. eapply injp_accg_acci_accg. 2: eauto.
     eapply injp_accg_yield_accg.
     eapply injp_accg_acci_accg; eauto. eauto. eauto.
   Qed.
   
   Lemma yield_to_initial_accg1 : forall w1 w2,
       injp_acc_yield w1 w2 -> injp_accg w1 w2.
   Proof.
     apply injp_acc_yield_accg.
   Qed.
   
   Lemma yield_to_initial_accg2 : forall w1 w2 w3 w4,
       injp_accg w1 w2 -> injp_acci w2 w3 -> injp_acc_yield w3 w4 ->
       injp_tid w4 <> injp_tid w1 ->
       injp_accg w1 w4.
   Proof.
     intros. eapply injp_accg_yield_accg.
     eapply injp_accg_acci_accg; eauto. eauto. eauto.
   Qed.

   Lemma substep_switch_out : forall i s1 s2 s1' target gmem',
       match_states i s1 s2 ->
       CMulti.switch_out OpenC s1 s1' target gmem' -> exists s2' gtmem',
           AsmMulti.switch_out OpenA s2 s2' target gtmem' /\
             match_states i s1' s2'.
   Proof.
     intros until gmem'. intros MS SWITCH.
     inv MS.
     inv SWITCH.
     - (* yield *)
       specialize (THREADS cur CUR_VALID) as THR_CUR.
       destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
       assert (lsc = CMulti.Local OpenC ls).
       eapply foo; eauto. subst lsc. inv MS.
       specialize (fsim_lts se tse wB MSEw valid_se) as FSIM.
       inversion FSIM.
       clear fsim_simulation fsim_match_initial_states
            fsim_match_final_states.
       exploit fsim_match_external; eauto. intros (wA & [rs_q tm_q] & HX & wp' & GW_ACC & GETwp & MQ & MS & MR).
       assert (wP = wPcur). congruence. subst wP.
       assert (tp : Mem.range_prop target (Mem.support(tm_q))).
         red. red in p. inv MQ. simpl in p. inv Hm0.
         inv mi_thread. setoid_rewrite <- H. auto.
         set (tm' := Mem.yield tm_q target tp).
       eexists. exists tm'. split.
       + (*step*)
         eapply switch_out_yield. eauto. eauto.
         { inv Q_YIE. inv MQ. red in MS. inv MS.
           econstructor. fold tse. rewrite <- SE_eq. eauto.
           subst tvf. inv H9.
           rewrite <- SE_eq in H5.
           exploit match_senv_id. eauto. apply H6. eauto. intros [X Y].
           subst b delta. reflexivity.
           simpl. simpl in H1. inv Hm0. inv mi_thread. unfold Mem.next_tid. auto.
         }
         reflexivity.
         reflexivity.
       + (*match_states*)
         apply injp_acci_nexttid in GW_ACC as NTID. apply injp_acci_tid in GW_ACC as TID.
         econstructor. 8:{ instantiate (2:= NatMap.set cur (Some wp') worldsP). rewrite NatMap.gss. reflexivity. }.
         all : simpl; eauto.
         -- simpl. intros. destruct (Nat.eq_dec 1 cur).
            subst. rewrite NatMap.gss. congruence.
            rewrite NatMap.gso; eauto.
         -- destruct CUR_INJP_TID. split; congruence.
         -- destruct CUR_INJP_TID.
            intros. destruct (Nat.eq_dec n cur). subst. rewrite NatMap.gss in H2. inv H2.
            apply TID. eapply FIND_TID. rewrite NatMap.gso in H2. eauto. eauto.
         -- intros.
            instantiate (1:= NatMap.set cur (Some wA) worldsA).
            destruct (Nat.eq_dec n cur).
            ++ subst n.
               exists wB, (Some wA), wp'. eexists. eexists. exists li.
               repeat apply conj; eauto. rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity. rewrite NatMap.gss. reflexivity.
               simpl. simpl in wp'. assert (HRS: rs_q = cajw_rs wA). inv MQ. reflexivity.
               rewrite HRS.
               eapply match_returny; eauto. inv Q_YIE. inv MQ. eauto. simpl in MR. simpl.
               setoid_rewrite GETwp. eauto.
               rewrite NatMap.gss. eauto. simpl. congruence.
            ++ (* clear - THREADS H3 OTHERi n0. *)
               destruct (THREADS n H) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto.
               rewrite NatMap.gso. simpl. eauto. lia.
               rewrite NatMap.gso. simpl. eauto. lia.
               rewrite NatMap.gso. simpl. eauto. lia.
               rewrite NatMap.gso. simpl. eauto. lia.
               simpl. intros. specialize (J H1).
               eapply injp_accg_acci_accg; eauto.
     - (** join *)
       specialize (THREADS cur CUR_VALID) as THR_CUR.
       destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
       assert (lsc = CMulti.Local OpenC ls).
       eapply foo; eauto. subst lsc. inv MS.
       specialize (fsim_lts se tse wB MSEw valid_se) as FSIM.
       inversion FSIM.
       clear fsim_simulation fsim_match_initial_states
            fsim_match_final_states.
       exploit fsim_match_external; eauto. intros (wA & [rs_q tm_q] & HX & wp' & GW_ACC & GETwp & MQ & MS & MR).
       assert (wP = wPcur). congruence. subst wP.
       inv Q_JOIN. inv MQ. red in MS. inv MS.
       subst targs tvf.
       setoid_rewrite pthread_join_locs in H6. simpl in H6.
       inv H6. inv H17. inv H18.
       assert (HPC: rs_q PC = Vptr b_ptj Ptrofs.zero).
       inv H7. rewrite <- SE_eq in H3. exploit match_senv_id; eauto. intros [X Y].
       subst b2 delta. reflexivity.
       assert (HRDI: rs_q RDI = Vint i0). inv H4. eauto.
       assert (HRSI: exists b_vptr' ofs_vptr', rs_q RSI = Vptr b_vptr' ofs_vptr').
       inv H5. eauto. destruct HRSI as [b_vptr' [ofs_vptr' HRSI]].
       assert (tp : Mem.range_prop target (Mem.support(tm_q))).
       red. red in p. simpl in p. inv Hm0.
       inv mi_thread. setoid_rewrite <- H. auto.
       set (tm' := Mem.yield tm_q target tp).
       eexists. exists tm'. split.
       + (*step*)
         eapply switch_out_join. eauto. eauto.
         econstructor; eauto.
         fold tse. rewrite <- SE_eq. eauto. eauto. reflexivity. reflexivity.
       + (*match_states*)
         apply injp_acci_nexttid in GW_ACC as NTID. apply injp_acci_tid in GW_ACC as TID.
         set (wA := {| cajw_injp := injpw j m tm_q Hm; cajw_sg := pthread_join_sig; cajw_rs := rs_q |}).
         set (wp' := injpw j m tm_q Hm). simpl in *.
         econstructor. 8:{ instantiate (2:= NatMap.set cur (Some wp') worldsP). rewrite NatMap.gss. reflexivity. }.
         all : simpl; eauto.
         -- simpl. intros. destruct (Nat.eq_dec 1 cur).
            subst. rewrite NatMap.gss. congruence.
            rewrite NatMap.gso; eauto.
         -- destruct CUR_INJP_TID. split; congruence.
         -- destruct CUR_INJP_TID.
            intros. destruct (Nat.eq_dec n cur). subst. rewrite NatMap.gss in H2. inv H2.
            apply TID. eapply FIND_TID. rewrite NatMap.gso in H2. eauto. eauto.
         -- intros.
            instantiate (1:= NatMap.set cur (Some wA) worldsA).
            destruct (Nat.eq_dec n cur).
            ++ subst n.
               exists wB, (Some wA), wp'. eexists. eexists. exists li.
               repeat apply conj; eauto. rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity. rewrite NatMap.gss. reflexivity.
               simpl. simpl in wp'. assert (HRS: rs_q = cajw_rs wA). reflexivity.
               rewrite HRS.
               eapply match_returnj; eauto. simpl.
               rewrite NatMap.gss. eauto. simpl. congruence.
            ++ (* clear - THREADS H3 OTHERi n0. *)
               destruct (THREADS n H) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto.
               rewrite NatMap.gso. simpl. eauto. lia.
               rewrite NatMap.gso. simpl. eauto. lia.
               rewrite NatMap.gso. simpl. eauto. lia.
               rewrite NatMap.gso. simpl. eauto. lia.
               simpl. intros. specialize (J H1).
               eapply injp_accg_acci_accg; eauto.
     - (** final *)
       specialize (THREADS cur CUR_VALID) as THR_CUR.
       destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
       assert (lsc = CMulti.Local OpenC ls).
       eapply foo; eauto. subst lsc. inv MS.
       specialize (fsim_lts se tse wB MSEw valid_se) as FSIM.
       inversion FSIM.
       clear fsim_simulation fsim_match_initial_states fsim_match_external.
       exploit fsim_match_final_states; eauto.
       intros ([rs_r tm_r] & FINAL' & GW_ACC_BIG & MR).
       assert (wP = wPcur). congruence. subst wP.
       assert (tp : Mem.range_prop target (Mem.support(tm_r))).
       red. red in p. simpl in p. inv MR. inv Hm'0.
       inv mi_thread. setoid_rewrite <- H1. auto.
       set (tm' := Mem.yield tm_r target tp).
       eexists. exists tm'. split.
       + (*step*)
         eapply switch_out_final. eauto. eauto. eauto. reflexivity. eauto.
         econstructor; eauto. reflexivity.
       + (*match_states*)
         simpl in *.
         econstructor; simpl; eauto.
         -- intros. destruct (Nat.eq_dec 1 cur).
            subst. rewrite NatMap.gss. congruence.
            rewrite NatMap.gso. eauto. eauto.
         -- intros.
            instantiate (1:= worldsA). 
            destruct (Nat.eq_dec n cur).
            ++ subst n.
               exists wB, None. eexists. eexists. eexists. exists li.
               repeat apply conj; eauto. rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity.
               eapply match_final_sub.
               inv MR.
               exploit SUB_THREAD_SIG; eauto. intro wBsig.
               destruct wB. inv H1. simpl in *. subst tres.
               setoid_rewrite wBsig in H6.
               unfold Conventions1.loc_result in H6. replace Archi.ptr64 with true in H6.
               simpl in H6. eauto. eauto.
            ++ (* clear - THREADS H3 OTHERi n0. *)
               destruct (THREADS n H) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto.
               rewrite NatMap.gso. simpl. eauto. lia.
               rewrite NatMap.gso. simpl. eauto. lia.
   Qed.

   Lemma substep_switch_in : forall i s1' s2' s1'' target gmem' gtmem',
            (*sth more about gtmem'*)
            match_states i s1' s2' ->
            CMulti.switch_in OpenC s1' s1'' target gmem' -> exists s2'',
            AsmMulti.switch_in OpenA s2' s2'' target gtmem' /\
              match_states i s1'' s2''.
   Proof.
   Admitted.
   
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
          assert (wP = wPcur). congruence. subst.
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
               destruct CUR_INJP_TID. simpl. split.
               erewrite injp_acci_tid; eauto.
               erewrite injp_acci_nexttid; eauto.
               {
                 exploit FIND_TID. eauto. intro.
                 erewrite <- injp_acci_tid in H4. 2: eauto.
                 clear - FIND_TID H4.
                 intros. unfold worldsP' in H.
                 destruct (Nat.eq_dec cur n). subst. rewrite NatMap.gss in H.
                 inv H. eauto.
                 rewrite NatMap.gso in H. eapply FIND_TID; eauto. lia.
               }
               intros. simpl. eauto.
               intros. instantiate (1:= worldsA).
               destruct (Nat.eq_dec n cur).
               - subst.
                 exists wB, None, wp', (CMulti.Local OpenC ls2), (Local OpenA s2'), li'.
                 repeat apply conj; eauto. rewrite NatMap.gss. reflexivity.
                 rewrite NatMap.gss. reflexivity. simpl. constructor. eauto.
                 unfold worldsP'. rewrite NatMap.gss. eauto.
                 simpl. congruence.
               - (* clear - THREADS H3 OTHERi n0. *)
                 destruct (THREADS n H4) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
                 exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto. rewrite <- OTHERi; eauto. lia.
                 rewrite NatMap.gso. simpl. eauto. lia.
                 rewrite NatMap.gso. simpl. eauto. lia.
                 unfold worldsP'. rewrite NatMap.gso. simpl. eauto. lia.
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
               destruct CUR_INJP_TID. simpl. split.
               erewrite injp_acci_tid; eauto.
               erewrite injp_acci_nexttid; eauto.
                {
                 exploit FIND_TID. eauto. intro.
                 erewrite <- injp_acci_tid in H5. 2: eauto.
                 clear - FIND_TID H5.
                 intros. unfold worldsP' in H.
                 destruct (Nat.eq_dec cur n). subst. rewrite NatMap.gss in H.
                 inv H. eauto.
                 rewrite NatMap.gso in H. eapply FIND_TID; eauto. lia.
                }
                simpl. eauto.
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
          set (wP'' := injpw j m' tm' Hm1).
          assert (wP = wPcur). congruence. subst wP.
          assert (ACC2: injp_acce wP' wP'').
          {
            inv Htc1. inv Htc2.
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
          destruct qa_str as [rs_qastr m_qastr].
          set (rs' := rs # PC <- (rs RA) # RAX <- (Vint Int.one)).
          set (ra_ptc := (rs', m_qastr)).
          inversion MQ_PTC. subst. inversion MQ_STR. subst.
          assert (MR_PTC : GS.match_reply cc_c_asm_injp_new (set wA_ptc wP'') (cr (Vint Int.one) m') ra_ptc).
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
          set (i'' := i' ++ (li::nil)).
          (** li for new thread is useless, also no effect? hopefully*)

          (*create world for new thread*)
          assert (NEXTTID: Mem.next_tid (Mem.support m) = next /\
                             Mem.next_tid (Mem.support tm) = next).
          {
            clear - CUR_INJP_TID APP.
            destruct CUR_INJP_TID as [_ Y].
            simpl in APP. apply injp_acci_nexttid in APP.
            rewrite <- Y in APP. unfold injp_nexttid in APP.
            split. auto. inv Hm0. inv mi_thread. setoid_rewrite <- H.
            eauto.
          }
          assert (p : Mem.range_prop next (Mem.support m')).
          destruct NEXTTID as [X Y].
          red. split. lia.
          inv Htc1. simpl. unfold Mem.sup_create, Mem.next_tid. simpl.
          rewrite app_length. simpl. lia.
          assert (tp : Mem.range_prop next (Mem.support m_qastr)).
          destruct NEXTTID as [X Y].
          red. split. lia. inv Htc2.
          simpl. unfold Mem.sup_create, Mem.next_tid. simpl.
          rewrite app_length. simpl. setoid_rewrite <- Y. unfold Mem.next_tid. lia.
          set (nm := Mem.yield m' next p).
          set (ntm := Mem.yield m_qastr next tp).
          specialize (yield_inject j m' m_qastr next p tp Hm1) as Hm1'.
          set (wP''n := injpw j nm ntm Hm1').
          assert (ACCY: injp_acc_yield wP'' wP''n).
          unfold wP'', wP''n. econstructor. reflexivity. reflexivity. simpl.
          apply injp_acci_tid in APP. simpl in APP. inv Htc1. simpl. rewrite APP.
          destruct CUR_INJP_TID as [Z _]. lia.
          set (wA_str := {|
             cajw_injp := wP''n;
             cajw_sg := start_routine_sig;
             cajw_rs := (rs # PC <- (rs RSI)) # RDI <- (rs RDX) |}).
          assert (ACCT: injp_acc_thc wP' wP'').
          unfold wP', wP''. econstructor; eauto.
          simpl.
          exists i''. eexists. split.
          -- left. eapply plus_one.
             eapply step_thread_create; eauto. 
          -- simpl.
             set (worlds' := NatMap.set next (Some wA_str) worldsB).
             set (worldsP' := NatMap.set next (Some wP''n) (NatMap.set cur (Some wP''') worldsP)).
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
             destruct CUR_INJP_TID as [A B].
             simpl. split. erewrite injp_acci_tid. 2: eauto.
             erewrite injp_acc_thc_tid. 2: eauto.
             erewrite injp_acci_tid; eauto.
             erewrite injp_acci_nexttid. 2: eauto.
             erewrite injp_acc_thc_nexttid. 2: eauto.
             f_equal. erewrite injp_acci_nexttid; eauto.
             {
               unfold worldsP'.
               exploit FIND_TID. eauto. intro TIDC.
               intros. destruct (Nat.eq_dec n next).
               - subst. rewrite NatMap.gss in H. inv H.
                 simpl. reflexivity. 
               - rewrite NatMap.gso in H. 2:lia.
                 destruct (Nat.eq_dec n cur).
                 subst. rewrite NatMap.gss in H. inv H.
                 erewrite injp_acci_tid. 2: eauto.
                 erewrite injp_acc_thc_tid. 2: eauto.
                 erewrite injp_acci_tid; eauto.
                 rewrite NatMap.gso in H. inv H.
                 eapply FIND_TID; eauto. lia.
             }
             simpl. eauto. simpl. intros. destruct (Nat.eq_dec n next).
             ++ (* the new thread *) subst.
                instantiate (1:= NatMap.set (Datatypes.length i'') None worldsA).
               exists wA_str. exists None. exists wP''n. eexists. eexists. eexists. repeat apply conj.
               unfold worlds'. rewrite NatMap.gss. reflexivity.
               unfold i''.
               rewrite nth_error_app2. rewrite app_length.
               simpl.
               replace (Datatypes.length i' + 1 - 1 - Datatypes.length i')%nat with 0%nat by lia.
               reflexivity. rewrite app_length. simpl. lia.
               simpl in MS. unfold wA_str. simpl.
               clear - MS Htc1 Htc2. inv MS. constructor; eauto.
               red. intros. inv Htc1. simpl. 
               rewrite <- Mem.sup_yield_in, <- Mem.sup_create_in. eauto.
               red. intros. inv Htc2. simpl.
               rewrite <- Mem.sup_yield_in, <- Mem.sup_create_in. eauto.
               rewrite NatMap.gso. rewrite NatMap.gss. reflexivity. lia.
               rewrite NatMap.gso. rewrite NatMap.gss. reflexivity. lia.
               rewrite NatMap.gss. reflexivity. 
               econstructor.
               instantiate (1:= ntm).
               instantiate (1:= nm).
               unfold get_cqv, get_query. simpl. 
               unfold wA_str, wP''n. simpl. econstructor; eauto.
               fold tsp1. unfold ntm.
               eapply Mach.valid_blockv_support. eauto.
               red. intros. simpl. erewrite <- Mem.sup_yield_in. auto.
               econstructor. unfold Conventions.tailcall_possible.
               unfold Conventions.size_arguments. rewrite start_routine_loc.
               simpl. lia.
               reflexivity.
               unfold worldsP'. rewrite NatMap.gss. reflexivity.
               intros.
               eapply pthread_create_accg1; eauto.
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
            intros. specialize (J H5).
            eapply pthread_create_accg2; eauto.
        + (** step_switch *)
          rename s1' into s1''. rename s' into s1'.
          (*
            Lemma substep_switch_out : forall i s1 s2 s1',
            match_states i s1 s2 ->
            CMulti.switch_out OpenC s1 s1' target gmem' -> exists s2' gtmem',
            AsmMulti.switch_out OpenA s2 s2' target gtmem' /\
            match_states i s1' s2'.
            (*sth more*)
           *)
          assert (exists s2' gtmem', AsmMulti.switch_out OpenA s2 s2' target gtmem' /\ match_states i s1' s2').
          eapply substep_switch_out; eauto.
          destruct H as [s2' [gtmem' [A B]]].
          (*
            Lemma substep_switch_in : forall i s1' s2' s1'' gmem',
            (*sth more about gtmem'*)
            match_states i s1' s2' ->
            CMulti.switch_in OpenC s1' s2'' target gmem' -> exists s2'',
            AsmMulti.switch_in OpenA s2' s2'' target gtmem' /\
            match_states i s1'' s2''.
          *)
          assert (exists s2'', AsmMulti.switch_in OpenA s2' s2'' target gtmem' /\ match_states i s1'' s2'').
          eapply substep_switch_in; eauto.
          destruct H as [s2'' [C D]].
          exists i, s2''. split. left. eapply plus_one. eapply step_switch; eauto. eauto.
Qed.
(*            
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
            rewrite <- H. rewrite NEXT_EQ. simpl.
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
          assert (ACCY: injp_acc_yield wP' wP'').
          {
            econstructor. reflexivity. reflexivity.
            simpl. fold target.
            apply injp_acci_tid in ACC1. simpl in ACC1.
            rewrite ACC1. destruct CUR_INJP_TID as [Z _]. lia.
          }
          assert (ACCE: injp_acce (get wAt) wP'').
          eapply yield_to_yield_acce; eauto.
          unfold wP''. simpl.
          exploit FIND_TID. apply GetWpT. intro. setoid_rewrite H8.
          reflexivity.
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
            subst tvf. inv H11.
            exploit match_senv_id; eauto. inv MS. rewrite <- SE_eq in H18.
            eauto. intros [A B]. subst. reflexivity.
            simpl in H. rewrite <- H. simpl. eauto.
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
            {
              split. erewrite injp_acci_tid. 2: eauto.
              unfold wP''. simpl. reflexivity.
              erewrite injp_acci_nexttid. 2: eauto.
              erewrite injp_acc_yield_nexttid. 2: eauto.
              erewrite injp_acci_nexttid; eauto.
              apply CUR_INJP_TID.
            }
            {
               unfold worldsP'.
               exploit FIND_TID. eauto. intro TIDC.
               intros n wp0 X. destruct (Nat.eq_dec n target).
               - subst. rewrite NatMap.gss in X. inv X.
                 erewrite injp_acci_tid. 2: eauto.
                 unfold wP''. simpl. reflexivity.
               - rewrite NatMap.gso in X. 2:lia.
                 destruct (Nat.eq_dec n cur).
                 subst. rewrite NatMap.gss in X. inv X.
                 erewrite injp_acci_tid. 2: eauto. eauto.
                 rewrite NatMap.gso in X. inv X.
                 eapply FIND_TID; eauto. lia.
             }
            intros.
            (** the invariants for each thread *)
            simpl. eauto. simpl. intros. destruct (Nat.eq_dec n target).
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
            intros. simpl. fold wP'.
            eapply yield_to_yield_accg1; eauto.
          * (* uneffected threads *)
            destruct (THREADS n H8) as (wn & owan & wpn & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
            exists wn, owan, wpn, lscn,lsan,lin. repeat apply conj; eauto.
            rewrite <- OTHERiT; eauto. lia.
            repeat rewrite NatMap.gso; eauto.
            repeat rewrite NatMap.gso; eauto.
            unfold worldsA'. repeat rewrite NatMap.gso; eauto.
            unfold worldsP'. repeat rewrite NatMap.gso; eauto.
            intros. specialize (J n1).
            eapply yield_to_yield_accg2; eauto.
            simpl. erewrite FIND_TID. 2: eauto. lia.
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
            rewrite <- H. rewrite NEXT_EQ. simpl.
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
          assert (ACCY: injp_acc_yield wP' wP'').
          {
            econstructor. reflexivity. reflexivity.
            simpl. fold target.
            apply injp_acci_tid in ACC1. simpl in ACC1.
            rewrite ACC1. destruct CUR_INJP_TID as [Z _]. lia.
          }
          set (w_CURt := set wBt wP'' ).
          assert (ACCT_CUR: injp_accg (get wBt) wPcur).
          eapply ACCT. lia. fold wP' in ACC1.
          assert (MATCH_NEWQ: GS.match_query cc_c_asm_injp_new w_CURt (get_query cqv m_t) (rs, tm_t)
                              /\ GS.match_senv cc_c_asm_injp_new w_CURt se tse).
          {
            clear - M_QUERIES SG_STR MS ACCT_CUR ACC1 ACCY.
            destruct wBt.
            inv M_QUERIES. unfold w_CURt. simpl.
            unfold get_query. simpl. split. subst tra tvf tsp0.
            rewrite SG_STR in *.
            inv H14.
            assert (Z: inject_incr j0 j /\ Mem.sup_include (Mem.support tm1) (Mem.support tm_t)).
            inv ACCT_CUR. inv ACC1. inv ACCY.
            split. eapply inject_incr_trans; eauto.
            eapply Mem.sup_include_trans. destruct H14 as [_ Y]. inv Y.
            apply unchanged_on_support. eapply Mem.sup_include_trans.
            destruct H27 as [_ Z]. inv Z. apply unchanged_on_support.
            unfold tm_t. simpl. red. intros.
            rewrite <- Mem.sup_yield_in. eauto.
            destruct Z as [INJINCR SUPI].
            - (* without stack_allocated argument *)
              red in H.
              econstructor; eauto.
              + (*initial arguments*)
                subst targs. rewrite SG_STR in H8.
                rewrite start_routine_loc in *. simpl in *.
                eauto.
              + intros. rewrite H in H0. simpl in H0. inv H0. extlia.
              + eapply Mach.valid_blockv_support; eauto.
              + constructor. eauto.
            - clear - H2. exfalso.
              unfold Conventions.size_arguments in H2.
              rewrite start_routine_loc in H2. simpl in H2. extlia.
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
            subst tvf. inv H11. exploit match_senv_id; eauto.
            inv MS. rewrite <- SE_eq in H18. eauto.
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
             {
              split.
              unfold wP''. simpl. reflexivity.
              erewrite injp_acc_yield_nexttid. 2: eauto. eauto.
            }
            {
               unfold worldsP'.
               exploit FIND_TID. eauto. intro TIDC.
               intros n wp0 X. destruct (Nat.eq_dec n target).
               - subst. rewrite NatMap.gss in X. inv X.
                 unfold wP''. simpl. reflexivity.
               - rewrite NatMap.gso in X. 2:lia.
                 destruct (Nat.eq_dec n cur).
                 subst. rewrite NatMap.gss in X. inv X.
                 erewrite injp_acci_tid. 2: eauto. eauto.
                 rewrite NatMap.gso in X. inv X.
                 eapply FIND_TID; eauto. lia.
             }
            intros.
            (** the invariants for each thread *)
            simpl. eauto. simpl. intros. destruct (Nat.eq_dec n target).
             ++ (* the target thread *) subst.
               instantiate (1:=  worldsA').
               exists w_CURt. exists None. do 4 eexists. repeat apply conj.
               unfold worldsB'. rewrite NatMap.gss. reflexivity. eauto. eauto.
               rewrite NatMap.gss. reflexivity. rewrite NatMap.gss. reflexivity.
               unfold worldsA'. rewrite NatMap.gso. eauto. eauto.
               constructor. eauto.
               unfold worldsP'. rewrite NatMap.gss. unfold w_CURt.
               destruct wBt. simpl. reflexivity. unfold w_CURt.
               destruct wBt. congruence.
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
            intros. simpl. fold wP'.
            eapply yield_to_initial_accg1; eauto.
          * (* uneffected threads *)
            destruct (THREADS n H8) as (wn & owan & wpn & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
            exists wn, owan, wpn, lscn,lsan,lin. repeat apply conj; eauto.
            unfold worldsB'. rewrite NatMap.gso. eauto. lia.
            rewrite <- OTHERiT; eauto. lia.
            repeat rewrite NatMap.gso; eauto.
            repeat rewrite NatMap.gso; eauto.
            unfold worldsA'. rewrite NatMap.gso. eauto. lia.
            unfold worldsP'. repeat rewrite NatMap.gso; eauto.
            intros. specialize (J n1).
            eapply yield_to_initial_accg2; eauto.
            simpl. erewrite FIND_TID. 2: eauto. lia.
          }
    Qed.
*)





    

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
