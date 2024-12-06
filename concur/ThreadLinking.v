Require Import Coqlib Errors Events Globalenvs Ctypes AST Memory Values Integers Asm.
Require Import LanguageInterface.
Require Import Smallstep SmallstepClosed.
Require Import ValueAnalysis.
Require Import MultiLibs CMulti AsmMulti.
Require Import Extends InjectFootprint CA.
Require Import CallconvBig Ext Injp CAnew Composition.



    
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

  (** * Get the concurrent semantics *)

  Let ConcurC := Concur_sem_c OpenC.
  Let ConcurA := Concur_sem_asm OpenA.

  (** * Initialization *)
  Let se := CMulti.initial_se OpenC.
  Let tse := initial_se OpenA.

  Section FSIM.

  (* Hypothesis OpenSim : GS.forward_simulation cc_compcert OpenC OpenA. *)
  (* Variable fsim_comp : GS.fsim_components cc_compcert OpenC OpenA. *)
    
    Variable fsim_index : Type.
    Variable fsim_order : fsim_index -> fsim_index -> Prop.
    Variable fsim_match_states : Genv.symtbl -> Genv.symtbl -> GS.ccworld cc_compcert -> GS.gworld cc_compcert -> fsim_index ->
                                 Smallstep.state OpenC -> Smallstep.state OpenA -> Prop.
    Hypothesis fsim_skel : skel OpenC = skel OpenA.
    Hypothesis fsim_lts : forall (se1 se2 : Genv.symtbl) (wB : GS.ccworld cc_compcert),
        GS.match_senv cc_compcert wB se1 se2 ->
        Genv.valid_for (skel OpenC) se1 ->
        GS.fsim_properties cc_compcert se1 se2 wB (OpenC se1) 
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
    |gorder_intro : forall hd tl li1 li2,
        fsim_order li1 li2 ->
        global_order (hd ++ (li1 :: tl)) (hd ++ (li2 :: tl)).

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


    Lemma nth_error_split {A: Type} : forall n (a: A) (l : list A),
        nth_error l n = Some a ->
        exists hd tl, l = hd ++ (a :: tl) /\ length hd = n.
    Proof.
      induction n; intros.
      - destruct l. simpl in H. inv H.
        simpl in H. inv H. exists nil. exists l. split. reflexivity. eauto.
      - simpl in H. destruct l. inv H.
        apply IHn in H. destruct H as [hd [tl [C B]]].
        exists (a0 :: hd), tl. split. simpl. rewrite C. simpl. reflexivity.
        simpl. lia.
    Qed.

    Lemma set_nth_error_split {A: Type} : forall n (a a':A) (l l' hd tl: list A),
        set_nth_error l n a' = Some l' ->
        l = hd ++ (a :: tl) ->
        length hd = n ->
        l' = hd ++ (a' :: tl).
    Proof.
      induction n; intros.
      - destruct l; simpl in H. inv H.
        inv H. inv H0. simpl. destruct hd. simpl in *. inv H2. eauto.
        inv H1.
      - destruct l; simpl in H. inv H.
        destruct (set_nth_error l n a') eqn:HS; inv H.
        destruct hd. inv H1. simpl in H1. simpl in H0.
        inv H0.
        exploit IHn. apply HS. reflexivity. lia.
        intros. rewrite H. reflexivity.
    Qed.

    Lemma global_order_decrease : forall i i' li li' n,
        nth_error i n = Some li ->
        set_nth_error i n li' = Some i' ->
        fsim_order li' li ->
        global_order i' i.
    Proof.
      intros. assert (exists hd tl, i = hd ++ (li::tl) /\ length hd = n).
      eapply nth_error_split; eauto.
      destruct H2 as [hd [tl [Heqi Hl]]].
      assert (Heqi': i' = hd ++ (li' :: tl)).
      eapply set_nth_error_split; eauto.
      rewrite Heqi, Heqi'.
      constructor. eauto.
    Qed.

    
   (** prove the well_founded property of global_order*)

   Inductive global_order_n : nat -> global_index -> global_index -> Prop :=
   |gon_intro : forall n i1 i2 li1 li2 hd tl,
       length i1 = n -> fsim_order li1 li2 ->
       i1 = hd ++ (li1 :: tl) -> i2 = hd ++ (li2 :: tl) ->
       global_order_n n i1 i2.

   Lemma go_length : forall n i, length i = n ->
                            Acc global_order i <-> Acc (global_order_n n) i.
   Proof.
     intros. split; intro.
     - induction H0. constructor. intros. apply H1.
       inv H2. constructor. auto. inv H2. auto.
     - induction H0. constructor. intros. apply H1.
       inv H2. econstructor; eauto. rewrite !app_length.
       simpl. lia. inv H2. rewrite !app_length. simpl. lia.
   Qed.

   Lemma global_order_n_wf: forall n,
       well_founded (global_order_n n).
   Proof.
     induction n.
     - red. intros. constructor. intros. inv H.
       destruct hd; simpl in H0; extlia.
     - red. destruct a.
       constructor. intros. inv H. destruct hd; inv H3.
       rename a into l. rename f into a.
       revert a l.
       induction a using (well_founded_induction fsim_order_wf).
       set (Q := fun l => Acc (global_order_n (S n)) (a::l)).
       apply well_founded_induction with (R:= (global_order_n n))(P:=Q). auto.
       intros. unfold Q. unfold Q in H0.
       constructor. intros. inv H1. destruct hd; simpl in *.
       + inv H5. apply H. auto.
       + inv H5. apply H0. econstructor; eauto.
   Qed.

   Lemma well_founed_go' : forall n i, length i = n -> Acc global_order i.
   Proof.
     intros. rewrite go_length; eauto. apply global_order_n_wf.
   Qed.

   Theorem global_index_wf : well_founded global_order.
   Proof.
     red. intros. eapply well_founed_go'; eauto.
   Qed.

   (** This lemma should be moved to and proved in ValueAnalysis.v.
       I'm 95% sure it's correct. Maybe we can somehow reuse the initialization
       proofs in ValueAnalysis for this. Or slightly change the definition of
       ro_sound_memory using existential [bc] if this approach is more ligheweight. *)

   (** This lemma should also be part of the DR with closed simulation and behavior
       refinement. We should refer the loading process proposed in CompCertOE *)      
   Lemma initial_romatch : forall skel m0,
       Genv.init_mem skel = Some m0 ->
       Genv.symboltbl skel = se ->
       ValueDomain.romatch (bc_of_symtbl se) m0 (romem_for_symtbl se).
   Proof.
     intros. constructor.
     - unfold romem_for_symtbl in H2.
       induction (Mem.sup_list (Genv.genv_sup se)); simpl in H2.
       rewrite Maps.PTree.gempty in H2. congruence.
       admit. (*ok*)
     - admit. (*ok *)
   Admitted.

   Section Initial.
     
     Variable m0 : mem.
     Variable main_b : block.
     Variable tm0 : mem.
     Variable sp0 : block.

     Definition main_id := prog_main (skel OpenC).
     
     Hypothesis INITM: Genv.init_mem (skel OpenC) = Some m0.
     Hypothesis FINDMAIN: Genv.find_symbol se main_id = Some main_b.
     Hypothesis DUMMYSP: Mem.alloc m0 0 0 = (tm0, sp0).
     
     Let j0 := Mem.flat_inj (Mem.support m0).
     Let Hm0_ := Genv.initmem_inject (skel OpenC) INITM.

     Lemma Hm0 : Mem.inject j0 m0 tm0.
     Proof.
       eapply Mem.alloc_right_inject; eauto.
     Qed.
     
     Definition wj0 := injpw j0 m0 tm0 Hm0.

     Lemma Hvalid: Mach.valid_blockv (Mem.support tm0) (Vptr sp0 Ptrofs.zero).
     Proof.
       constructor.
       eapply Mem.valid_new_block. eauto.
     Qed.

     Lemma Hlocal: StackingproofC.pointer_tid (Mem.tid (Mem.support tm0)) (Vptr sp0 Ptrofs.zero).
     Proof.
       constructor. apply Mem.alloc_result in DUMMYSP as RES.
       subst. simpl. apply Mem.support_alloc in DUMMYSP.
       rewrite DUMMYSP. reflexivity.
     Qed.
     
     Let rs0 := initial_regset (Vptr main_b Ptrofs.zero) (Vptr sp0 Ptrofs.zero).

     Lemma Hme : Mem.extends tm0 tm0.
     Proof. eapply Mem.extends_refl. Qed.
     
     Definition init_w_cainjp := cajw wj0 main_sig rs0.
     
     Definition init_w_ext := extw tm0 tm0 Hme.
          
     Definition init_w : GS.ccworld cc_compcert :=
       (se,(row se m0,(se,(se,main_sig,(tse,(init_w_cainjp,init_w_ext)))))).


     Theorem sound_ro : sound_memory_ro se m0.
     Proof.
       constructor.
       - eapply initial_romatch; eauto.
       - apply Genv.init_mem_genv_sup in INITM as SUP.
         rewrite <- SUP. unfold se.
         apply Mem.sup_include_refl.
     Qed.
     
   End Initial.


   Definition empty_worlds {T:Type}: NatMap.t (option T) := NatMap.init None.
   Definition empty_gworlds {T:Type}: NatMap.t (option T) := NatMap.init None.
   Definition initial_worlds {T: Type} (w: T) := NatMap.set 1%nat (Some w) empty_worlds.
   Definition initial_gworlds {T:Type} (w: T) := NatMap.set 1%nat (Some w) empty_gworlds.
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

    Compute GS.ccworld cc_compcert.
    
    Definition sig_w_compcert (w: GS.ccworld cc_compcert) : signature :=
      (snd (fst (snd (snd (snd w))))).

    Definition rs_w_compcert (w: GS.ccworld cc_compcert) : regset :=
      cajw_rs (fst (snd (snd (snd (snd (snd (w))))))).

    Definition injp_w_compcert (w: GS.ccworld cc_compcert) : injp_world :=
      cajw_injp (fst (snd (snd (snd (snd (snd (w))))))).

    Definition cainjp_w_compcert (w: GS.ccworld cc_compcert) :=
      (fst (snd (snd (snd (snd (snd (w))))))).
    
    Definition regset_lessdef (rs1 rs2: regset) := forall r, Val.lessdef (rs1 r) (rs2 r).

    Compute GS.gworld cc_compcert.

    Definition injp_gw_compcert (w: GS.gworld cc_compcert) : injp_world :=
      fst (snd (snd (w))).

    Inductive match_thread_states : GS.ccworld cc_compcert -> (option (GS.ccworld cc_compcert)) -> GS.gworld cc_compcert -> fsim_index -> thread_state_C -> thread_state_A -> Prop :=
    |match_local : forall wB i sc sa wp
        (M_STATES: match_local_states wB wp i sc sa),
        match_thread_states wB None wp i (CMulti.Local OpenC sc) (Local OpenA sa)
    |match_initial : forall wB i cqv rs m tm
        (M_QUERIES: GS.match_query cc_compcert wB (get_query cqv m) (rs,tm))
        (SG_STR: cqv_sg cqv = start_routine_sig),
        match_thread_states wB None (get wB) i (CMulti.Initial OpenC cqv) (Initial OpenA rs)
    |match_returny : forall wB wA i sc sa wp wp' rs
        (M_STATES: match_local_states wB wp i sc sa)
        (WA_SIG : sig_w_compcert wA = yield_sig)
        (GET: get wA = wp')
        (RSLD: regset_lessdef (rs_w_compcert wA) rs)
        (ACC1: wp *-> wp')
        (M_REPLIES: forall r1 r2 sc' wp'',
            get wA o-> wp'' ->
            GS.match_reply cc_compcert (set wA wp'') r1 r2 ->
            (after_external (OpenC se)) sc r1 sc' ->
            exists i' sa', (after_external (OpenA tse)) sa r2 sa' /\
                        match_local_states wB wp'' i' sc' sa'),
        match_thread_states wB (Some wA) wp' i (CMulti.Returny OpenC sc) (Returny OpenA sa rs)
    |match_returnj : forall wB wA i sc sa wp wp' wait vptr int rs
        (RSLD: regset_lessdef (rs_w_compcert wA) rs)                     
        (M_STATES: match_local_states wB wp i sc sa)
        (WAIT: rs # RDI = Vint int /\ int_to_nat int = wait)
        (VPTR: Val.inject (injp_mi (injp_w_compcert wA)) vptr (rs # RSI))
        (WA_SIG : sig_w_compcert wA = pthread_join_sig)
        (GET: get wA = wp')
        (ACC1: wp *-> wp')
        (M_REPLIES: forall r1 r2 sc' wp'',
            get wA o-> wp'' ->
            GS.match_reply cc_compcert (set wA wp'') r1 r2 ->
            (after_external (OpenC se)) sc r1 sc' ->
            exists i' sa', (after_external (OpenA tse)) sa r2 sa' /\
                        match_local_states wB wp'' i' sc' sa'),
        match_thread_states wB (Some wA) wp' i (CMulti.Returnj OpenC sc wait vptr) (Returnj OpenA sa rs)
    |match_final_sub : forall wB wp i res tres
      (VRES: Val.inject (injp_mi (injp_gw_compcert wp)) res tres),
      (* the signature for all sub threads are start_routine_sig *)
      match_thread_states wB None wp i (CMulti.Final OpenC res) (Final OpenA tres).


      
    Definition injp_tid (w: injp_world) : nat :=
     match w with injpw j m tm Hm => Mem.tid (Mem.support m) end.
                     
    Definition injp_nexttid (w: injp_world) : nat :=
      match w with injpw j m tm Hm => Mem.next_tid (Mem.support m) end.

    Definition gw_tid (gw: GS.gworld cc_compcert) : nat :=
      injp_tid (injp_gw_compcert gw).

    Definition gw_nexttid gw : nat := injp_nexttid (injp_gw_compcert gw).

    Definition gw_accg (gw gw' : GS.gworld cc_compcert) :=
      injp_accg (injp_gw_compcert gw) (injp_gw_compcert gw').

    Inductive match_states' : global_index -> (NatMap.t (option (GS.gworld cc_compcert))) -> CMulti.state OpenC -> state OpenA -> Prop :=
      |global_match_intro : forall threadsC threadsA cur next (worldsA : NatMap.t (option (GS.ccworld cc_compcert))) worldsB worldsP gi (w0 : GS.ccworld cc_compcert) m0 main_b wPcur tm0 sp0
      (CUR_VALID: (1 <= cur < next)%nat)
      (INDEX_LENGTH : length gi = (next -1)%nat)                      
      (INITMEM: Genv.init_mem (skel OpenC) = Some m0)
      (DUMMYSP : Mem.alloc m0 0 0 = (tm0, sp0))
      (FINDMAIN: Genv.find_symbol se main_id = Some main_b)
      (INITW: w0 = init_w m0 main_b tm0 sp0 INITMEM DUMMYSP)
      (INITVALID: forall cqv, ~ NatMap.get 1%nat threadsC = Some (CMulti.Initial OpenC cqv))
      (MAIN_THREAD_INITW: NatMap.get 1%nat worldsB = Some w0)
      (SUB_THREAD_SIG: forall n wB, (n <> 1)%nat -> NatMap.get n worldsB = Some wB ->
                               (sig_w_compcert wB) = start_routine_sig /\
                                 cajw_sg (cainjp_w_compcert wB) = start_routine_sig )
      (CUR_GWORLD: NatMap.get cur worldsP = Some wPcur)
      (CUR_INJP_TID: cur = gw_tid wPcur /\ next = gw_nexttid wPcur)
      (FIND_TID: forall n wp, NatMap.get n worldsP = Some wp -> gw_tid wp = n /\ (1<= n < next)%nat)
      (THREADS_DEFAULT: fst threadsA = None)
      (THREADS: forall n, (1 <= n < next)%nat -> exists wB owA wP lsc lsa i,
            NatMap.get n worldsB = Some wB /\
              nth_error gi (n-1)%nat = Some i /\
              GS.match_senv cc_compcert wB se tse /\
              (* injp_match_stbls (injp_w_compcert wB) se tse /\ *)
              NatMap.get n threadsC = Some lsc /\
              NatMap.get n threadsA = Some lsa /\
              NatMap.get n worldsA = owA /\
              match_thread_states wB owA wP i lsc lsa /\
              NatMap.get n worldsP = Some wP /\
              (n <> cur -> gw_accg wP wPcur)
              ),
          match_states' gi worldsP (mk_gstate OpenC threadsC cur next) (mk_gstate_asm OpenA threadsA cur next).
    
    Inductive match_states : global_index -> CMulti.state OpenC -> state OpenA -> Prop :=
    |ms_intro: forall gi worldsP gsc gsa ,
        match_states' gi worldsP gsc gsa ->
        match_states gi gsc gsa.

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


    Lemma sup_incr_tid_ntid : forall s t, Mem.next_tid s = Mem.next_tid (Mem.sup_incr_tid s t).
    Proof.
      intros. unfold Mem.sup_incr_tid. destruct s. simpl. unfold Mem.next_tid. simpl.
      destruct stacks; simpl. rewrite Mem.update_list_length. reflexivity.
      rewrite Mem.update_list_length. reflexivity.
    Qed.

    Lemma advance_next_nexttid : forall gl s s',
        Genv.advance_next gl s = s' ->
        Mem.next_tid s' = Mem.next_tid s.
    Proof.
      induction gl. intros.
      inv H. simpl. reflexivity.
      intros. simpl in H. apply IHgl in H. simpl in H.
      rewrite <- sup_incr_tid_ntid in H. auto.
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
      case_eq (Mem.alloc m0 0 0). intros tm0 sp0 DUMMY.
      (* set (j0 := Mem.flat_inj (Mem.support m0)).
        se   t (wj0 := injpw j0 m0 m0 Hm0). *)
      set (w0 := init_w m0 main_b tm0 sp0 H1 DUMMY). unfold init_w, wj0 in w0.
      generalize valid_se. intro VALID.
      simpl in fsim_lts.
      assert (MSE': GS.match_senv cc_compcert w0 se tse).
      (* assert (MSE': injp_match_stbls (injp_w_compcert w0) se tse). *)
      { constructor. constructor. constructor.
        constructor. constructor. constructor.
        constructor.
        constructor.  rewrite <- SE_eq. apply match_se_initial; eauto.
        unfold se, CMulti.initial_se. rewrite SUP. eauto with mem. rewrite <- SE_eq.
        unfold se, CMulti.initial_se. rewrite SUP.
        apply Mem.support_alloc in DUMMY as SUPA. rewrite SUPA.
        simpl. eauto with mem.
        constructor. }
      specialize (fsim_lts se tse w0 MSE' VALID) as FSIM.
      set (rs0 := initial_regset (Vptr main_b Ptrofs.zero) (Vptr sp0 Ptrofs.zero)).
      set (q2 := (rs0,tm0)).
      set (q1 := {| cq_vf := Vptr main_b Ptrofs.zero; cq_sg := main_sig; cq_args := nil; cq_mem := m0 |}).
      assert (MQ: GS.match_query cc_compcert w0 q1 q2).
      { (* match initial query *)
        assert (NONEARG: Conventions1.loc_arguments main_sig = nil).
        unfold main_sig. unfold Conventions1.loc_arguments. destruct Archi.ptr64; simpl; eauto.
        destruct Archi.win64; simpl; eauto.
        (*ro*)
        econstructor. split. instantiate (1:= q1). constructor. constructor.
        exploit sound_ro; eauto.
        (*wt*)
        econstructor. split. instantiate (1:= q1). constructor. constructor.
        reflexivity. simpl. constructor.
        (*CAinjp*)
        econstructor. split. instantiate (1:= q2).
        { econstructor.
        - rewrite NONEARG. simpl. constructor.
        - econstructor. unfold Mem.flat_inj. rewrite pred_dec_true.
          reflexivity.  rewrite <- SUP.
          eapply Genv.genv_symb_range; eauto. reflexivity.
        - intros. unfold Conventions.size_arguments in H.
          rewrite NONEARG in H. simpl in H. inv H. extlia.
        - simpl. unfold Tptr. replace Archi.ptr64 with true. reflexivity.
          eauto.
        - simpl. unfold initial_regset. rewrite Pregmap.gso.
          rewrite Pregmap.gss. unfold Vnullptr. replace Archi.ptr64 with true.
            econstructor. eauto. congruence.
        - unfold initial_regset. rewrite Pregmap.gss.
          eapply Hvalid; eauto.
        - unfold initial_regset. rewrite Pregmap.gss.
          eapply Hlocal; eauto.
        - econstructor. simpl. red.
          unfold Conventions.size_arguments. rewrite NONEARG.
          reflexivity.
        - congruence.
        - unfold initial_regset. rewrite Pregmap.gso. rewrite Pregmap.gss. unfold Vnullptr.
          destruct Archi.ptr64; congruence. congruence. }
        econstructor; eauto. intros. simpl. apply val_inject_id. eauto.
        split. unfold rs0. unfold initial_regset.
        rewrite Pregmap.gso; try congruence.
        rewrite Pregmap.gso; try congruence.
        rewrite Pregmap.gss. congruence.
        constructor.
      }
      eapply GS.fsim_match_initial_states in FSIM as FINI; eauto.
      destruct FINI as [i [ls2 [A B]]].
      exists (initial_indexs i). eexists. split.
      + econstructor. unfold AsmMulti.main_id, initial_se.
        unfold CMulti.initial_se, CMulti.main_id in H0.
        rewrite <- fsim_skel. eauto. rewrite <- fsim_skel. eauto.
        eauto. reflexivity. eauto.
      + econstructor; eauto. econstructor; eauto.
        intros. simpl. rewrite NatMap.gss. congruence.
        instantiate (1:= DUMMY). instantiate (1:= H1).
        instantiate (1:= initial_worlds w0). reflexivity.
        intros. unfold initial_worlds in H3. rewrite NatMap.gso in H3.
        inv H3. auto.
        instantiate (2:= initial_gworlds (get w0)). reflexivity.
        unfold gw_tid. simpl.
        simpl. split.  erewrite init_mem_tid; eauto.
        unfold gw_nexttid. simpl.
        erewrite init_mem_nexttid; eauto.
        intros. simpl in H. unfold initial_gworlds in H.
        destruct (Nat.eq_dec n 1). subst. rewrite NatMap.gss in H.
        inv H. unfold gw_tid. simpl. erewrite init_mem_tid; eauto.
        rewrite NatMap.gso in H. inv H. lia.
        instantiate (1:= empty_worlds). 
        intros.
        assert (n=1)%nat. lia. subst. 
        exists w0, None, (get w0), (CMulti.Local OpenC ls), (Local OpenA ls2), i.
        repeat apply conj; eauto. simpl.
        constructor. unfold match_local_states. eauto.
        congruence.
    Qed.

    Lemma concur_final_states: forall i s1 s2 r,
            match_states i s1 s2 -> Closed.final_state ConcurC s1 r -> Closed.final_state ConcurA s2 r.
    Proof.
      intros. inv H0. inv H. inv H0.
      simpl in *. subst cur.
      unfold CMulti.get_cur_thread, CMulti.get_thread in H2. simpl in H2.
      specialize (THREADS 1%nat CUR_VALID).
      destruct THREADS as (wB & owA & wP & lsc & lsa & i' & GETWB & GETi & MSEw & GETC & GETA & GETWA & MS & GETP & ACC).
      assert (lsc = CMulti.Local OpenC ls).
      eapply foo; eauto. subst lsc.
      specialize (fsim_lts se tse wB MSEw valid_se) as FSIM.
      inversion FSIM.
      assert (wB = init_w m0 main_b tm0 sp0 INITMEM DUMMYSP).
      eapply foo; eauto. subst wB.
      inv MS.
      unfold match_local_states in M_STATES.
      exploit fsim_match_final_states. eauto.
      eauto. intros [r2 [gw' [FIN [ACCE [ACCI MR]]]]]. destruct r2.
      destruct gw' as [p [q [wp we]]]. simpl in p, q,wp,we.
      destruct MR as [q1' [MRro [q1'' [MRwt [q2' [MRp MRe]]]]]].
      inv MRro. inv MRwt. inv MRp. inv MRe.
      econstructor. 5: eauto. eauto. eauto.
      subst. simpl in *. unfold tres in H9.
      - assert (rs' PC = Vnullptr). eauto. generalize (H4 PC).
        intro RLD. rewrite H6 in RLD. unfold Vnullptr in *.
        destr; inv RLD; eauto.
      - assert (rs' RAX = Vint r).
        unfold Conventions1.loc_result, main_sig in H9. simpl in H9.
        destruct Archi.ptr64; simpl in H9. inv H9. eauto. inv H9. eauto.
        generalize (H4 RAX). intro. simpl in H7. rewrite H6 in H7. inv H7. reflexivity.
Qed.
    
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
      - inv mi_thread. simpl. inv Hms. constructor; auto.
        simpl. unfold Mem.sup_create. simpl.
        split. simpl.
        rewrite !app_length. simpl. lia. simpl. auto.
      - clear - mi_inj.
        inv mi_inj. constructor; eauto.
      - intros. eapply mi_freeblocks. unfold Mem.valid_block in *.
        simpl in H.
        rewrite Mem.sup_create_in. eauto.
      - intros. unfold Mem.valid_block. simpl. rewrite <- Mem.sup_create_in.
        eapply mi_mappedblocks; eauto.
      - inv mi_thread. inv Hms. unfold Mem.next_tid. eauto.
    Qed.

    Lemma yield_inject : forall j m tm n p tp,
        Mem.inject j m tm ->
        Mem.inject j (Mem.yield m n p) (Mem.yield tm n tp).
    Proof.
      intros. unfold Mem.yield. inv H.
      constructor; simpl; eauto.
      - inv mi_thread. inv Hms. constructor; auto.
          simpl. unfold Mem.sup_yield. red. split; eauto.
      - inv mi_inj.
        constructor; eauto.
    Qed.
    Locate mksup.
    (** To be moved to Memory.v *)
    Lemma mksup_ext:
      forall stack1 stack2 tid1 tid2 a1 a2,
        stack1 = stack2 -> tid1 = tid2 ->
        Mem.mksup stack1 tid1 a1 = Mem.mksup stack2 tid2 a2.
    Proof.
      intros. subst. f_equal; apply Axioms.proof_irr.
    Qed.
    
    Lemma yield_extends : forall m tm n1 n2 p tp,
        Mem.extends m tm -> n1 = n2 ->
        Mem.extends (Mem.yield m n1 p) (Mem.yield tm n2 tp).
    Proof.
      intros. unfold Mem.yield. inv H.
      constructor; simpl; eauto.
      - unfold Mem.sup_yield. apply mksup_ext; congruence.
      - inv mext_inj. constructor; eauto.
    Qed.

   Inductive injp_acc_thc : injp_world -> injp_world -> Prop :=
     injp_thread_create: forall j m1 m2 Hm m1' m2' Hm' id1 id2
         (Htc1: (m1', id1) = Mem.thread_create m1)
         (Htc2: (m2', id2) = Mem.thread_create m2),
         injp_acc_thc (injpw j m1 m2 Hm) (injpw j m1' m2' Hm').

   Inductive injp_acc_yield : injp_world -> injp_world -> Prop :=
     |injp_yield_intro : forall j m1 m2 (n: nat) p tp m1' m2' Hm Hm',
         m1' = Mem.yield m1 n p ->
         m2' = Mem.yield m2 n tp ->
         injp_acc_yield (injpw j m1 m2 Hm) (injpw j m1' m2' Hm').

   Inductive worlds_ptc_str : cc_cainjp_world -> cc_cainjp_world -> Prop :=
   | ptc_str_intro : forall j m tm id m' tm' P1 m'' P2 tm'' Hm0 sp rs tm''' Hm1
       (Htc1: (m', id) = Mem.thread_create m)
       (Htc2: (tm', id) = Mem.thread_create tm)
       (Hy1: Mem.yield m' id P1 = m'')
       (Hy2: Mem.yield tm' id P2 = tm'')
       (Hd: (tm''', sp) = Mem.alloc tm'' 0 0),
       worlds_ptc_str
         (cajw (injpw j m tm Hm0) pthread_create_sig rs)
         (cajw (injpw j m'' tm''' Hm1) start_routine_sig (rs # PC <- (rs RSI) # RDI <- (rs RDX)) # RSP <- (Vptr sp Ptrofs.zero)).

   Lemma inject_next_tid : forall j m1 m2,
       Mem.inject j m1 m2 ->
       Mem.next_tid (Mem.support m1) = Mem.next_tid (Mem.support m2).
   Proof.
     intros. inv H. inv mi_thread. inv Hms.
     apply H.
   Qed.

   Lemma lessdef_trans: forall r' v rs trs,
       (forall r : preg, Val.inject inject_id (rs r) (trs r)) ->
       rs r' = v -> v <> Vundef ->
       trs r' = v.
   Proof.
     intros. generalize (H r'). intro HH. apply val_inject_id in HH.
     inv HH; try congruence.
   Qed.

   Lemma ro_acc_yield : forall m1 n p m2,
       Mem.yield m1 n p = m2 ->
       ro_acc m1 m2.
   Proof.
     intros. inv H. constructor; red; simpl; eauto.
   Qed.

   Lemma ro_acc_thread_create : forall m1 m2 n,
       Mem.thread_create m1 = (m2, n) ->
       ro_acc m1 m2.
   Proof.
     intros. inv H. constructor; red; simpl; eauto.
     intros. rewrite <- Mem.sup_create_in; eauto.
   Qed.
   
   Lemma trans_pthread_create__start_routine: forall q_ptc r_ptc q_str qa_ptc wA,
        query_is_pthread_create OpenC q_ptc r_ptc q_str ->
        GS.match_query cc_compcert wA q_ptc qa_ptc ->
        GS.match_senv cc_compcert wA se tse ->
        exists gw wA' ra_ptc qa_str,
          query_is_pthread_create_asm OpenA qa_ptc ra_ptc qa_str /\
            gw_accg (get wA') gw /\
            (forall w, gw_accg w (get wA) -> gw_accg w gw) /\
            (get wA) o-> gw /\
            gw_nexttid gw = S (gw_nexttid (get wA)) /\
                           GS.match_reply cc_compcert (set wA gw) r_ptc ra_ptc /\
                           GS.match_query cc_compcert wA' q_str qa_str /\
                           GS.match_senv cc_compcert wA' se tse /\
                           worlds_ptc_str (cainjp_w_compcert wA) (cainjp_w_compcert wA').
   Proof.
     intros until wA. intros H H0 MSE.
     inv H. destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & w_cap & w_e).
     destruct H0 as [q1' [Hqr [q1'' [Hqw [qa' [Hqca Hqe]]]]]].
     inv Hqr. inv Hqw. simpl in H. destruct H0. simpl in H0. inv H0. simpl in H1.
     inv Hqca. destruct qa_ptc as [trs ttm]. inv Hqe. destruct H2 as [PCN Hme].
     inv Hme. clear Hm4. rename Hm3 into Hme.
     subst tvf targs. rewrite pthread_create_locs in H5. simpl in H5.
     inv H5. inv H17. inv H18. inv H19.
     destruct MSE as [EQ1 [EQ2 [MSE EQ3]]].
     inv EQ1. inv EQ2. inv EQ3. inv H2. inv H3.
     (** prepare arguments *)
     assert (INJPTC: j b_ptc = Some (b_ptc, 0)).
     {
       inv MSE. inv H17.
       exploit mge_dom; eauto. eapply Genv.genv_symb_range. apply FINDPTC.
       intros (b3 & INJ).
       exploit mge_symb; eauto.
       intro HH. apply HH in FINDPTC as FINDPTC'.
       rewrite <- SE_eq in FINDPTC'. fold se in FINDPTC. setoid_rewrite FINDPTC in FINDPTC'.
       inv FINDPTC'. eauto.
     }
     assert (PCVAL: rs PC = Vptr b_ptc Ptrofs.zero).
     inv H6. rewrite H17 in INJPTC. inv INJPTC. reflexivity.
     assert (INJSTR: j b_start = Some (b_start, 0)).
     {
       inv MSE. inv H17.
       exploit mge_dom; eauto. eapply Genv.genv_symb_range. apply FINDSTR. eauto.
       intros (b3 & INJ).
       exploit mge_symb; eauto.
       intro HH. apply HH in FINDSTR as FINDSTR'.
       rewrite <- SE_eq in FINDSTR'. fold se in FINDSTR. setoid_rewrite FINDSTR in FINDSTR'.
       inv FINDSTR'. eauto.
     }
     assert (RSIVAL: rs RSI = Vptr b_start Ptrofs.zero).
     inv H5. rewrite H17 in INJSTR. inv INJSTR. reflexivity.
     case (Mem.thread_create tm) as [tm' id] eqn:MEM_CREATE'.
     exploit thread_create_inject; eauto. intros [Hm1' eqid]. subst id.
     assert (exists b_t' ofs_t', rs RDI = Vptr b_t' ofs_t').
     inv H11. eauto. destruct H2 as [b_t' [ofs_t' RDIVAL]].
     assert (exists b_arg' ofs_arg', rs RDX = Vptr b_arg' ofs_arg').
     inv H13. eauto. destruct H2 as [b_arg' [ofs_arg' RDXVAL]].

     (** prepare memories *)
     (** Here we allocate a dummy block on new thread for target memory.
         It's address is used as the initial value of RSP on this new procedure *)
     assert (TP1: Mem.range_prop tid (Mem.support tm')).
     {
       inv P1. constructor. auto. erewrite <- inject_next_tid; eauto.
     }
     set (tm'2 := Mem.yield tm' tid TP1).
     case (Mem.alloc tm'2 0 0 ) as [tm'3 sp0] eqn:DUMMY.
     assert (TP2: Mem.range_prop (Mem.tid (Mem.support tm)) (Mem.support tm'3)).
     {
       generalize (Mem.tid_valid (Mem.support tm)). intro.
       constructor; eauto. lia.
       apply Mem.support_alloc in DUMMY. rewrite DUMMY. simpl.
       unfold Mem.next_tid, sup_incr, Mem.sup_yield. simpl.
       rewrite Mem.update_list_length. inv MEM_CREATE'. simpl.
       rewrite app_length. simpl. lia.
     }
     set (tm'4 := Mem.yield tm'3 (Mem.tid (Mem.support tm)) TP2).
     
     set (m1' := Mem.yield m1 tid P1).
     assert (Hm'2 : Mem.inject j m1' tm'2).  unfold m1', tm'2.
     eapply yield_inject. eauto.
     assert (Hmq: Mem.inject j m1' tm'3).
     eapply Mem.alloc_right_inject; eauto.
     assert (Hmr: Mem.inject j m1 tm'4).
     {
       clear - Hm1 MEM_CREATE Hmq.
       inv Hmq. constructor; eauto.
       + inv mi_thread. constructor; eauto.
         inv Hms. constructor; eauto. simpl. inv MEM_CREATE.
         simpl. eapply inject_tid; eauto.
       + inv mi_inj. constructor; eauto.
     }
          

     (** similarly we need Mem.extends tm'4 ttm'4*)
     case (Mem.thread_create ttm) as [ttm' id] eqn:MEM_CREATE'2.
     assert (Hme1: Mem.extends tm' ttm').
     {
       clear - Hme MEM_CREATE' MEM_CREATE'2.
       unfold Mem.thread_create in *. inv MEM_CREATE'.
       inv MEM_CREATE'2. inv Hme.
       constructor; simpl; eauto. congruence.
       inv mext_inj. constructor; eauto.
     }
     assert (tid = id).
     {
       clear -Hme MEM_CREATE' MEM_CREATE'2.
       unfold Mem.thread_create in *. inv MEM_CREATE'.
       inv MEM_CREATE'2. inv Hme. rewrite mext_sup. reflexivity.
     }
     subst id.
     assert (TTP1: Mem.range_prop tid (Mem.support ttm')).
     {
       erewrite <- Mem.mext_sup; eauto.
     }
     set (ttm'2 := Mem.yield ttm' tid TTP1).
     assert (Hme2: Mem.extends tm'2 ttm'2).
     apply yield_extends; eauto.
     exploit Mem.alloc_extends. apply Hme2. eauto. reflexivity. reflexivity.
     intros (ttm'3 & DUMMY2 & Hmqe).
     assert (TTP2: Mem.range_prop (Mem.tid (Mem.support ttm)) (Mem.support ttm'3)).
     {
       erewrite <- Mem.mext_sup; eauto.
       erewrite <- (Mem.mext_sup tm'3 ttm'3); eauto.
     }
     set (ttm'4 := Mem.yield ttm'3 (Mem.tid (Mem.support ttm)) TTP2).
     assert (Hmre: Mem.extends tm'4 ttm'4).
     apply yield_extends; eauto. inv Hme. congruence.
     
     set (rs_q := rs # PC <- (rs RSI) # RDI <- (rs RDX) # RSP <- (Vptr sp0 Ptrofs.zero)).
     set (rs_r := rs # PC <- (rs RA) # RAX <- (Vint Int.one)).
     set (trs_q := trs # PC <- (trs RSI) # RDI <- (trs RDX) # RSP <- (Vptr sp0 Ptrofs.zero)).
     set (trs_r := trs # PC <- (trs RA) # RAX <- (Vint Int.one)).
     rename H0 into RSLD. simpl in RSLD.
     eapply lessdef_trans in PCVAL as PCVAL'; eauto.
     eapply lessdef_trans in RSIVAL as RSIVAL'; eauto.
     eapply lessdef_trans in RDIVAL as RDIVAL'; eauto.
     eapply lessdef_trans in RDXVAL as RDXVAL'; eauto.
     inv H.
     exists (tt, (tt, (injpw j m1 tm'4 Hmr, extw tm'4 ttm'4 Hmre))).
     exists (se, ((row se m1'), (se, (se, start_routine_sig, (tse,((cajw (injpw j m1' tm'3 Hmq) start_routine_sig rs_q) , extw tm'3 ttm'3 Hmqe))) ))).
     exists (trs_r, ttm'4). exists (trs_q, ttm'3).
     assert (UNC23: Mem.unchanged_on (fun _ _ => True) tm'2 tm'3). eapply Mem.alloc_unchanged_on. eauto.
     assert (UNC23': Mem.unchanged_on (fun _ _ => True) ttm'2 ttm'3). eapply Mem.alloc_unchanged_on. eauto.
     apply Mem.support_alloc in DUMMY as HSUP.
     apply Mem.support_alloc in DUMMY2 as HSUP2. simpl.
     assert (ROACCR1 : ro_acc m m1). eapply ro_acc_thread_create; eauto.
     assert (ROACCQ1: ro_acc m m1'). eapply ro_acc_trans. eauto. eapply ro_acc_yield; eauto. reflexivity.
     assert (ROACCQ2: ro_acc tm tm'3).
     eapply ro_acc_trans. eapply ro_acc_thread_create; eauto.
     eapply ro_acc_trans. eapply ro_acc_yield. 
     instantiate (1:= tm'2). reflexivity. eapply ro_acc_alloc; eauto.
     assert (ROACCR2: ro_acc tm tm'4). eapply ro_acc_trans. eauto. eapply ro_acc_yield; eauto. reflexivity.
     assert (ROACCQ3: ro_acc ttm ttm'3).
      eapply ro_acc_trans. eapply ro_acc_thread_create; eauto.
     eapply ro_acc_trans. eapply ro_acc_yield. 
     instantiate (1:= ttm'2). reflexivity. eapply ro_acc_alloc; eauto.
     assert (ROACCR3: ro_acc ttm ttm'4). eapply ro_acc_trans. eauto. eapply ro_acc_yield; eauto. reflexivity.
     assert (SINC1: Mem.sup_include (Mem.support tm) (Mem.support tm'4)).
     { inv ROACCR2. eauto. }
     assert (SINC2: Mem.sup_include (Mem.support ttm) (Mem.support ttm'4)).
     { inv ROACCR3. eauto. } 
     repeat apply conj.
     - fold se in FINDPTC. rewrite SE_eq in FINDPTC.
       fold se in FINDSTR. rewrite SE_eq in FINDSTR.
       econstructor.
       eapply FINDPTC. eapply FINDSTR. eauto. eauto. eauto. eauto. reflexivity.
       unfold trs_q.  rewrite Pregmap.gso.
       rewrite Pregmap.gso.
       rewrite Pregmap.gss.
       eauto. congruence. congruence.
       unfold trs_q. rewrite Pregmap.gso; try congruence.
       rewrite Pregmap.gss. eauto.
       unfold trs_q. rewrite Pregmap.gss. eauto. eauto. eauto.
       instantiate (1:= TTP1). fold ttm'2. eauto. reflexivity.
     - (** accg *)
       simpl.
       econstructor; eauto; try red; intros; try congruence; eauto.
       split. split; eauto. inv MEM_CREATE. simpl. generalize (Mem.tid_valid (Mem.support m)). intro. unfold Mem.next_tid. lia.
       inv MEM_CREATE. constructor; eauto. simpl. red. intros. eauto with mem.
       intros. reflexivity.
       split. split; eauto. simpl. erewrite Mem.support_alloc; eauto. simpl. inv MEM_CREATE'. simpl.
       generalize (Mem.tid_valid (Mem.support tm)). intro. unfold Mem.next_tid. lia.
       constructor; eauto. simpl. red. intros. eauto with mem. intros. reflexivity.
     - intros. inv H. inv MEM_CREATE. inv MEM_CREATE'. unfold gw_accg. unfold injp_gw_compcert.
       simpl. unfold injp_gw_compcert in H0. setoid_rewrite <- H0.
       assert (ROACC: ro_acc m2 tm'4). eapply ro_acc_trans. 2: eauto. constructor; eauto. destruct H23 as [_ [A _]].
       eauto.
       econstructor; eauto.
       + inv ROACC. eauto.
       + inv ROACC. eauto.
       + destruct H22 as [[A B] C]. constructor; simpl. split. unfold Mem.next_tid, Mem.sup_create in *. simpl. rewrite app_length. simpl. lia.
         lia. inv C. constructor; simpl. eapply Mem.sup_include_trans. eauto. red. intros. rewrite <- Mem.sup_create_in. auto.
         intros. etransitivity. eauto. reflexivity. intros. etransitivity. reflexivity. eauto.
       + destruct H23 as [[A B] C]. constructor; simpl. split. etransitivity. eauto.
         unfold Mem.next_tid, Mem.sup_yield. simpl.
         rewrite HSUP. simpl. rewrite Mem.update_list_length. rewrite app_length. simpl. lia. lia.
         inv C. constructor; simpl. eapply Mem.sup_include_trans. eauto. red. intros. rewrite <- Mem.sup_yield_in.
         rewrite HSUP. apply Mem.sup_incr_in2. simpl. rewrite <- Mem.sup_yield_in, <- Mem.sup_create_in. eauto.
         intros. etransitivity. eauto. transitivity (Mem.perm tm'2 b ofs k p). reflexivity.
         transitivity (Mem.perm tm'3 b ofs k p). 2: reflexivity. inv UNC23. apply unchanged_on_perm0; eauto.
         red. simpl. rewrite <- Mem.sup_yield_in, <- Mem.sup_create_in. eauto.
         intros. inv UNC23. rewrite unchanged_on_contents0; eauto. apply unchanged_on_perm in H3; eauto with mem.
     - auto.
     - auto.
     - simpl. inv MEM_CREATE. inv MEM_CREATE'.
       constructor; simpl; eauto; try red; intros; simpl in *; try congruence; eauto.
       assert (Mem.loadbytes tm'3 b ofs n = Some bytes). eauto.
       erewrite Mem.loadbytes_unchanged_on_1 in H17. 2: eauto. eauto.
       red. simpl. rewrite <- Mem.sup_yield_in, <- Mem.sup_create_in. eauto.
       intros. simpl. reflexivity.
       assert (Mem.perm tm'3 b ofs Max p). eauto.
       exploit Mem.perm_unchanged_on_2; eauto. reflexivity.
       red. simpl. rewrite <- Mem.sup_yield_in, <- Mem.sup_create_in. eauto.
       split. split; simpl; eauto. rewrite app_length. simpl. lia. constructor; simpl; eauto. 
       red. intros. rewrite <- Mem.sup_create_in. auto. intros. reflexivity.
       split. split; simpl; eauto. rewrite HSUP. simpl. rewrite Mem.update_list_length. rewrite app_length. simpl. lia.
       constructor; eauto.
       intros. unfold tm'4. transitivity (Mem.perm tm'2 b ofs k p). reflexivity.
       transitivity (Mem.perm tm'3 b ofs k p). 2: reflexivity.
       inv UNC23. apply unchanged_on_perm; eauto. red. simpl. rewrite <- Mem.sup_yield_in, <- Mem.sup_create_in. eauto.
       intros. transitivity (  Maps.ZMap.get ofs (NMap.get (Maps.ZMap.t memval) b (Mem.mem_contents tm'2))).
       2: reflexivity.
       inv UNC23. apply unchanged_on_contents; eauto.
     - simpl. constructor; eauto. inv ROACCR2. eauto. inv ROACCR3. eauto.
     - unfold gw_nexttid. simpl. inv MEM_CREATE. simpl. unfold Mem.sup_create. unfold Mem.next_tid.
       simpl. rewrite app_length. simpl. lia.
     - econstructor; eauto.
       split. econstructor; eauto. constructor. eauto.
       eexists. split. econstructor; eauto. 
       unfold pthread_create_sig. simpl. auto.
       exists (rs_r, tm'4). split. econstructor; eauto.
       unfold pthread_create_sig. simpl.
       unfold Conventions1.loc_result. replace Archi.ptr64 with true. simpl.
       unfold rs_r. rewrite Pregmap.gss. constructor. eauto.
       intros. unfold rs_r. rewrite !Pregmap.gso; eauto.
       destruct r; simpl in H1; simpl; congruence.
       destruct r; simpl in H; simpl; congruence.
       constructor; simpl; eauto.
       intros. unfold rs_r. unfold trs_r.
       setoid_rewrite Pregmap.gsspec. destr. constructor.
       setoid_rewrite Pregmap.gsspec. destr. eauto. eauto. constructor.
     - eexists. split. econstructor; eauto. econstructor.
       eapply ro_acc_sound; eauto.
       eexists. split. econstructor; eauto. simpl. intuition auto.
       exists (rs_q, tm'3). split.
       econstructor; eauto. rewrite start_routine_loc. simpl.
       constructor. unfold rs_q. rewrite Pregmap.gso; try congruence.
       rewrite Pregmap.gss. eauto.
       constructor. unfold Conventions.size_arguments.
       rewrite start_routine_loc. simpl. intros. inv H. extlia.
       unfold rs_q. rewrite Pregmap.gss. constructor.
       eapply Hvalid; eauto. eapply Hlocal; eauto.
       econstructor. unfold Conventions.tailcall_possible, Conventions.size_arguments.
       rewrite start_routine_loc. simpl. reflexivity. congruence.
       constructor; eauto. simpl. unfold rs_q, trs_q. intros.
       setoid_rewrite Pregmap.gsspec. destr. apply val_inject_id. constructor.
       setoid_rewrite Pregmap.gsspec. destr. eauto.
       setoid_rewrite Pregmap.gsspec. destr. eauto. eauto.
       split. unfold rs_q. rewrite Pregmap.gso; try congruence.
       rewrite Pregmap.gso; try congruence. rewrite Pregmap.gss. congruence.
       constructor.
     - constructor. reflexivity.
     - constructor. reflexivity.
     - inv MSE. constructor; eauto. inv ROACCQ1. eapply Mem.sup_include_trans; eauto.
     - reflexivity.
     - econstructor; eauto. reflexivity.
     - congruence.
     - congruence.
     - congruence.
   Qed.

   Lemma match_q_nid: forall qc qa w,
       GS.match_query cc_compcert w qc qa ->
        Mem.next_tid (Mem.support (cq_mem qc)) = Mem.next_tid (Mem.support (snd qa)).
   Proof.
     intros. destruct w as (a & b & c & d & e & f & g). simpl in g.
     destruct H as (qc1 & H1 & qc2 & H2 & qa1 & H3 & H4). 
     inv H1. inv H2. inv H3. destruct qa. inv H4. simpl.
     destruct H13 as [A B]. inv B. inv Hm2. rewrite <- mext_sup.
     inv Hm. inv mi_thread. inv Hms. eauto.
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
      intros. inv H. destruct H4 as [[_ X] _]. simpl. auto.
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
(*
    Lemma injp_acc_yield_nexttid : forall w1 w2, injp_acc_yield w1 w2 -> injp_nexttid w2 = injp_nexttid w1.
    Proof.
      intros. inv H. simpl. eauto. eauto.
    Qed.
*)
    Lemma injp_accg_acci_accg : forall w1 w2 w3,
        injp_accg w1 w2 -> injp_acci w2 w3 -> injp_accg w1 w3.
    Proof.
      intros. destruct w1 as [j1 m1 tm1 Htm1]. destruct w2 as [j2 m2 tm2 Htm2].
      destruct w3 as [j3 m3 tm3 Htm3].
      inv H. inv H0. destruct H11 as [[S11 S11'] H11]. destruct H12 as [[S12 S12'] H12].
      destruct H19 as [[A B] H19]. destruct H20 as [[C D] H20].
      constructor; eauto.
      - eapply Mem.ro_unchanged_trans; eauto. inversion H11. eauto.
      - eapply Mem.ro_unchanged_trans; eauto. inversion H12. eauto.
      -  intros b ofs p Hb ?.
         eapply H9, H17; eauto using Mem.valid_block_unchanged_on.
      - intros b ofs p Hb ?.
        eapply H10, H18; eauto using Mem.valid_block_unchanged_on.
      - split. split. setoid_rewrite <- A.  auto. congruence.
        eapply mem_unchanged_on_trans_implies_valid; eauto.
        unfold loc_unmapped, Mem.thread_external_P. simpl.
        intros b1 _ [Hb Hb0] Hb1. split.
        destruct (j2 b1) as [[b2 delta] | ] eqn:Hb'; eauto.
        edestruct H14; eauto. contradiction. congruence.
      - split. split. setoid_rewrite <- C. auto. congruence.
        eapply mem_unchanged_on_trans_implies_valid; eauto.
        unfold loc_out_of_reach, Mem.thread_external_P. simpl.
        intros b2 ofs2 [Hb2 Hb2'] Hv. split. intros b1 delta Hb'.
        destruct (j1 b1) as [[xb2 xdelta] | ] eqn:Hb.
        * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
            by (eapply H13 in Hb; split; congruence); subst.
        specialize (Hb2 b1 delta Hb). intro. apply Hb2.
        eapply H9; eauto. eapply Mem.valid_block_inject_1; eauto.
        * edestruct H14; eauto. erewrite inject_tid; eauto.
          erewrite inject_block_tid. eauto. 2: eauto. eauto.
        * congruence.
      - eapply inject_incr_trans; eauto.
      - intros b1 b2 delta Hb Hb'' Ht.
      destruct (j2 b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply H21 in Hb'; split; congruence); subst.
        eapply H14; eauto.
      * edestruct H22; eauto. congruence.
        intuition eauto using Mem.valid_block_unchanged_on.
      - intros b1 b2 delta Hb Hb''.
      destruct (j2 b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply H21 in Hb'; split; congruence); subst.
        eapply H15; eauto.
      * eapply inject_incr_local_noglobal; eauto.
    Qed.

    Lemma gw_accg_acci_accg : forall w1 w2 w3,
        gw_accg w1 w2 -> w2 *-> w3 -> gw_accg w1 w3.
    Proof.
      intros. 
      destruct w1 as [p1 [q1 [wp1 we1]]].
      destruct w2 as [p2 [q2 [wp2 we2]]].
      destruct w3 as [p3 [q3 [wp3 we3]]].
      unfold gw_accg in H. unfold gw_accg.
      unfold injp_gw_compcert in *. simpl in H. simpl.
      destruct H0 as [_ [_ [A B]]]. simpl in A.
      eapply injp_accg_acci_accg; eauto.
    Qed.
      
    Lemma injp_acc_yield_accg : forall w1 w2,
        injp_acc_yield w1 w2 ->
        injp_tid w1 <> injp_tid w2 ->
        injp_accg w1 w2.
    Proof.
      intros. inv H.
      constructor; try red; intros; eauto.
      split. split. unfold Mem.next_tid. simpl. lia. simpl in H0. simpl. congruence.
      constructor; try red; intros; eauto.
      split. split; simpl. unfold Mem.next_tid. simpl. lia. simpl in H0.  inv Hm.
      inv mi_thread. inv Hms. congruence.
      constructor; try red; intros; eauto.
      congruence. congruence.
    Qed.

    Lemma injp_acc_yield_acce : forall w1 w2,
        injp_acc_yield w1 w2 ->
        injp_tid w1 = injp_tid w2 ->
        injp_acce w1 w2.
    Proof.
      intros. inv H.
      constructor; try red; intros; eauto.
      split. constructor; simpl. lia. simpl in H0. lia.
      constructor; try red; intros; eauto.
      split. constructor; simpl. lia. simpl in H0.  inv Hm.
      inv mi_thread. inv Hms. congruence.
      constructor; try red; intros; eauto.
      congruence. congruence.
    Qed.

    Lemma injp_acc_yield_acci : forall w1 w2,
        injp_acc_yield w1 w2 ->
        injp_tid w1 = injp_tid w2 ->
        injp_acci w1 w2.
    Proof.
      intros. inv H.
      constructor; try red; intros; eauto.
      setoid_rewrite <- Mem.sup_yield_in in H1. exfalso. apply H, H1.
      setoid_rewrite <- Mem.sup_yield_in in H1. exfalso. apply H, H1.
      split. simpl. simpl in H0. constructor. reflexivity.
      simpl. eauto.
      constructor; try red; intros; eauto.
      split. simpl. simpl in H0.  inv Hm.
      inv mi_thread. inv Hms. constructor.
      reflexivity. simpl. eauto.
      constructor; try red; intros; eauto.
      congruence. congruence.
    Qed.


    Lemma injp_yield_acci_accg : forall w1 w2 w3,
        injp_acc_yield w1 w2 -> injp_acci w2 w3 -> injp_tid w1 <> injp_tid w2 -> injp_accg w1 w3.
    Proof.
      intros. inv H.
      inv H0. simpl in H1.
      constructor; eauto.
      - destruct H8 as [S8 H8]. inv S8. simpl in H0. split. split; simpl.
        simpl in H. setoid_rewrite <- H. reflexivity.
        congruence.
        inv H8. constructor.
        + red. intros. eauto.
        + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m1 b ofs k p0).
          reflexivity. eapply unchanged_on_perm; eauto.
          red. split. auto. simpl. congruence.
        + intros b ofs [A B] Hp. simpl.
          eapply unchanged_on_contents; eauto. split. auto. simpl. congruence.
      - destruct H9 as [S9 H9]. inv S9.
        apply Mem.mi_thread in Hm as Hs. inv Hs. destruct Hms as [X Y].
        split. split.  simpl in H. setoid_rewrite <- H. auto. simpl in H0. congruence.
        inv H9. constructor.
        + red. intros. eauto.
        + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m2 b ofs k p0).
          reflexivity. eapply unchanged_on_perm; eauto.
          red. split. auto. simpl. congruence.
        + intros b ofs [A B] Hp. simpl.
          eapply unchanged_on_contents; eauto. split. auto. simpl. congruence.
      - red. intros. eapply H11; eauto. simpl. congruence.
      - eapply inject_incr_local_noglobal; eauto.
    Qed.
    
    Lemma injp_yield_acci_accg' : forall w1 w2 w3,
        injp_acc_yield w1 w2 -> injp_acci w1 w3 -> injp_tid w1 <> injp_tid w2 -> injp_accg w2 w3.
    Proof.
      intros. inv H.
      inv H0. simpl in H1.
      constructor; eauto.
      - destruct H8 as [S8 H8]. inv S8. split. split; simpl. setoid_rewrite <- H. auto. congruence.
        inv H8. constructor.
        + red. intros. eauto.
        + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m1 b ofs k p0).
          reflexivity. eapply unchanged_on_perm; eauto.
          red. split. auto. simpl in B. congruence.
        + intros b ofs [A B] Hp. simpl.
          eapply unchanged_on_contents; eauto. split. auto. simpl in B. congruence.
      - destruct H9 as [S9 H9]. inv S9. apply Mem.mi_thread in Hm as Hs. inv Hs. destruct Hms as [X Y].
        split. split; simpl. setoid_rewrite <- H. auto. congruence.
        inv H9. constructor.
        + red. intros. eauto.
        + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m2 b ofs k p0).
          reflexivity. eapply unchanged_on_perm; eauto.
          red. split. auto. simpl in B. congruence.
        + intros b ofs [A B] Hp. simpl.
          eapply unchanged_on_contents; eauto. split. auto. simpl in B. congruence.
      - red. intros. exploit H11; eauto. simpl in H2. congruence.
      - eapply inject_incr_local_noglobal; eauto.
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
     - destruct H7 as [[S7 S7'] H7]. split. split; simpl. unfold Mem.next_tid. simpl.
       rewrite app_length. simpl. unfold Mem.next_tid in S7. lia.
       congruence.
       inv H7. constructor.
       + red. intros. apply VALID1. eapply unchanged_on_support; eauto.
       + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m1 b ofs k p0).
         eapply unchanged_on_perm; eauto.
         red. split; auto. simpl. reflexivity.
       + intros b ofs [A B] Hp. simpl.
         eapply unchanged_on_contents; eauto. split; auto.
      - destruct H8 as [[S8 S8'] H8]. apply Mem.mi_thread in Hm as Hs. destruct Hs as [X Y].
        split. split; simpl. unfold Mem.next_tid in *. simpl. rewrite app_length. simpl. lia. congruence.
        inv H8. constructor.
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
     apply Mem.mi_thread in Hm as Hmi. inv Hmi.  destruct Hms as [X Y].
     constructor; eauto.
     - destruct H6 as [[S6 S6'] H6]. split. split; simpl. auto. congruence.
        inv H6. constructor.
        + red. intros.  apply VALID1. apply unchanged_on_support. auto.
        + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m1' b ofs k p0).
          eapply unchanged_on_perm; eauto.
          red. split. auto. congruence. reflexivity.
        + intros b ofs [A B] Hp. simpl.
          eapply unchanged_on_contents; eauto. split. auto. auto.
      - destruct H7 as [[S7 S7'] H7]. 
        split. split; simpl. auto. congruence.
        inv H7. constructor.
        + red. intros. apply VALID2. apply unchanged_on_support. auto.
        + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m2 b ofs k p0).
          reflexivity. eapply unchanged_on_perm; eauto.
          red. split. auto. simpl in B. congruence.
        + intros b ofs [A B] Hp. simpl.
          eapply unchanged_on_contents; eauto. split; auto.
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
     apply Mem.mi_thread in Hm as Hmi. inv Hmi. destruct Hms as [X Y]. simpl in Hid.
     constructor; eauto.
     - destruct H7 as [[S7 S7'] H7]. split. split; simpl. auto. congruence.
       inv H7. constructor.
       + red. intros. apply VALID1. apply unchanged_on_support. auto.
       + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m1 b ofs k p0).
         eapply unchanged_on_perm; eauto.
         red. split; auto. reflexivity.
       + intros b ofs [A B] Hp. simpl.
         eapply unchanged_on_contents; eauto. split; auto.
     - destruct H8 as [S8 H8]. split.
       apply Mem.mi_thread in Hm1 as Hs. inv Hs. destruct Hms as [Z Z'].
       simpl in *. split; simpl. unfold Mem.next_tid in *. simpl. lia. congruence.
       inv H8. constructor.
       + red. intros. apply VALID2. apply unchanged_on_support. auto.
       + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m2 b ofs k p0).
         eapply unchanged_on_perm; eauto.
         red. split; auto. reflexivity.
       + intros b ofs [A B] Hp. simpl.
         eapply unchanged_on_contents; eauto. split; auto.
   Qed.

      Lemma injp_accg_yield_acce : forall w1 w2 w3,
       injp_accg w1 w2 -> injp_acc_yield w2 w3 ->
       injp_tid w3 = injp_tid w1 ->
       injp_acce w1 w3.
   Proof.
     intros. rename H1 into Hid. inv H0. inv H.
     assert (VALID1: forall b, Mem.valid_block m1 b <-> Mem.valid_block (Mem.yield m1 n p) b).
     intros. unfold Mem.valid_block. simpl. apply Mem.sup_yield_in.
     assert (VALID2: forall b, Mem.valid_block m2 b <-> Mem.valid_block (Mem.yield m2 n tp) b).
     intros. unfold Mem.valid_block. simpl. apply Mem.sup_yield_in.
     apply Mem.mi_thread in Hm as Hmi. inv Hmi. destruct Hms as [X Y]. simpl in Hid.
     constructor; eauto.
     - destruct H7 as [[S7 S7'] H7]. split. split; simpl. auto. congruence.
       inv H7. constructor.
       + red. intros. apply VALID1. apply unchanged_on_support. auto.
       + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m1 b ofs k p0).
         eapply unchanged_on_perm; eauto.
         red. split; auto. reflexivity.
       + intros b ofs [A B] Hp. simpl.
         eapply unchanged_on_contents; eauto. split; auto.
     - destruct H8 as [[S8 S8'] H8]. split.
       apply Mem.mi_thread in Hm1 as Hs. inv Hs. destruct Hms as [Z Z'].
       simpl in *. split; auto.
       inv H8. constructor.
       + red. intros. apply VALID2. apply unchanged_on_support. auto.
       + intros b ofs k p0 [A B] Hv. transitivity (Mem.perm m2 b ofs k p0).
         eapply unchanged_on_perm; eauto.
         red. split; auto. reflexivity.
       + intros b ofs [A B] Hp. simpl.
         eapply unchanged_on_contents; eauto. split; auto.
   Qed.
   
   (*
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
    *)

   
   Lemma w_compcert_sig_eq : forall w qc qa, 
       GS.match_query cc_compcert w qc qa ->
       sig_w_compcert w = cajw_sg (cainjp_w_compcert w).
   Proof.
     intros. destruct w as (a & b & c & d & e & f & g).
     destruct H as (qc' & H1 & qc'' & H2 & qa' & H3 & H4).
     inv H1. inv H2. destruct d. inv H0. inv H3. reflexivity.
   Qed.

   Lemma gw_acce_tid : forall (w1 w2: GS.gworld cc_compcert),
       w1 o-> w2 ->
       gw_tid w2 = gw_tid w1.
   Proof.
     intros. destruct w1 as [p [q [wp1 we1]]]. destruct w2 as [p' [q' [wp2 we2]]].
     destruct H as [_ [_ [H1 H2]]]. simpl in H1, H2.
     unfold injp_gw_compcert. simpl. eapply injp_acce_tid. eauto.
   Qed.

   Lemma gw_acci_tid : forall (w1 w2: GS.gworld cc_compcert),
       w1 *-> w2 ->
       gw_tid w2 = gw_tid w1.
   Proof.
     intros. destruct w1 as [p [q [wp1 we1]]]. destruct w2 as [p' [q' [wp2 we2]]].
     destruct H as [_ [_ [H1 H2]]]. simpl in H1, H2.
     unfold injp_gw_compcert. simpl. eapply injp_acci_tid. eauto.
   Qed.

    Lemma gw_acci_nexttid : forall (w1 w2: GS.gworld cc_compcert),
       w1 *-> w2 ->
       gw_nexttid w2 = gw_nexttid w1.
   Proof.
     intros. destruct w1 as [p [q [wp1 we1]]]. destruct w2 as [p' [q' [wp2 we2]]].
     destruct H as [_ [_ [H1 H2]]]. simpl in H1, H2.
     unfold injp_gw_compcert. simpl. eapply injp_acci_nexttid. eauto.
   Qed.

   Lemma w_get_injp_eq : forall (w: GS.ccworld cc_compcert),
       injp_gw_compcert (get w) = cajw_injp (cainjp_w_compcert w).
   Proof.
     intros. destruct w as (a & b & c & d & e & f & g). reflexivity.
   Qed.

   Inductive ext_acc_yield : ext_world -> ext_world -> Prop :=
    ext_yield_intro : forall (m1 m2 : mem) (n : nat) (p : Mem.range_prop n (Mem.support m1))
                        (tp : Mem.range_prop n (Mem.support m2)) (m1' m2' : Mem.mem') Hm Hm',
                       m1' = Mem.yield m1 n p ->
                       m2' = Mem.yield m2 n tp -> ext_acc_yield (extw m1 m2 Hm) (extw m1' m2' Hm').
   
   Inductive gw_acc_yield : GS.gworld cc_compcert -> GS.gworld cc_compcert -> Prop :=
     gw_acc_yield_intro : forall j m1 m2 m3 m1' m2' m3' Hmj Hme Hmj' Hme',
         injp_acc_yield (injpw j m1 m2 Hmj) (injpw j m1' m2' Hmj') ->
         ext_acc_yield (extw m2 m3 Hme) (extw m2' m3' Hme') ->
         gw_acc_yield (tt,(tt,(injpw j m1 m2 Hmj, extw m2 m3 Hme))) (tt,(tt,(injpw j m1' m2' Hmj', extw m2' m3' Hme'))).
   
   Lemma substep_switch_out : forall i s1 s2 s1' target m',
       match_states i s1 s2 ->
       CMulti.switch_out OpenC s1 s1' target m' ->
       exists s2' tm' ttm' worldsP wpc f Hme' Hmj',
         AsmMulti.switch_out OpenA s2 s2' target ttm' /\
           match_states' i worldsP s1' s2' /\
           let cur := CMulti.cur_tid OpenC s1' in
           (forall cqv, CMulti.get_cur_thread OpenC s1' <> Some (CMulti.Initial OpenC cqv)) /\
             NatMap.get cur worldsP = Some wpc /\
           gw_acc_yield wpc (tt,(tt,(injpw f m' tm' Hmj', extw tm' ttm' Hme'))) /\
           Mem.tid (Mem.support m') = target.
   Proof.
     intros until m'. intros MS SWITCH.
     inv MS. inv H.
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
       exploit fsim_match_external; eauto. intros (wA & [rs_q tm_q] & HX & GW_ACC & MQ & MS & MR).
       assert (wP = wPcur). congruence. subst wP.
       destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & w_cap & w_e).
       destruct MQ as [q1' [Hqr [q1'' [Hqw [qa' [Hqca Hqe]]]]]].
       inv Hqr. inv Hqw. simpl in H. destruct H1. simpl in H1. inv H1. simpl in H.
       inv Hqca. inv Hqe. destruct H13 as [PCN Hme].
       inv Hme. clear Hm3. rename Hm2 into Hme.
       destruct MS as [EQ1 [EQ2 [MSE EQ3]]]. inv EQ1. inv EQ2. inv EQ3.
       inv H13. inv H14.
       rename tm_q into ttm_q. rename rs_q into rrs_q. rename rs into rs_q. rename tm into tm_q.
       assert (tp : Mem.range_prop target (Mem.support(tm_q))).
       { red. red in p. simpl in p. inversion Hm.
         inv mi_thread. inv Hms.
         setoid_rewrite <- H13. auto. }
       set (tm' := Mem.yield tm_q target tp).
       simpl.
       set (wAca := {| cajw_injp := injpw j m tm_q Hm; cajw_sg := sg; cajw_rs := rs_q |}).
       set (m' := Mem.yield m target p).
       assert (Hm' : Mem.inject j m' tm').
       exploit yield_inject; eauto.
       assert (ttp : Mem.range_prop target (Mem.support (ttm_q))).
       { erewrite <- Mem.mext_sup; eauto. }
       set (ttm' := Mem.yield ttm_q target ttp).
       assert (Hme' : Mem.extends tm' ttm').
       eapply yield_extends; eauto.
       eexists. exists tm', ttm'.
       set (wpj := injpw j m tm_q Hm).
       set (wpj' := injpw j m' tm' Hm').
       set (wp:= (tt,(tt,(wpj, extw tm_q ttm_q Hm1)))).
       set (wp' := (tt,(tt,(wpj', extw tm' ttm' Hme')))).

       (*exists (se, ((row se m1'), (se, (se, start_routine_sig, (tse,((cajw (injpw j m1' tm'3 Hmq) start_routine_sig rs_q) , extw tm'3 ttm'3 Hmqe))) ))). *)
       set (wA := (se,(row se m0',(se,(se, sg, (tse,(wAca,extw tm_q ttm_q Hm1))))))).
       exists (NatMap.set cur (Some wp) worldsP), wp, j, Hme', Hm'.
       repeat apply conj.
       + (*step*)
         eapply switch_out_yield. eauto. eauto.
         { inv Q_YIE. inv MSE.
           econstructor. fold tse. rewrite <- SE_eq. eauto.
           subst tvf. inv H3.
           rewrite <- SE_eq in H16.
           exploit match_senv_id. eauto. apply H17. eauto. intros [X Y].
           subst b delta. symmetry in H15. eapply lessdef_trans in H15; eauto.
           simpl. simpl in H19. erewrite <- Mem.mext_sup. 2: eauto.
           inv Hm3. inv mi_thread. inv Hms. unfold Mem.next_tid. auto.
         }
         reflexivity.
         reflexivity.
       + (*match_states*)
         apply gw_acci_nexttid in GW_ACC as NTID. apply gw_acci_tid in GW_ACC as TID.
         econstructor. 8:{ rewrite NatMap.gss. reflexivity. }
         all : simpl; eauto.
         -- simpl. intros. destruct (Nat.eq_dec 1 cur).
            subst. rewrite NatMap.gss. congruence.
            rewrite NatMap.gso; eauto.
         -- destruct CUR_INJP_TID. split.
            rewrite <- H13 in TID. simpl in TID.
            unfold gw_tid in TID. simpl in TID. unfold gw_tid. simpl. congruence.
            rewrite <- H14 in NTID. simpl in NTID.
            unfold gw_nexttid in NTID. simpl in NTID. unfold gw_nexttid. simpl. congruence.
         -- destruct CUR_INJP_TID.  simpl in *.
            intros. destruct (Nat.eq_dec n cur). subst.
            rewrite NatMap.gss in H15. inv H15.
            split. eauto. lia. 
            rewrite NatMap.gso in H15.
            exploit FIND_TID; eauto. eauto.
         -- intros.
            instantiate (1:= NatMap.set cur (Some wA) worldsA).
            destruct (Nat.eq_dec n cur).
            ++ subst n.
               exists wB, (Some wA), wp. eexists. eexists. exists li.
               repeat apply conj; eauto. rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity. rewrite NatMap.gss. reflexivity.
               simpl. simpl in wp'. assert (HRS: rs_q = cajw_rs wAca).  reflexivity.
               eapply match_returny; eauto. inversion Q_YIE. subst m1 args sg vf next0. eauto.
               red. intros. apply val_inject_id. eauto.
               rewrite NatMap.gss. eauto. simpl. congruence.
            ++ (* clear - THREADS H3 OTHERi n0. *)
               destruct (THREADS n H13) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto.
               rewrite NatMap.gso. simpl. eauto. lia.
               rewrite NatMap.gso. simpl. eauto. lia.
               rewrite NatMap.gso. simpl. eauto. lia.
               rewrite NatMap.gso. simpl. eauto. lia.
               simpl. intros. specialize (J H14).
               eapply gw_accg_acci_accg; eauto.
       + intros. simpl. unfold CMulti.get_cur_thread, CMulti.update_cur_thread. simpl.
         unfold CMulti.get_thread, CMulti.update_thread. simpl. rewrite NatMap.gss. congruence.
       + rewrite NatMap.gss. eauto.
       + econstructor; eauto. econstructor; eauto.
         reflexivity. reflexivity. econstructor; eauto. reflexivity. reflexivity.
       + eauto.
     - (** join *)
       specialize (THREADS cur CUR_VALID) as THR_CUR.
       destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
       assert (lsc = CMulti.Local OpenC ls).
       eapply foo; eauto. subst lsc. inv MS.
       specialize (fsim_lts se tse wB MSEw valid_se) as FSIM.
       inversion FSIM.
       clear fsim_simulation fsim_match_initial_states
            fsim_match_final_states.
       exploit fsim_match_external; eauto. intros (wA & [rs_q tm_q] & HX & GW_ACC & MQ & MS & MR).
       assert (wP = wPcur). congruence. subst wP.
       destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & w_cap & w_e).
       destruct MQ as [q1' [Hqr [q1'' [Hqw [qa' [Hqca Hqe]]]]]].
       inv Hqr. inv Hqw. simpl in H. destruct H1. simpl in H1. inv H1. simpl in H.
       inv Hqca. inv Hqe. destruct H13 as [PCN Hme].
       inv Hme. clear Hm3. rename Hm2 into Hme.
       destruct MS as [EQ1 [EQ2 [MSE EQ3]]]. inv EQ1. inv EQ2. inv EQ3.
       inv H13. inv H14. inv MSE.
       rename tm_q into ttm_q. rename rs_q into rrs_q. rename rs into rs_q. rename tm into tm_q.
       inv Q_JOIN.
       subst targs tvf.
       setoid_rewrite pthread_join_locs in H1. simpl in H1.
       inv H1. inv H21. inv H22.
       assert (HPC: rs_q PC = Vptr b_ptj Ptrofs.zero).
       inv H3. rewrite <- SE_eq in H16. exploit match_senv_id; eauto. intros [X Y].
       subst b2 delta. reflexivity.
       assert (HRDI: rs_q RDI = Vint i0). inv H17. eauto.
       assert (HRSI: exists b_vptr' ofs_vptr', rs_q RSI = Vptr b_vptr' ofs_vptr').
       inv H15. eauto. destruct HRSI as [b_vptr' [ofs_vptr' HRSI]].
       eapply lessdef_trans in HPC as HPC'; eauto.
       eapply lessdef_trans in HRDI as HRDI'; eauto.
       eapply lessdef_trans in HRSI as HRSI'; eauto.
       
       assert (tp : Mem.range_prop target (Mem.support(tm_q))).
       red. red in p. simpl in p. inversion Hm.
       inv mi_thread. inv Hms. setoid_rewrite <- H1. auto.
       set (tm' := Mem.yield tm_q target tp).
       set (wAca := {| cajw_injp := injpw j m tm_q Hm; cajw_sg := pthread_join_sig; cajw_rs := rs_q |}).
       set (m' := Mem.yield m target p).
       assert (Hm': Mem.inject j m' tm'). eapply yield_inject; eauto.
       assert (ttp: Mem.range_prop target (Mem.support (ttm_q))).
       erewrite <- Mem.mext_sup; eauto.
       set (ttm' := Mem.yield ttm_q target ttp).
       assert (Hme' : Mem.extends tm' ttm'). eapply yield_extends; eauto.
       set (wpj := injpw j m tm_q Hm).
       set (wpj' := injpw j m' tm' Hm').
       set (wp:= (tt,(tt,(wpj, extw tm_q ttm_q Hm1)))).
       set (wp' := (tt,(tt,(wpj', extw tm' ttm' Hme')))).
       set (wA := (se,(row se m0',(se,(se, pthread_join_sig, (tse,(wAca,extw tm_q ttm_q Hm1))))))).
       eexists. exists tm', ttm'. exists (NatMap.set cur (Some wp) worldsP). exists wp,j,Hme', Hm'.
       repeat apply conj; try rewrite NatMap.gss; eauto.
       + (*step*)
         eapply switch_out_join. eauto. eauto.
         econstructor; eauto.
         fold tse. rewrite <- SE_eq. eauto. eauto. reflexivity. reflexivity.
       + (*match_states*)
         apply gw_acci_nexttid in GW_ACC as NTID. apply gw_acci_tid in GW_ACC as TID.
         simpl in *.
         econstructor. 8:{ rewrite NatMap.gss. reflexivity. }
         all : simpl; eauto.
         -- simpl. intros. destruct (Nat.eq_dec 1 cur).
            subst. rewrite NatMap.gss. congruence.
            rewrite NatMap.gso; eauto.
         -- destruct CUR_INJP_TID. split.
            rewrite H1. rewrite <- TID. reflexivity.
            rewrite H13. rewrite <- NTID. reflexivity.
         -- destruct CUR_INJP_TID.
            intros. destruct (Nat.eq_dec n cur). subst.
            rewrite NatMap.gss in H14. inv H14.
            split. eauto. lia. 
            rewrite NatMap.gso in H14.
            exploit FIND_TID; eauto. eauto.
         -- intros.
            instantiate (1:= NatMap.set cur (Some wA) worldsA).
            destruct (Nat.eq_dec n cur).
            ++ subst n.
               exists wB, (Some wA), wp. eexists. eexists. exists li.
               repeat apply conj; eauto. rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity. rewrite NatMap.gss. reflexivity.
               simpl. simpl in wp.
               eapply match_returnj; eauto.
               red. intros. eapply val_inject_id; eauto.
               simpl. rewrite HRSI'. rewrite <- HRSI. eauto.
               rewrite NatMap.gss. eauto. simpl. congruence.
            ++ (* clear - THREADS H3 OTHERi n0. *)
               destruct (THREADS n H1) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto.
               rewrite NatMap.gso. simpl. eauto. lia.
               rewrite NatMap.gso. simpl. eauto. lia.
               rewrite NatMap.gso. simpl. eauto. lia.
               rewrite NatMap.gso. simpl. eauto. lia.
               simpl. intros. specialize (J H13).
               eapply gw_accg_acci_accg; eauto.
       +  intros. simpl. unfold CMulti.get_cur_thread, CMulti.update_cur_thread. simpl.
         unfold CMulti.get_thread, CMulti.update_thread. simpl. rewrite NatMap.gss. congruence.
       + econstructor; eauto; econstructor; eauto; reflexivity.
       + congruence.
       + congruence.
     - (** final *)
       specialize (THREADS cur CUR_VALID) as THR_CUR.
       destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
       assert (lsc = CMulti.Local OpenC ls).
       eapply foo; eauto. subst lsc. inv MS.
       specialize (fsim_lts se tse wB MSEw valid_se) as FSIM.
       inversion FSIM.
       clear fsim_simulation fsim_match_initial_states fsim_match_external.
       exploit fsim_match_final_states; eauto.
       intros ([rs_r tm_r] & gw' & FINAL' & GW_ACC_IF & GW_ACC_BIG & MR).
       assert (wP = wPcur). congruence. subst wP.
       destruct wB as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & w_cap & w_e).
       destruct gw' as [pp [qq [gwp' gwe']]]. simpl in MR.
       destruct MR as [r1' [Hrr [r1'' [Hrw [qa' [Hrca Hre]]]]]].
       assert (sig' = start_routine_sig).
       {
         exploit SUB_THREAD_SIG; eauto. intros [A B].
         eauto.
       }
       assert (SIG2: cajw_sg w_cap = start_routine_sig).
       { exploit SUB_THREAD_SIG; eauto. intros [A B]. eauto. }
       subst sig'.
       inv Hrr. inv Hrw. simpl in H. inv H. simpl in H1.
       inv Hrca. inv Hre. inv H4. clear Hm2. rename Hm1 into Hme.
       destruct MSEw as [EQ1 [EQ2 [MSE EQ3]]]. inv EQ1. inv EQ2. inv EQ3.
       inv H4. inv H8. inv MSE.
       rename tm_r into ttm_r. rename rs_r into rrs_r.
       rename rs' into rs_r. rename tm' into tm_r.
       simpl in H2. simpl in gwp'.
       
       assert (tp : Mem.range_prop target (Mem.support(tm_r))).
       red. red in p. simpl in p. inversion Hm'0.
       inv mi_thread. inv Hms. setoid_rewrite <- H12. auto.
       set (tm' := Mem.yield tm_r target tp).
       set (m' := Mem.yield gmem target p).
       rename j' into j. rename Hme into Hme_r. rename Hm into Hme. rename Hm' into Hm.
       assert (Hmj' : Mem.inject j m' tm'). eapply yield_inject; eauto.


       assert (ttp: Mem.range_prop target (Mem.support (ttm_r))).
       erewrite <- Mem.mext_sup; eauto.
       set (ttm' := Mem.yield ttm_r target ttp).
       assert (Hme' : Mem.extends tm' ttm'). eapply yield_extends; eauto.

       set (wpj := injpw j gmem tm_r Hm).
       set (wpj' := injpw j m' tm' Hmj').
       set (wp:= (tt,(tt,(wpj, extw tm_r ttm_r Hme_r)))).
       set (wp' := (tt,(tt,(wpj', extw tm' ttm' Hme')))).
       (* set (wA := (se,(row se m0',(se,(se, pthread_join_sig, (tse,(wAca,extw tm_q ttm_q Hm1))))))).
       set (wp' := injpw j m' tm' Hmj'). *)
       set (gw' := (tt,(tt,(gwp', extw tm_r ttm_r Hme)))).
       set (wB := (se,( row se m0',(se,(se, start_routine_sig ,(tse,(w_cap,w_e))))))).
       eexists. exists tm', ttm'. exists (NatMap.set cur (Some gw') worldsP). exists gw',j, Hme', Hmj'.
       repeat apply conj; try rewrite NatMap.gss; eauto.
       + (*step*)
         eapply switch_out_final. eauto. eauto. eauto. reflexivity. reflexivity.
         econstructor; eauto.
       + (*match_states*)
         simpl in *.
         econstructor.
         8:{  rewrite NatMap.gss. reflexivity. }
         all: simpl; eauto.
         -- intros. destruct (Nat.eq_dec 1 cur).
            subst. rewrite NatMap.gss. congruence.
            rewrite NatMap.gso. eauto. eauto.
         -- destruct   CUR_INJP_TID as [X Y]. split.
            apply gw_acci_tid in GW_ACC_BIG. rewrite X. rewrite <- GW_ACC_BIG. reflexivity.
            apply gw_acci_nexttid in GW_ACC_BIG. rewrite Y. rewrite <- GW_ACC_BIG. reflexivity.
         -- destruct   CUR_INJP_TID as [X Y].
            intros. destruct (Nat.eq_dec n cur). subst. rewrite NatMap.gss in H12. inv H12.
            split. apply gw_acci_tid in GW_ACC_BIG. auto. lia.
            rewrite NatMap.gso in H12. eauto. eauto.
         -- intros.
            instantiate (1:= worldsA). 
            destruct (Nat.eq_dec n cur).
            ++ subst n.
               exists wB, None. eexists. eexists. eexists. exists li.
               repeat apply conj; eauto. constructor. reflexivity.
               constructor. reflexivity. destruct w_cap. rewrite <- H4. constructor; eauto.
               rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity.
               eapply match_final_sub.
               instantiate (1:= gw').
               subst tres. unfold injp_gw_compcert. simpl. destruct w_cap.
               inv H. simpl. simpl in SIG2. subst.
               eapply Mem.val_inject_lessdef_compose. eauto. apply val_inject_id.
               apply H2.
               rewrite NatMap.gss. eauto. intros. extlia.
            ++ (* clear - THREADS H3 OTHERi n0. *)
               destruct (THREADS n H12) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto.
               rewrite NatMap.gso. simpl. eauto. lia.
               rewrite NatMap.gso. simpl. eauto. lia.
               rewrite NatMap.gso. simpl. eauto. lia.
               intros. specialize (J H13). eapply gw_accg_acci_accg; eauto.
       + intros. simpl. unfold CMulti.get_cur_thread, CMulti.update_cur_thread. simpl.
         unfold CMulti.get_thread, CMulti.update_thread. simpl. rewrite NatMap.gss. congruence.
       + unfold gw'. destruct w_cap. simpl in H. inv H. constructor; eauto; econstructor; eauto; reflexivity.
   Qed.

   Lemma yield_unchanged: forall m target p P,
       Mem.unchanged_on P m (Mem.yield m target p).
   Proof.
     intros. constructor; simpl; eauto.
     - red. intros. simpl. rewrite <- Mem.sup_yield_in. auto.
     - intros. simpl. reflexivity.
   Qed.

   (** The following 3 lemmas have the *exactly the same* proof,
       for the [store] of [pthread_join],
       which modifies *public* resource that does not get protected *)
   Lemma injp_acce_storev : forall w1 j' m1' m2' Hm' m1'' m2'' Hm'' v tv r tr,
       injp_acce w1 (injpw j' m1' m2' Hm') ->
       Mem.storev Many64 m1' v r = Some m1'' ->
       Val.inject j' v tv ->
       Mem.storev Many64 m2' tv tr = Some m2'' ->
       injp_acce w1 (injpw j' m1'' m2'' Hm'').
   Proof.
     intros.
     etransitivity. eauto. eapply injp_acc_tl_e. eapply injp_acc_tl_storev; eauto.
   Qed.

   Lemma injp_acci_storev : forall w1 j' m1' m2' Hm' m1'' m2'' Hm'' v tv r tr,
       injp_acci w1 (injpw j' m1' m2' Hm') ->
       Mem.storev Many64 m1' v r = Some m1'' ->
       Val.inject j' v tv ->
       Mem.storev Many64 m2' tv tr = Some m2'' ->
       injp_acci w1 (injpw j' m1'' m2'' Hm'').
   Proof.
     intros.
     etransitivity. eauto. eapply injp_acc_tl_i. eapply injp_acc_tl_storev; eauto.
   Qed.

   Lemma injp_accg_storev : forall w1 j' m1' m2' Hm' m1'' m2'' Hm'' v tv r tr,
       injp_accg w1 (injpw j' m1' m2' Hm') ->
       Mem.storev Many64 m1' v r = Some m1'' ->
       Val.inject j' v tv ->
       Mem.storev Many64 m2' tv tr = Some m2'' ->
       injp_accg w1 (injpw j' m1'' m2'' Hm'').
   Proof.
     intros. eapply injp_accg_acci_accg; eauto. eapply injp_acc_tl_i.
     eapply injp_acc_tl_storev; eauto.
   Qed.
   
   Lemma substep_switch_in : forall i s1' s2' s1'' target m' tm' ttm' f Hmj' Hme' worldsP wpc,
       (* sth more about gtmem'*)
       let cur := CMulti.cur_tid OpenC s1' in
       match_states' i worldsP s1' s2' ->
       NatMap.get cur worldsP = Some wpc -> (** the wpc here is a world at [X] *)
       (forall cqv, CMulti.get_cur_thread OpenC s1' <> Some (CMulti.Initial OpenC cqv)) ->
       gw_acc_yield wpc (tt,(tt,(injpw f m' tm' Hmj',extw tm' ttm' Hme'))) ->
       Mem.tid (Mem.support m') = target ->
       CMulti.switch_in OpenC s1' s1'' target m' -> exists s2'' i',
           AsmMulti.switch_in OpenA s2' s2'' target ttm' /\
             match_states i' s1'' s2''.
   Proof.
   Admitted.
   (*
     intros until wpc. intros cur MS' GETwpc NOTINIT ACCY TID_TARGET SWITCH.
     assert (RANGE: (1 <= target < CMulti.next_tid OpenC s1')%nat).
     {
       inv ACCY. simpl. inv MS'. simpl. simpl in cur. subst cur.
       assert ((injpw f m1 m2 Hm) = wPcur). congruence.
       destruct CUR_INJP_TID. rewrite H1. rewrite <- H. simpl. eauto.
     }
     inv MS'. set (target := Mem.tid (Mem.support m')).
     simpl in cur. subst cur. rename cur0 into cur.
     destruct (Nat.eq_dec cur target).
     - (*switch to self*)
       simpl in RANGE.
       specialize (THREADS target RANGE) as THR_TAR.
       destruct THR_TAR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
       assert (wpc = wP). congruence. subst wpc.
       inv SWITCH.
       + (*yield*)
         assert (lsc = CMulti.Returny OpenC ls1).
         eapply foo; eauto. subst lsc. inv MS. simpl in *.
         assert (get_injp wA = wPcur). congruence. subst wPcur.
         apply FIND_TID in GETWp as X. destruct X as [HwaTid RNGtarget].
         assert (ACCE: injp_acce (get_injp wA) (injpw f m' tm' Hm')).
         eapply injp_acc_yield_acce; eauto.
         set (qc := cr Vundef m').
         set (rs := cajw_rs wA).
         set (rs' := Pregmap.set PC (rs RA) rs).
         set (r_a := (rs', tm')).
         exploit M_REPLIES; eauto. instantiate (1:= r_a). unfold r_a.
         destruct wA. simpl.
         econstructor; eauto.
         intros. unfold rs'.
         destruct r; simpl in H; inv H; repeat rewrite Pregmap.gso;
           simpl; try congruence; try reflexivity.
         intros (li' & sa' & AFT_E' & MLS').
         specialize (get_nth_set (target-1) i li li' GETi) as SETi.
         destruct SETi as (i' & SETi & Newi & OTHERi).
         eexists. exists i'. split.
         (*switch_in*)
         econstructor; eauto.
         (*match*)
         set (wp' := injpw f m' tm' Hm').
         econstructor. instantiate (1:= NatMap.set target (Some wp') worldsP).
         econstructor; simpl. 8:{  rewrite NatMap.gss. reflexivity. }
         all: eauto.
         -- erewrite set_nth_error_length; eauto.
         -- intros. fold target. destruct (Nat.eq_dec 1 target).
            subst target. rewrite e. rewrite NatMap.gss. congruence.
            rewrite NatMap.gso. eauto. eauto.
         -- destruct CUR_INJP_TID as [X Y]. unfold wp'.
            split; eauto.
            inv ACCY. rewrite <- H. simpl. reflexivity.
         -- intros. destruct (Nat.eq_dec n target).
            subst. rewrite NatMap.gss in H. inv H.
            split. reflexivity. lia.
            rewrite NatMap.gso in H.
            exploit FIND_TID; eauto. eauto.
         -- intros.
            instantiate (1:= NatMap.set target None worldsA).
            destruct (Nat.eq_dec n target).
            ++ subst.
               exists wB, None, wp'. eexists. eexists. exists li'.
               repeat apply conj; eauto.
               rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity.
               econstructor; eauto. rewrite NatMap.gss. reflexivity.
               intros. congruence.
            ++ destruct (THREADS n H) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; try rewrite NatMap.gso; eauto.
               rewrite <- OTHERi; eauto. lia.
               intros n1. specialize (J n1). subst wp'.
               eapply injp_accg_yield_accg; eauto. simpl.
               exploit FIND_TID. apply I. intros [X Y]. rewrite X. lia.
       + (*join*)
         assert (lsc = CMulti.Returnj OpenC ls1 tar' vptr).
         eapply foo; eauto. subst lsc. inv MS. simpl in *.
         assert (get_injp wA = wPcur). congruence. subst wPcur.
         apply FIND_TID in GETWp as X. destruct X as [HwaTid RNGtarget].
         assert (ACCE1: injp_acce (get_injp wA) (injpw f m' tm' Hm')).
         eapply injp_acc_yield_acce; eauto.
         specialize (THREADS tar' RNG_WAIT) as THR_TAR'.
         destruct THR_TAR' as (wBt & owAt & wPt & lsct & lsat & lit & GETWt & GETit & MSEwt & GETCt & GETAt & GETWat & MSt & GETWpt & ACCt).         
         assert (lsct = CMulti.Final OpenC res ).   eapply foo; eauto. subst lsct.
         inv MSt.
         exploit ACCt. congruence. intro ACCt'.
         rename gmem'' into m''.
         set (qc := cr (Vint Int.one) m').
         set (rs := cajw_rs wA).
         set (rs' := Pregmap.set RAX (Vint Int.one)(Pregmap.set PC (rs RA) rs)).
         exploit Mem.storev_mapped_inject; eauto.
         eapply val_inject_incr. 2: eauto. unfold get_injp in ACCE1. inv ACCE1. eauto.
         eapply val_inject_incr. 2: eauto. inv ACCt'. simpl. rewrite <- H in ACCE1. inv ACCE1.
         eapply inject_incr_trans. eauto. eauto.
         intros [tm''[MEM_RES' Hm'']].
         set (r_a := (rs', tm'')).
         simpl in *.
         set (wp' := injpw f m'' tm'' Hm'').
         assert (ACCE: injp_acce (get_injp wA) wp').
         {
           simpl in VPTR. destruct wA. simpl in *.
           destruct cajw_injp. unfold wp'. simpl in *.
           eapply injp_acce_storev; eauto.  inv ACCE1. eauto.
         }
         exploit M_REPLIES; eauto. instantiate (1:= r_a). unfold r_a.
         destruct wA. simpl in *.
         econstructor; eauto. rewrite WA_SIG. unfold Conventions1.loc_result.
         replace Archi.ptr64 with true. simpl. unfold rs'. rewrite Pregmap.gss. constructor. eauto.
         intros. unfold rs'.
         destruct r; simpl in H; inv H; repeat rewrite Pregmap.gso;
           simpl; try congruence; try reflexivity.
         intros (li' & sa' & AFT_E' & MLS').
         specialize (get_nth_set (target-1) i li li' GETi) as SETi.
         destruct SETi as (i' & SETi & Newi & OTHERi).
         eexists. exists i'. split.
         (*switch_in*)
         eapply switch_in_join; eauto.
         (*match*)
         econstructor. instantiate (1:= NatMap.set target (Some wp') worldsP).
         econstructor. simpl. 8:{  rewrite NatMap.gss. reflexivity. }
         all: eauto.
         -- erewrite set_nth_error_length; eauto.
         -- intros. fold target. destruct (Nat.eq_dec 1 target).
            subst target. rewrite e. rewrite NatMap.gss. congruence.
            rewrite NatMap.gso. eauto. eauto.
         -- destruct CUR_INJP_TID as [X Y].
            split.
            transitivity (Mem.tid (Mem.support m')). reflexivity. erewrite Mem.support_storev; eauto.
            reflexivity.
            inv ACCY. rewrite <- H. simpl.
            transitivity (Mem.next_tid (Mem.support ((Mem.yield m1 n p)))). reflexivity. erewrite Mem.support_storev; eauto.
         -- intros. destruct (Nat.eq_dec n target).
            subst. rewrite NatMap.gss in H. inv H. split.
            unfold wp'. simpl. erewrite <- Mem.support_storev; eauto. reflexivity. simpl. lia.
            rewrite NatMap.gso in H. eauto. eauto.
         -- intros.
            instantiate (1:= NatMap.set target None worldsA).
            destruct (Nat.eq_dec n target).
            ++ subst.
               exists wB, None, wp'. eexists. eexists. exists li'.
               repeat apply conj; try rewrite NatMap.gss; eauto.
               econstructor; eauto. simpl. intros. congruence.
            ++ destruct (THREADS n H) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; try rewrite NatMap.gso; eauto.
               rewrite <- OTHERi; eauto. lia.
               intros n1. specialize (J n1). simpl in n1. subst wp'. simpl in *.
               eapply injp_accg_acci_accg. eauto.
               eapply injp_acci_storev; eauto.
               eapply injp_acc_yield_acci; eauto. destruct wA. simpl in *.
               inv ACCE1. simpl in VPTR. eauto.
       + (*initial, impossible*)
         simpl in *. exfalso. eapply NOTINIT. eauto.
     -  (*switch to others*)
       
       simpl in RANGE.
       specialize (THREADS target RANGE) as THR_TAR.
       destruct THR_TAR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
       exploit ACC. eauto. intro ACCG.
       inv SWITCH.
       + (*yield*)
         assert (lsc = CMulti.Returny OpenC ls1).
         eapply foo; eauto. subst lsc. inv MS. simpl in *.
         assert (wpc = wPcur). congruence. subst wpc.
         apply FIND_TID in GETWp as X. destruct X as [HwaTid RNGtarget].
         assert (ACCE: injp_acce (get_injp wA) (injpw f m' tm' Hm')).
         eapply injp_accg_yield_acce; eauto.
         set (qc := cr Vundef m').
         set (rs := cajw_rs wA).
         set (rs' := Pregmap.set PC (rs RA) rs).
         set (r_a := (rs', tm')).
         exploit M_REPLIES; eauto. instantiate (1:= r_a). unfold r_a.
         destruct wA. simpl.
         econstructor; eauto.
         intros. unfold rs'.
         destruct r; simpl in H; inv H; repeat rewrite Pregmap.gso;
           simpl; try congruence; try reflexivity.
         intros (li' & sa' & AFT_E' & MLS').
         specialize (get_nth_set (target-1) i li li' GETi) as SETi.
         destruct SETi as (i' & SETi & Newi & OTHERi).
         eexists. exists i'. split.
         (*switch_in*)
         econstructor; eauto.
         (*match*)
         set (wp' := injpw f m' tm' Hm').
         econstructor. instantiate (1:= NatMap.set target (Some wp') worldsP).
         econstructor; simpl. 8:{  rewrite NatMap.gss. reflexivity. }
         all: eauto.
         -- erewrite set_nth_error_length; eauto.
         -- intros. fold target. destruct (Nat.eq_dec 1 target).
            subst target. rewrite e. rewrite NatMap.gss. congruence.
            rewrite NatMap.gso. eauto. eauto.
         -- destruct CUR_INJP_TID as [X Y]. subst wp'.
            split. reflexivity.
            inv ACCY. simpl. reflexivity.
         -- intros. destruct (Nat.eq_dec n0 target).
            subst. rewrite NatMap.gss in H. inv H.
            split. reflexivity. lia.
            rewrite NatMap.gso in H. eauto. eauto.
         -- intros.
            instantiate (1:= NatMap.set target None worldsA).
            destruct (Nat.eq_dec n0 target).
            ++ subst.
               exists wB, None, wp'. eexists. eexists. exists li'.
               repeat apply conj; eauto.
               rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity.
               econstructor; eauto. rewrite NatMap.gss. reflexivity.
               intros. congruence.
            ++ destruct (THREADS n0 H) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; try rewrite NatMap.gso; eauto.
               rewrite <- OTHERi; eauto. lia.
               intros n2. destruct (Nat.eq_dec n0 cur).
               subst. replace wnp with wPcur by congruence.
               eapply injp_yield_acci_accg; eauto. reflexivity. simpl.
               apply FIND_TID in GETwpc. destruct GETwpc as [X Y]. rewrite X.
               lia.
               specialize (J n3).
               eapply injp_accg_yield_accg. eauto. eauto. simpl.
               apply FIND_TID in I. destruct I as [X Y]. rewrite X.
               lia.
       + (*join*)
         assert (lsc = CMulti.Returnj OpenC ls1 tar' vptr).
         eapply foo; eauto. subst lsc. inv MS. simpl in *.
         assert (wpc = wPcur). congruence. subst wpc.
         apply FIND_TID in GETWp as X. destruct X as [HwaTid RNGtarget].
         assert (ACCE1: injp_acce (get_injp wA) (injpw f m' tm' Hm')).
         eapply injp_accg_yield_acce; eauto.
         (* get the waited thread state *)
         specialize (THREADS tar' RNG_WAIT) as THR_TAR'.
         destruct THR_TAR' as (wBt & owAt & wPt & lsct & lsat & lit & GETWt & GETit & MSEwt & GETCt & GETAt & GETWat & MSt & GETWpt & ACCt).         
         assert (lsct = CMulti.Final OpenC res ).   eapply foo; eauto. subst lsct.         
         inv MSt.
         assert (ACCT: injp_accg wPt wPcur \/ wPcur = wPt).
         {
           destruct (Nat.eq_dec tar' cur). subst. right. congruence.
           left. eapply ACCt; eauto.
         }
         rename gmem'' into m''.
         set (qc := cr (Vint Int.one) m').
         set (rs := cajw_rs wA).
         set (rs' := Pregmap.set RAX (Vint Int.one)(Pregmap.set PC (rs RA) rs)).
         exploit Mem.storev_mapped_inject; eauto.
         eapply val_inject_incr. 2: eauto. unfold get_injp in ACCE1. inv ACCE1. eauto.
         eapply val_inject_incr. 2: eauto.
         {
           destruct ACCT. inv ACCY. inv H. eauto.
           inv ACCY. eauto.
         }
         intros [tm''[MEM_RES' Hm'']].
         set (r_a := (rs', tm'')).
         simpl in *.
         set (wp' := injpw f m'' tm'' Hm'').
         assert (ACCE: injp_acce (get_injp wA) wp').
         eapply injp_acce_storev; eauto. destruct wA. simpl in *. inv ACCE1. eauto.
         
         exploit M_REPLIES; eauto. instantiate (1:= r_a). unfold r_a.
         destruct wA. simpl in *.
         econstructor; eauto. rewrite WA_SIG. unfold Conventions1.loc_result.
         replace Archi.ptr64 with true. simpl. unfold rs'. rewrite Pregmap.gss. constructor. eauto.
         intros. unfold rs'.
         destruct r; simpl in H; inv H; repeat rewrite Pregmap.gso;
           simpl; try congruence; try reflexivity.
         intros (li' & sa' & AFT_E' & MLS').
         specialize (get_nth_set (target-1) i li li' GETi) as SETi.
         destruct SETi as (i' & SETi & Newi & OTHERi).
         eexists. exists i'. split.
         (*switch_in*)
         eapply switch_in_join; eauto.
         (*match*)
         econstructor. instantiate (1:= NatMap.set target (Some wp') worldsP).
         econstructor. simpl. 8:{  rewrite NatMap.gss. reflexivity. }
         all: simpl; eauto.
         -- erewrite set_nth_error_length; eauto.
         -- intros. fold target. destruct (Nat.eq_dec 1 target).
            subst target. rewrite e. rewrite NatMap.gss. congruence.
            rewrite NatMap.gso. eauto. eauto.
         -- destruct CUR_INJP_TID as [X Y].
            split.
            transitivity (Mem.tid (Mem.support m')). reflexivity. erewrite Mem.support_storev; eauto.
            inv ACCY. simpl. 
            transitivity (Mem.next_tid (Mem.support ((Mem.yield m1 n0 p)))). reflexivity.
            erewrite Mem.support_storev; eauto.
         -- intros. destruct (Nat.eq_dec n0 target).
            subst. rewrite NatMap.gss in H. inv H.
            unfold wp'. simpl. erewrite <- Mem.support_storev; eauto. split. reflexivity. lia.
            rewrite NatMap.gso in H. eauto. eauto.
         -- intros.
            instantiate (1:= NatMap.set target None worldsA).
            destruct (Nat.eq_dec n0 target).
            ++ subst.
               exists wB, None, wp'. eexists. eexists. exists li'.
               repeat apply conj; try rewrite NatMap.gss; eauto.
               econstructor; eauto. simpl. intros. congruence.
            ++ destruct (THREADS n0 H) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; try rewrite NatMap.gso; eauto.
               rewrite <- OTHERi; eauto. lia.
               intros n2. destruct (Nat.eq_dec n0 cur).
               subst. replace wnp with wPcur by congruence.
               eapply injp_accg_storev.
               eapply injp_acc_yield_accg. eauto. simpl. lia. eauto.
               destruct wA. simpl in *. inv ACCE1. eauto.
               eauto.
               specialize (J n3).
               eapply injp_accg_storev; eauto.
               eapply injp_accg_yield_accg. eauto. eauto. simpl.
               apply FIND_TID in I. destruct I as [X Y]. rewrite X.
               lia. destruct wA. simpl in *. inv ACCE1. eauto.
       + (* initial *)
         assert (lsc = CMulti.Initial OpenC cqv).
         eapply foo; eauto. subst lsc. inv MS. simpl in *.
         assert (wpc = wPcur). congruence. subst wpc.
         exploit ACC. eauto. intro ACCG_wB_wPcur.
         set (wp' := injpw f m' tm' Hm').
         apply FIND_TID in GETWp as X. destruct X as [HwaTid RNGtarget].
         assert (ACCG1: injp_acce (get_injp wB) wp').
         eapply injp_accg_yield_acce; eauto.
         assert (MQ_CUR: cc_c_asm_injp_mq (set_injp wB wp') (get_query cqv m') (rs, tm')).
         {
           clear - M_QUERIES ACCG1 SG_STR.
           inv M_QUERIES. subst targs tsp0.
           assert (Hincr :inject_incr j f).
           inv ACCG1. eauto. 
           econstructor; eauto. rewrite SG_STR in *.
           simpl in *. rewrite start_routine_loc in *. simpl.
           simpl in H5. inv H5. inv H3. constructor; eauto.
           intros. rewrite SG_STR in H. unfold Conventions.size_arguments in H.
           setoid_rewrite start_routine_loc in H. simpl in H. inv H. extlia.
           inv ACCG1. inv H11.
           econstructor. simpl. inv H20. inv unchanged_on_e'.
           eauto.
           inv ACCG1. inv H12. econstructor. destruct H20 as [[_ B] _]. congruence.
           econstructor. rewrite SG_STR. red. unfold Conventions.size_arguments.
           rewrite start_routine_loc. simpl. auto.
         }
         set (wB' := set_injp wB wp').
         assert (MSEw' : injp_match_stbls (cajw_injp wB') se tse).
         {
           
           unfold wB'. destruct wB. simpl in *. inv ACCG1.
           inv MSEw. constructor. eapply Genv.match_stbls_incr_noglobal; eauto.
           destruct H7 as [P [Q R]]. eauto.
           destruct H8 as [P [Q R]]. eauto.
         }
         specialize (fsim_lts se tse wB' MSEw' valid_se) as FSIM.
         inversion FSIM.
         clear fsim_simulation fsim_match_final_states fsim_match_external.
         exploit fsim_match_initial_states.  eauto. eauto. eauto.
         intros (li' & ls' & INIT & MLS').
          specialize (get_nth_set (target-1) i li li' GETi) as SETi.
         destruct SETi as (i' & SETi & Newi & OTHERi).
         eexists. exists i'. split.
         (* switin_in_initial *)
         eapply switch_in_initial. eauto. eauto. eauto.
     (* match_states *)
         econstructor. instantiate (1:= NatMap.set target (Some wp') worldsP).
         econstructor. 6:{ instantiate (2:= NatMap.set target (Some wB') worldsB).
         rewrite NatMap.gso. eauto. congruence. }
         all: simpl; eauto. erewrite set_nth_error_length; eauto.
         intros. destruct (Nat.eq_dec 1 target). subst. congruence.
         rewrite NatMap.gso. eauto. eauto.
         intros. destruct (Nat.eq_dec n0 target) in H0. subst. rewrite NatMap.gss in H0. inv H0.
         unfold wB'. destruct wB. simpl. inv M_QUERIES. eauto. rewrite NatMap.gso in H0. eauto. eauto.        
         rewrite NatMap.gss. reflexivity.
         unfold wp'. simpl. split. eauto.
         destruct CUR_INJP_TID as [X Y]. inv ACCY.
         simpl. reflexivity.
         intros. destruct (Nat.eq_dec n0 target). subst. rewrite NatMap.gss in H.
         inv H. split. reflexivity. lia.
         rewrite NatMap.gso in H. eauto. eauto.
         intros. instantiate (1:= worldsA).
         destruct (Nat.eq_dec n0 target). subst.
         exists wB', None, wp'. eexists. eexists. exists li'.
         repeat apply conj; try rewrite NatMap.gss; eauto.
         econstructor. red. replace wp' with (get wB'). eauto.
         unfold wB'. destruct wB'. simpl. destruct wB. reflexivity.
         intros. congruence.
         destruct (THREADS n0 H) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
         exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; try rewrite NatMap.gso; eauto.
         rewrite <- OTHERi; eauto. lia.
         intros n2. destruct (Nat.eq_dec n0 cur).
         subst. replace wnp with wPcur by congruence.
         eapply injp_acc_yield_accg. eauto. simpl. lia.
         specialize (J n3).
         eapply injp_accg_yield_accg. eauto. eauto. simpl.
         apply FIND_TID in I. destruct I as [X Y]. rewrite X.
         lia.
   Qed.
    *)
     
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
          inv H0. inv H. simpl in *.
          specialize (THREADS cur CUR_VALID) as THR_CUR.
          destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
          assert (lsc = CMulti.Local OpenC ls1).
          eapply foo; eauto. subst lsc. inv MS.
          specialize (fsim_lts se tse wB MSEw valid_se) as FSIM.
          inversion FSIM.
          clear fsim_match_initial_states
            fsim_match_final_states fsim_match_external.
          exploit fsim_simulation; eauto. intros (li' & s2' & STEP & MATCH).
          specialize (get_nth_set (cur-1) i li li' GETi) as SETi.
          destruct SETi as (i' & SETi & Newi & OTHERi). exists i'.
          assert (wP = wPcur). congruence. subst.
          destruct STEP.
          -- eexists. split. left.
             eapply local_plus; eauto. unfold update_cur_thread.
             {
               simpl. econstructor. econstructor. simpl; eauto. simpl.
               erewrite set_nth_error_length; eauto. eauto.
               eauto.
               intros. destruct (Nat.eq_dec 1 cur). subst.
               rewrite NatMap.gss. congruence.
               rewrite NatMap.gso; eauto.
               eauto. eauto.
               instantiate (2:= worldsP). simpl. eauto.
               destruct CUR_INJP_TID. simpl. split; eauto.
               eauto. eauto.
               intros. instantiate (1:= worldsA).
               destruct (Nat.eq_dec n cur).
               - subst.
                 exists wB, None, wPcur, (CMulti.Local OpenC ls2), (Local OpenA s2'), li'.
                 repeat apply conj; eauto. rewrite NatMap.gss. reflexivity.
                 rewrite NatMap.gss. reflexivity. simpl. constructor. eauto.
               - (* clear - THREADS H3 OTHERi n0. *)
                 destruct (THREADS n H3) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
                 exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto. rewrite <- OTHERi; eauto. lia.
                 rewrite NatMap.gso. simpl. eauto. lia.
                 rewrite NatMap.gso. simpl. eauto. lia.
             }
          -- destruct H. eexists. split. right. split. eapply local_star; eauto.
             eapply global_order_decrease; eauto.
             {
               simpl. econstructor. econstructor. simpl; eauto. simpl.
               erewrite set_nth_error_length; eauto.
               eauto. eauto.
               intros. destruct (Nat.eq_dec 1 cur). subst.
               rewrite NatMap.gss. congruence.
               rewrite NatMap.gso; eauto.
               eauto. eauto. eauto. eauto. eauto. eauto.
               intros.
               destruct (Nat.eq_dec n cur).
               - subst.
                 exists wB, None, wPcur, (CMulti.Local OpenC ls2), (Local OpenA s2'), li'.
                 repeat apply conj; eauto. rewrite NatMap.gss. reflexivity.
                 rewrite NatMap.gss. reflexivity. simpl. constructor. eauto.
               - (* clear - THREADS H3 OTHERi n0. *)
                 destruct (THREADS n H4) as (wn & ownA & wp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
                 exists wn, ownA, wp, lscn,lsan,lin. repeat apply conj; eauto. rewrite <- OTHERi; eauto. lia.
                 rewrite NatMap.gso. simpl. eauto. lia.
                 rewrite NatMap.gso. simpl. eauto. simpl. lia.
             }
        + (* pthread_create *)
          inv H0. inv H. subst.
          specialize (THREADS cur CUR_VALID) as THR_CUR.
          destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA &GETWa & MS & GETWp & ACC).
          assert (lsc = CMulti.Local OpenC ls).
          eapply foo; eauto. subst lsc. inv MS.
          specialize (fsim_lts se tse wB MSEw valid_se) as FSIM.
          inversion FSIM.
          clear fsim_match_initial_states
            fsim_match_final_states fsim_simulation.
          exploit fsim_match_external. eauto. eauto.
          intros (wA & qa_ptc & AT_PTC & APP & MQ_PTC & MS & MR).
          exploit trans_pthread_create__start_routine; eauto.
          intros (gw & wA'c & ra_ptc & qa_str & PTR_TO_STR_ASM & ACCGTRANS & ACCG & ACCE &NTID & MR_PTC & MQ_STR &  MS_NT & WORLDS).
          inv WORLDS.
          set (wA'c_injp := {|
                        cajw_injp := injpw j (Mem.yield m' id P1) tm''' Hm2;
                        cajw_sg := start_routine_sig;
                        cajw_rs := ((rs # PC <- (rs RSI)) # RDI <- (rs RDX)) # RSP <- (Vptr sp Ptrofs.zero) |} ).
          assert (wP = wPcur). congruence. subst wP.
          exploit MR; eauto. intros (li' & lsa' & AFTERa & MSla).
          specialize (get_nth_set (cur-1) i li li' GETi).
          intros (i' & SETi' & GETi' & OTHERi).
          set (i'' := i' ++ (li::nil)).
          (** li for new thread is useless, also no effect? hopefully*)
          exists i''. eexists. split.
          -- left. eapply plus_one.
             destruct qa_ptc.
             eapply step_thread_create; eauto. 
          -- (*match_states*)
             simpl.
             set (worlds' := NatMap.set next (Some wA'c) worldsB).
             set (worldsP' := NatMap.set next (Some (get wA'c)) (NatMap.set cur (Some gw) worldsP)).
             assert (LENGTHi'' :Datatypes.length i'' = next).
             unfold i''. rewrite app_length.
             simpl. erewrite set_nth_error_length; eauto. lia.
             econstructor. econstructor. simpl. lia.
             simpl. lia.
             eauto. eauto. simpl. unfold get_cqv. simpl.
             intros. destruct (Nat.eq_dec 1 cur). subst.
               rewrite NatMap.gss. congruence.
               rewrite NatMap.gso; eauto. 
               rewrite NatMap.gso. eauto. lia.
             instantiate (6:= worlds'). unfold worlds'.
             rewrite NatMap.gso. eauto. lia.
             intros. unfold worlds' in H7. destruct (Nat.eq_dec n next).
             subst. rewrite NatMap.gss in H7. inv H7. simpl.
             erewrite w_compcert_sig_eq. rewrite <- H. reflexivity.
             eauto.
             rewrite NatMap.gso in H7. eauto. eauto.
             simpl. instantiate (2:= worldsP').
             unfold worldsP'. rewrite NatMap.gso. rewrite NatMap.gss. reflexivity. lia.
             simpl.
             destruct CUR_INJP_TID as [A B]. 
             simpl. split.

             erewrite gw_acce_tid. 2: eauto.
             erewrite gw_acci_tid; eauto. rewrite NTID.
             f_equal. erewrite gw_acci_nexttid; eauto.
             { (** thread id validity *)
               unfold worldsP'.
               exploit FIND_TID. eauto. intro TIDC.
               intros. destruct (Nat.eq_dec n next).
               - subst. rewrite NatMap.gss in H6.
                 assert (WEQ: get wA'c = wp). congruence.
                 unfold gw_tid. simpl. split.
                 rewrite <- WEQ. rewrite w_get_injp_eq. rewrite <- H. simpl.
                 destruct CUR_INJP_TID as [C D].
                 apply gw_acci_nexttid in APP. rewrite <- D in APP.
                 rewrite <- APP. unfold gw_nexttid. rewrite w_get_injp_eq. rewrite <- H4.
                 simpl. inv Htc1. reflexivity. lia.
               - destruct TIDC as [X Y]. rewrite NatMap.gso in H6. 2:lia.
                 destruct (Nat.eq_dec n cur).
                 +
                   subst. rewrite NatMap.gss in H6. inv H6.
                   split. apply gw_acce_tid in ACCE. rewrite ACCE.
                   apply gw_acci_tid in APP. rewrite APP. reflexivity.
                   simpl. lia.
                 + rewrite NatMap.gso in H6. inv H6.
                   assert (injp_tid (injp_gw_compcert wp) = n).
                   { eapply FIND_TID; eauto. }
                   split. eauto. simpl. rewrite <- H6.
                   exploit FIND_TID; eauto. intros [Z1 Z2]. lia. eauto.
             }
             simpl. eauto. simpl. intros. destruct (Nat.eq_dec n next).
             ++ (* the new thread *) subst.
                instantiate (1:= NatMap.set (Datatypes.length i'') None worldsA).
               exists wA'c. exists None. eexists. eexists. eexists. eexists. repeat apply conj.
                **
                  unfold worlds'. rewrite NatMap.gss. reflexivity.
                **
                  unfold i''.
                  rewrite nth_error_app2. rewrite app_length.
                  simpl.
                  replace (Datatypes.length i' + 1 - 1 - Datatypes.length i')%nat with 0%nat by lia.
                  reflexivity. rewrite app_length. simpl. lia.
                ** eauto.
               ** rewrite NatMap.gso. rewrite NatMap.gss. reflexivity. lia.
               ** rewrite NatMap.gso. rewrite NatMap.gss. reflexivity. lia.
               ** rewrite NatMap.gss. reflexivity.
               ** destruct q_str, qa_str.
                  econstructor. 
                  unfold get_cqv, get_query. eauto.
                  inv H3. reflexivity.
               **
               unfold worldsP'. rewrite NatMap.gss. reflexivity.
               ** intros. eauto.
             ++ destruct (Nat.eq_dec n cur).
          * (*the executing thread *) subst.
            exists wB, None, gw, (CMulti.Local OpenC ls'),(Local OpenA lsa'), li'.
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
            intros. specialize (J H7).
            exploit gw_accg_acci_accg; eauto.
        + (** step_switch *)
          rename s1' into s1''. rename s' into s1'.
          exploit substep_switch_out; eauto.
          intros (s2' & tm' & ttm' & worldsP & wpc & f & Hme' & Hmj' & A & B & C & D & E& F).
          exploit substep_switch_in; eauto.
          intros (s2'' & i' & X & Y).
          exists i', s2''. split. left. eapply plus_one. eapply step_switch; eauto. eauto.
Qed.

  End FSIM.

  Lemma SIM : GS.forward_simulation cc_compcert OpenC OpenA ->
    Closed.forward_simulation ConcurC ConcurA.
  Proof.
    intro. inv H. inv X. eapply Concur_Sim; eauto.
  Qed.

End ConcurSim.

Theorem Opensim_to_Globalsim : forall OpenC OpenA,
    GS.forward_simulation cc_compcert OpenC OpenA ->
    Closed.forward_simulation (Concur_sem_c OpenC) (Concur_sem_asm OpenA).
Proof.
  intros. eapply SIM; eauto.
Qed.
