Require Import Coqlib.
Require Import List.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import SmallstepLinking Smallstep.
Require Import Linking.
Require Import Classical.
Require Import Invariant.

Parameter mem_error : forall liA liB st, lts liA liB st -> st -> Prop.

(** Module safety : similar to the preservation of invariant in LTS *)

Definition safe {liA liB st} (L: lts liA liB st) (s: st) : Prop :=
  (exists r, final_state L s r)
  \/ (exists q, at_external L s q)
  \/ (exists t, exists s', Step L s t s').

Definition partial_safe {liA liB st} (L: lts liA liB st) (s: st) : Prop :=
  (exists r, final_state L s r)
  \/ (exists q, at_external L s q)
  \/ (exists t, exists s', Step L s t s')
  \/ (mem_error liA liB st L s).



Record lts_safe {liA liB S} se (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB) (SI: _ -> S -> Prop) w :=
  {
    step_safe s t s':
      (* SI L s -> *)
      Step L s t s' ->
      SI L s';
    initial_progress q:
      valid_query L q = true ->
      query_inv IB w q ->
      exists s, initial_state L q s;
    initial_safe q s:
      initial_state L q s ->
      SI L s;
    external_safe s q:
      at_external L s q ->
      exists wA, symtbl_inv IA wA se /\ query_inv IA wA q /\
              forall r, reply_inv IA wA r ->
                   (* after external progress *)
                   (exists s', after_external L s r s')
                   (* after external safe *)
                   /\ (forall s', after_external L s r s' -> SI L s');
    final_safe s r:
      final_state L s r ->
      reply_inv IB w r;
  }.


Definition module_safe {liA liB} (L: semantics liA liB) (IA IB: invariant _) SI :=
  forall w se,
    Genv.valid_for (skel L) se ->
    symtbl_inv IB w se ->
    lts_safe se (L se) IA IB SI w.


Lemma safe_internal {li} (I: invariant li) L1 L2: forall i sk se s k w,
    let L := fun (i:bool) => if i then L1 else L2 in
    forall (Hsk: link (skel L1) (skel L2) = Some sk)
      (VALID: Genv.valid_for (skel (SmallstepLinking.semantics L sk)) se)
      (INV : symtbl_inv I w se)
      (VALIDSE: forall i, Genv.valid_for (skel (L i)) se)
      (SAFE: forall i, module_safe (L i) I I safe)
      (STSAFE: safe (L i se) s),
      safe (SmallstepLinking.semantics L sk se) (st L i s :: k).
Proof.
  intros.
  destruct STSAFE as [(r & FINAL)|[(q & EXT)|(t1 & s1 & STEP1)]].
  * destruct k.
    -- left. exists r.
       econstructor. auto.
    -- destruct f.
       right. right.
       do 2 eexists.
       eapply step_pop; eauto.
       (* we need to ensure that all the conts are in at_external states *)
       admit.
  * generalize (external_safe _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) INV) s q EXT).
    intros (wA & SYMBINV & QINV & AFTER).
    destruct (valid_query (L i se) q) eqn: VQ1.
    -- right. right.
       generalize (initial_progress _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) SYMBINV) _ VQ1 QINV).
       intros (initS & INIT).
       do 2 eexists.
       eapply step_push; eauto.
    -- destruct i; simpl in *.
       ++ destruct (valid_query (L2 se) q) eqn: VQ2.
          ** right. right.
             generalize (initial_progress _ _ _ _ _ _ (SAFE false _ _ (VALIDSE false) SYMBINV) _ VQ2 QINV).
             intros (initS & INIT).
             do 2 eexists.
             eapply step_push. eauto.
             instantiate (1 := false). auto.
             simpl. eauto.
          ** right. left.
             eexists. econstructor.
             simpl. eauto.
             intros. destruct j; simpl; auto.
       ++  destruct (valid_query (L1 se) q) eqn: VQ2.
           ** right. right.
              generalize (initial_progress _ _ _ _ _ _ (SAFE true _ _ (VALIDSE true) SYMBINV) _ VQ2 QINV).
              intros (initS & INIT).
              do 2 eexists.
              eapply step_push. eauto.
              instantiate (1 := true). auto.
              simpl. eauto.
           ** right. left.
              eexists. econstructor.
              simpl. eauto.
              intros. destruct j; simpl; auto.
  * right. right. do 2 eexists.
    eapply step_internal. simpl. eauto.
Admitted.

  
Lemma compose_safety {li} (I: invariant li) L1 L2 L:
  module_safe L1 I I safe ->
  module_safe L2 I I safe ->
  compose L1 L2 = Some L ->
  module_safe L I I safe.
Proof.
  intros SAFE1 SAFE2 COMP. unfold compose in *. unfold option_map in *.
  destruct (link (skel L1) (skel L2)) as [sk|] eqn:Hsk; try discriminate. inv COMP.
  set (L := fun i:bool => if i then L1 else L2).
  red. intros w se VALID INV.
  assert (VALIDSE: forall i, Genv.valid_for (skel (L i)) se).
  destruct i.
  eapply Genv.valid_for_linkorder.
  eapply (link_linkorder _ _ _ Hsk). eauto.
  eapply Genv.valid_for_linkorder.
  eapply (link_linkorder _ _ _ Hsk). eauto.
  assert (SAFE: forall i, module_safe (L i) I I safe).
  destruct i; simpl; auto.
    
  constructor.
  - intros s t s' STEP.
    inv STEP.
    + (* destruct i; simpl in H. *)
      assert (A: safe (L i se) s0). right. right. eauto.
      assert (B: safe (L i se) s'0). {
        eapply step_safe. eapply SAFE; eauto. eauto. }
      eapply safe_internal; eauto.
      destruct B as [(r & FINAL)|[(q & EXT)|(t1 & s1 & STEP1)]].
      * destruct k.
        -- left. exists r.
           econstructor. auto.
        -- destruct f.
           right. right.
           do 2 eexists.
           eapply step_pop; eauto.
           (* we need to ensure that all the conts are in at_external states *)
           admit.
      * generalize (external_safe _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) INV) s'0 q EXT).
        intros (wA & SYMBINV & QINV & AFTER).
        destruct (valid_query (L i se) q) eqn: VQ1.
        -- right. right.
           generalize (initial_progress _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) SYMBINV) _ VQ1 QINV).
           intros (initS & INIT).
           do 2 eexists.
           eapply step_push; eauto.
        -- destruct i; simpl in *.
           ++ destruct (valid_query (L2 se) q) eqn: VQ2.
              ** right. right.
                 generalize (initial_progress _ _ _ _ _ _ (SAFE2 _ _ (VALIDSE false) SYMBINV) _ VQ2 QINV).
                 intros (initS & INIT).
                 do 2 eexists.
                 eapply step_push. eauto.
                 instantiate (1 := false). auto.
                 simpl. eauto.
              ** right. left.
                 eexists. econstructor.
                 simpl. eauto.
                 intros. destruct j; simpl; auto.
           ++  destruct (valid_query (L1 se) q) eqn: VQ2.
               ** right. right.
                  generalize (initial_progress _ _ _ _ _ _ (SAFE1 _ _ (VALIDSE true) SYMBINV) _ VQ2 QINV).
                  intros (initS & INIT).
                  do 2 eexists.
                  eapply step_push. eauto.
                  instantiate (1 := true). auto.
                  simpl. eauto.
               ** right. left.
                  eexists. econstructor.
                  simpl. eauto.
                  intros. destruct j; simpl; auto.
      * right. right. do 2 eexists.
        eapply step_internal. simpl. eauto.
        
    (* step_push *)
    + assert (A: safe (L i se) s0). right. left. eauto.
      assert (B: safe (L j se) s'0).
      eapply initial_safe. eapply SAFE; eauto. eauto.
      destruct B as [(r & FINAL)|[(q1 & EXT)|(t1 & s1 & STEP1)]].
      * generalize (external_safe _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) INV) s0 q H).
        intros (wA & SYMBINV & QINV & AFTER).      
        right. right.
        generalize (final_safe _ _ _ _ _ _ (SAFE j _ _ (VALIDSE j) SYMBINV) _ _ FINAL).
        intros VREP.
        generalize (AFTER r VREP).
        intros ((s' & AFTER1) & C).
        do 2 eexists.
        eapply step_pop; eauto.

      (** TODO: same as above  *)
      * generalize (external_safe _ _ _ _ _ _ (SAFE j _ _ (VALIDSE j) INV) s'0 q1 EXT).
        intros (wA & SYMBINV & QINV & AFTER).
        destruct (valid_query (L i se) q1) eqn: VQ1.
        -- right. right.
           generalize (initial_progress _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) SYMBINV) _ VQ1 QINV).
           intros (initS & INIT).
           do 2 eexists.
           eapply step_push; eauto.
        -- destruct i; simpl in *.
           ++ destruct (valid_query (L2 se) q1) eqn: VQ2.
              ** right. right.
                 generalize (initial_progress _ _ _ _ _ _ (SAFE2 _ _ (VALIDSE false) SYMBINV) _ VQ2 QINV).
                 intros (initS & INIT).
                 do 2 eexists.
                 eapply step_push. eauto.
                 instantiate (1 := false). auto.
                 simpl. eauto.
              ** right. left.
                 eexists. econstructor.
                 eauto.
                 intros. destruct j0; simpl; auto.
           ++  destruct (valid_query (L1 se) q1) eqn: VQ2.
               ** right. right.
                  generalize (initial_progress _ _ _ _ _ _ (SAFE1 _ _ (VALIDSE true) SYMBINV) _ VQ2 QINV).
                  intros (initS & INIT).
                  do 2 eexists.
                  eapply step_push. eauto.
                  instantiate (1 := true). auto.
                  simpl. eauto.
               ** right. left.
                  eexists. econstructor.
                  simpl. eauto.
                  intros. destruct j0; simpl; auto.
      * right. right. do 2 eexists.
        eapply step_internal. simpl. eauto.

    (* step_pop *)
    + assert (ATEXT: exists q, at_external (L j se) sk0 q).
      admit. (* we need to ensure that all the conts are in at_external states *)
      destruct ATEXT as (q & ATEXT).
      generalize (external_safe _ _ _ _ _ _ (SAFE j _ _ (VALIDSE j) INV) sk0 q ATEXT).
      intros (wA & SYMBINV & QINV & AFTER).
      generalize (final_safe _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) SYMBINV) _ _ H).
      intros VR.
      generalize (AFTER r VR).
      intros ((s' & AFTER1) & C).
      assert (B: safe (L j se) s'0). eapply C. eauto.
      destruct B as [(r1 & FINAL)|[(q1 & EXT)|(t1 & s1 & STEP1)]].
      * destruct k.
        -- left. exists r1.
           econstructor. auto.
        -- destruct f.
           right. right.
           do 2 eexists.
           eapply step_pop; eauto.
           (* we need to ensure that all the conts are in at_external states *)
           admit.

      (** TODO: same as above  *)
      * generalize (external_safe _ _ _ _ _ _ (SAFE j _ _ (VALIDSE j) INV) s'0 q1 EXT).
        intros (wA1 & SYMBINV1 & QINV1 & AFTER2).
        destruct (valid_query (L i se) q1) eqn: VQ1.
        -- right. right.
           generalize (initial_progress _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) SYMBINV1) _ VQ1 QINV1).
           intros (initS & INIT).
           do 2 eexists.
           eapply step_push; eauto.
        -- destruct i; simpl in *.
           ++ destruct (valid_query (L2 se) q1) eqn: VQ2.
              ** right. right.
                 generalize (initial_progress _ _ _ _ _ _ (SAFE2 _ _ (VALIDSE false) SYMBINV1) _ VQ2 QINV1).
                 intros (initS & INIT).
                 do 2 eexists.
                 eapply step_push. eauto.
                 instantiate (1 := false). auto.
                 simpl. eauto.
              ** right. left.
                 eexists. econstructor.
                 eauto.
                 intros. destruct j0; simpl; auto.
           ++  destruct (valid_query (L1 se) q1) eqn: VQ2.
               ** right. right.
                  generalize (initial_progress _ _ _ _ _ _ (SAFE1 _ _ (VALIDSE true) SYMBINV1) _ VQ2 QINV1).
                  intros (initS & INIT).
                  do 2 eexists.
                  eapply step_push. eauto.
                  instantiate (1 := true). auto.
                  simpl. eauto.
               ** right. left.
                  eexists. econstructor.
                  simpl. eauto.
                  intros. destruct j0; simpl; auto.
      * right. right. do 2 eexists.
        eapply step_internal. simpl. eauto.

  (* initial_progress *)
  - intros q VQ SQ. simpl in *.
    unfold SmallstepLinking.valid_query in VQ.
    simpl in *.
    destruct (valid_query (L1 se) q) eqn: VQ1.
    + generalize (initial_progress _ _ _ _ _ _ (SAFE true _ _ (VALIDSE true) INV) _ VQ1 SQ).
      intros (s & INIT).
      exists (st L true s :: nil). econstructor; eauto.
    + rewrite orb_false_l in VQ.
      generalize (initial_progress _ _ _ _ _ _ (SAFE false _ _ (VALIDSE false) INV) _ VQ SQ).
      intros (s & INIT).
      exists (st L false s :: nil). econstructor; eauto.
  (* initial_safe *)
  - intros q s INIT.
    inv INIT.    
    generalize (initial_safe _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) INV) q s0 H0).
    intros A.
    (* repeated work *)
    eapply safe_internal; eauto.
  - intros s q EXT. inv EXT.
    generalize (external_safe _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) INV) s0 q H).
    intros (wA & SYMBINV & QINV & AFTER).
    exists wA. split; auto. split; auto.
    intros r SR.
    generalize (AFTER r SR).
    intros ((s' & AFTER1) & C).
    split. exists (st L i s' :: k). econstructor; eauto.
    intros s1' AFTER2. simpl in *. inv AFTER2. 
    eapply inj_pair2 in H3. subst.
    generalize (C s'0 H6). intros D.
    (* repeated work *)
    eapply safe_internal; eauto.
  - intros s r FINAL. simpl in *.
    inv FINAL.
    generalize (final_safe _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) INV) _ _ H).
    auto.
Admitted.    
