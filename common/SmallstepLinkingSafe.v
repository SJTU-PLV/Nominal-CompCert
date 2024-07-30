Require Import Coqlib.
Require Import List.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import SmallstepLinking Smallstep.
Require Import Linking.
Require Import Classical.
Require Import Invariant.

(** Module safety : similar to the preservation of invariant in LTS *)

Definition safe {liA liB st} (L: lts liA liB st) (s: st) : Prop :=
  (exists r, final_state L s r)
  \/ (exists q, at_external L s q)
  \/ (exists t, exists s', Step L s t s').

(* Definition partial_safe {liA liB st} mem_error (L: lts liA liB st) (s: st) : Prop := *)
(*   (exists r, final_state L s r) *)
(*   \/ (exists q, at_external L s q) *)
(*   \/ (exists t, exists s', Step L s t s') *)
(*   \/ (mem_error liA liB st L s). *)


(** TODO: generalize safe/partial_safe to module linking and show that
the original safe/partial_safe is identical to the composed
safe/partial_safe *)

Record lts_safe {liA liB S} se (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB) (SI: _ -> S -> Prop) w :=
  {
    step_safe s t s' (REACH: reachable L s):
      (* SI L s -> *)
      Step L s t s' ->
      SI L s';
    initial_safe q:
      valid_query L q = true ->
      query_inv IB w q ->
      (* initial_progress *)
      (exists s, initial_state L q s)
      (* initial_safe *)
      /\ (forall s, initial_state L q s -> SI L s);
    external_safe s q (REACH: reachable L s):
      at_external L s q ->
      exists wA, symtbl_inv IA wA se /\ query_inv IA wA q /\
              forall r, reply_inv IA wA r ->
                   (* after external progress *)
                   (exists s', after_external L s r s')
                   (* after external safe *)
                   /\ (forall s', after_external L s r s' -> SI L s');
    final_safe s r (REACH: reachable L s):
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
      (STSAFE: safe (L i se) s)
      (WFSTATE: wf_state L se (st L i s :: k)),
      safe (SmallstepLinking.semantics L sk se) (st L i s :: k).
Proof.
  intros.
  destruct STSAFE as [(r & FINAL)|[(q & EXT)|(t1 & s1 & STEP1)]].
  * destruct k.
    -- left. exists r.
       econstructor. auto.
    -- destruct f.
       right. right.
       (* s0 in in at_external state *)
       inv WFSTATE. subst_dep. inv H3. inv H2. subst_dep.
       generalize (external_safe _ _ _ _ _ _ (SAFE i0 _ _ (VALIDSE i0) INV) s0 q H5 H3).
       intros (wA & SYMBINV & QINV & AFTER).
       generalize (final_safe _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) SYMBINV) _ _ H1 FINAL).
       intros WR.
       generalize (AFTER _ WR).
       intros ((s0' & AFTER1) & SAFTER).
       do 2 eexists.
       eapply step_pop; eauto.
  * inv WFSTATE. subst_dep.
    generalize (external_safe _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) INV) s q H1 EXT).
    intros (wA & SYMBINV & QINV & AFTER).
    destruct (valid_query (L i se) q) eqn: VQ1.
    -- right. right.
       generalize (initial_safe _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) SYMBINV) _ VQ1 QINV).
       intros ((initS & INIT) & INITSAFE).
       do 2 eexists.
       eapply step_push; eauto.
    -- destruct i; simpl in *.
       ++ destruct (valid_query (L2 se) q) eqn: VQ2.
          ** right. right.
             generalize (initial_safe _ _ _ _ _ _ (SAFE false _ _ (VALIDSE false) SYMBINV) _ VQ2 QINV).
             intros ((initS & INIT) & INITSAFE).
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
              generalize (initial_safe _ _ _ _ _ _ (SAFE true _ _ (VALIDSE true) SYMBINV) _ VQ2 QINV).
              intros ((initS & INIT) & INITSAFE).
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
Qed.
  
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
  - intros s t s' REACH STEP.
    eapply reachable_wf_state in REACH.
    inv STEP.
    + (* destruct i; simpl in H. *)
      assert (A: safe (L i se) s0). right. right. eauto.
      assert (B: safe (L i se) s'0). {
        eapply step_safe; eauto. eapply SAFE; eauto.
        inv REACH. subst_dep. auto. }
      eapply safe_internal; eauto.
      inv REACH. subst_dep. econstructor;eauto. eapply step_reachable; eauto.
    (* step_push *)
    + assert (A: safe (L i se) s0). right. left. eauto.
      assert (B: safe (L j se) s'0).
      { inv REACH. subst_dep.
        generalize (external_safe _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) INV) s0 q H4 H).
        intros (wA & SYMBINV & QINV & AFTER).
        eapply initial_safe. eapply SAFE; eauto. eauto. auto. auto. }
      eapply safe_internal;eauto.
      constructor; eauto. econstructor; eauto.
      eapply star_refl.
      inv REACH. subst_dep. econstructor;eauto.
      econstructor;eauto.
    (* step_pop *)
    + inv REACH. inv H5. subst_dep.
      inv H6. subst_dep.
      assert (ATEXT: exists q, at_external (L j se) sk0 q).
      eauto.
      destruct ATEXT as (q1 & ATEXT).
      generalize (external_safe _ _ _ _ _ _ (SAFE j _ _ (VALIDSE j) INV) sk0 q1 H5 ATEXT).
      intros (wA & SYMBINV & QINV & AFTER).
      generalize (final_safe _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) SYMBINV) _ _ H3 H).
      intros VR.
      generalize (AFTER r VR).
      intros ((s' & AFTER1) & C).
      assert (B: safe (L j se) s'0). eapply C. eauto.
      eapply safe_internal; eauto.
      econstructor;eauto. eapply external_reach. eapply H5. eapply H0.
      eapply star_refl.
  (* initial_safe *)
  - intros q VQ SQ. simpl in *.
    unfold SmallstepLinking.valid_query in VQ.
    simpl in *. split.
    + (* progress *)
      destruct (valid_query (L1 se) q) eqn: VQ1.
      * generalize (initial_safe _ _ _ _ _ _ (SAFE true _ _ (VALIDSE true) INV) _ VQ1 SQ).
        intros ((s & INIT) & INITSAFE).
        exists (st L true s :: nil). econstructor; eauto.
      * rewrite orb_false_l in VQ.
        generalize (initial_safe _ _ _ _ _ _ (SAFE false _ _ (VALIDSE false) INV) _ VQ SQ).
        intros ((s & INIT) & INITSAFE).
        exists (st L false s :: nil). econstructor; eauto.
    + (* safe *)
      intros s INIT.
      inv INIT.
      generalize (initial_safe _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) INV) _ H SQ).
      intros ((s & INIT) & INITSAFE).
      (* repeated work *)
      clear INIT.
      eapply safe_internal; eauto.
      econstructor. eapply initial_reach; eauto.
      eapply star_refl. constructor.  
  - intros s q REACH EXT. inv EXT.
    eapply reachable_wf_state in REACH. inv REACH. subst_dep.
    generalize (external_safe _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) INV) s0 q H3 H).
    intros (wA & SYMBINV & QINV & AFTER).
    exists wA. split; auto. split; auto.
    intros r SR.
    generalize (AFTER r SR).
    intros ((s' & AFTER1) & C).
    split. exists (st L i s' :: k). econstructor; eauto.
    intros s1' AFTER2. simpl in *. inv AFTER2. 
    subst_dep.
    generalize (C s'0 H8). intros D.
    (* repeated work *)
    eapply safe_internal; eauto.
    econstructor; eauto. eapply external_reach; eauto.
    eapply star_refl.    
  - intros s r REACH FINAL.
    inv FINAL.
    apply reachable_wf_state in REACH. inv REACH. subst_dep.
    generalize (final_safe _ _ _ _ _ _ (SAFE i _ _ (VALIDSE i) INV) _ _ H2 H).
    auto.
Qed.
