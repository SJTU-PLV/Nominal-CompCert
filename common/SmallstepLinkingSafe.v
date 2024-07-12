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


Record lts_safe {liA liB S} se (L: lts liA liB S) IA IB (SI: _ -> S -> Prop) w :=
  {
    step_safe s t s':
      SI L s ->
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
      SI L s -> at_external L s q ->
      exists wA, symtbl_inv IA wA se /\ query_inv IA wA q /\
              forall r, reply_inv IA wA r ->
                   (* after external progress *)
                   (exists s', after_external L s r s')
                   (* after external safe *)
                   /\ (forall s', after_external L s r s' -> SI L s');
    final_safe s r:
      SI L s ->
      final_state L s r ->
      reply_inv IB w r;
  }.


Definition module_safe {liA liB} (L: semantics liA liB) (IA IB: invariant _) SI :=
  forall w se,
    Genv.valid_for (skel L) se ->
    symtbl_inv IB w se ->
    lts_safe se (L se) IA IB SI w.

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
  (* exploit SAFE1. eapply Genv.valid_for_linkorder. *)
  (* eapply (link_linkorder _ _ _ Hsk). eauto. eauto. *)
  (* intros LTSSAFE1. *)
  (* exploit SAFE2. eapply Genv.valid_for_linkorder. *)
  (* eapply (link_linkorder _ _ _ Hsk). eauto. eauto. *)
  (* intros LTSSAFE2. *)
  assert (VALIDSE1: Genv.valid_for (skel L1) se).
  eapply Genv.valid_for_linkorder.
  eapply (link_linkorder _ _ _ Hsk). eauto.
  assert (VALIDSE2: Genv.valid_for (skel L2) se).
  eapply Genv.valid_for_linkorder.
  eapply (link_linkorder _ _ _ Hsk). eauto.
  
  constructor.
  - intros s t s' SIS STEP.
    inv STEP.
    + (* destruct i; simpl in H. *)
      assert (A: safe (L i se) s0). right. right. eauto.
      assert (B: safe (L i se) s'0). {
        destruct i; simpl in *.
        eapply step_safe. eapply SAFE1; eauto. eauto. eauto.
        eapply step_safe. eapply SAFE2; eauto. eauto. eauto. }
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
      * destruct (valid_query (L i se) q) eqn: VQ1.
        -- right. right.
           assert (C: safe (L i se) s'0). right. left. eauto.
           destruct i; simpl in *.
           ++ generalize (external_safe _ _ _ _ _ _ (SAFE1 _ _ VALIDSE1 INV) s'0 q C EXT).
              intros (wA & SYMBINV & QINV & AFTER).
              generalize (initial_progress _ _ _ _ _ _ (SAFE1 _ _ VALIDSE1 SYMBINV) _ VQ1 QINV).
              intros (initS & INIT).
              do 2 eexists.
              eapply step_push. eauto.
              instantiate (1 := true). auto.
              simpl. eauto.
           ++ generalize (external_safe _ _ _ _ _ _ (SAFE2 _ _ VALIDSE2 INV) s'0 q C EXT).
              intros (wA & SYMBINV & QINV & AFTER).
              generalize (initial_progress _ _ _ _ _ _ (SAFE2 _ _ VALIDSE2 SYMBINV) _ VQ1 QINV).
              intros (initS & INIT).
              do 2 eexists.
              eapply step_push. eauto.
              instantiate (1 := false). auto.
              simpl. eauto.              
        -- destruct i; simpl in *.
           ++ destruct (valid_query (L2 se) q) eqn: VQ2.
              ** right. right.
                 assert (C: safe (L1 se) s'0). right. left. eauto.
                 generalize (external_safe _ _ _ _ _ _ (SAFE1 _ _ VALIDSE1 INV) s'0 q C EXT).
                 intros (wA & SYMBINV & QINV & AFTER).
                 generalize (initial_progress _ _ _ _ _ _ (SAFE2 _ _ VALIDSE2 SYMBINV) _ VQ2 QINV).
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
                  assert (C: safe (L2 se) s'0). right. left. eauto.
                  generalize (external_safe _ _ _ _ _ _ (SAFE2 _ _ VALIDSE2 INV) s'0 q C EXT).
                  intros (wA & SYMBINV & QINV & AFTER).
                  generalize (initial_progress _ _ _ _ _ _ (SAFE1 _ _ VALIDSE1 SYMBINV) _ VQ2 QINV).
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
    + assert (A: safe (L j se) s'0).
      destruct j; simpl in *.
      eapply initial_safe. eapply SAFE1; eauto. eauto.
      eapply initial_safe. eapply SAFE2; eauto. eauto.
      destruct A as [(r & FINAL)|[(q1 & EXT)|(t1 & s1 & STEP1)]].
      * right. right. do 2 eexists.
        eapply step_pop; eauto.
        (** we need to ensure that all the conts are in at_external states *)
        admit.
      * assert (B: safe (L j se) s'0). {
          destruct j; simpl in *.
          eapply initial_safe. eapply SAFE1; eauto. eauto.
          eapply initial_safe. eapply SAFE2; eauto. eauto. }

        
        assert (C: query_inv 
        
        generalize (external_safe _ _ _ _ _ _ (SAFE2 _ _ VALIDSE2 INV) s'0 q C EXT).

