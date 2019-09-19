Require Import CKLR.
Require Import Axioms.
Require Import Inject.

(** * Self-injection as a CKLR *)

Global Instance block_le_preo:
  PreOrder Block.le.
Proof.
  split.
  - exact Block.le_refl.
  - exact Block.le_trans.
Qed.

Global Instance mem_flat_inj_incr:
  Monotonic (@Mem.flat_inj) (Block.le ++> inject_incr).
Proof.
  unfold Mem.flat_inj. repeat rstep.
  intros b b' delta Hb.
  destruct (Block.lt_dec b x); inv Hb.
  destruct (Block.lt_dec b' y); try blomega.
  elim n. blomega.
Qed.

Program Definition injn: cklr :=
  {|
    world := block;
    wacc := Block.le;
    mi := Mem.flat_inj;
    match_mem w := (match_mem inj (Mem.flat_inj w) /\ req w @@ Mem.nextblock)%rel;
  |}.

Next Obligation.
  destruct H as [H _].
  apply (cklr_wf inj (Mem.flat_inj w) m1 m2); eauto.
Qed.

Next Obligation. (* Mem.alloc *)
  intros nb m1 m2 [[Hm Hwf] Hnb] lo hi.
  destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn:Hm1'.
  edestruct Mem.alloc_parallel_inject
    as (f' & m2' & b2 & Hm2' & Hm' & Hf'' & Hb2 & Hf');
    eauto using Zle_refl.
  rewrite Hm2'.
  exists (Block.succ (Mem.nextblock m1)); split; repeat rstep.
  - destruct Hnb. simpl. blomega.
  - split.
    + replace (Mem.flat_inj (Block.succ (Mem.nextblock m1))) with f'; eauto.
      {
        split; eauto.
        split.
        - transitivity (Mem.flat_inj nb); eauto.
          apply meminj_wf_incr; eauto.
        - intros x y [d Hxy] Hy.
          destruct (Block.eq x b1); subst.
          * assert (y = b2) by congruence; subst.
            eapply Mem.alloc_result in Hm2'; subst.
            elim (Block.lt_strict Block.init).
            eapply Block.le_lt_trans; eauto.
            apply Mem.init_nextblock.
          * rewrite Hf' in Hxy by eauto.
            eapply meminj_wf_img; eauto.
      }
      eapply functional_extensionality; intros b.
      apply Mem.alloc_result in Hm1'.
      apply Mem.alloc_result in Hm2'.
      destruct Hnb. subst.
      specialize (Hf' b).
      unfold Mem.flat_inj in Hf' |- *.
      destruct (Block.lt_dec b nb).
      * destruct (Block.lt_dec b (Block.succ nb)).
        apply Hf'; solve [blomega].
        elim n; blomega.
      * destruct (Block.lt_dec b (Block.succ nb)).
        apply Block.lt_succ_inv in l. destruct l; [contradiction | congruence].
        apply Block.nlt_le in n0.
        assert (Block.lt nb b) by blomega.
        apply Blt_ne in H. eauto.
    + apply Mem.nextblock_alloc in Hm1'.
      apply Mem.nextblock_alloc in Hm2'.
      red. rewrite Hm1', Hm2'. destruct Hnb. constructor.
  - apply Mem.alloc_result in Hm1'.
    apply Mem.alloc_result in Hm2'.
    rewrite <- Hm1'. destruct Hnb. subst.
    red. unfold Mem.flat_inj.
    destruct Block.lt_dec; eauto.
    elim n; blomega.
Qed.

Next Obligation. (* Mem.free *)
  intros nb m1 m2 [[Hm Hwf] Hnb] [[b1 lo1] hi1] [[b2 lo2] hi2] Hr.
  simpl. red.
  destruct (Mem.free m1 b1 lo1 hi1) as [m1'|] eqn:Hm1'; [|rauto].
  inv Hr. inv H0.
  edestruct Mem.free_parallel_inject as (m2' & Hm2' & Hm'); eauto.
  replace (lo1 + delta + sz) with (lo1 + sz + delta) by xomega.
  rewrite Hm2'. rstep.
  exists nb; split; [rauto|].
  split; [rauto|].
  apply Mem.nextblock_free in Hm1'.
  apply Mem.nextblock_free in Hm2'.
  destruct Hnb. red. rewrite Hm1', Hm2'. constructor.
Qed.

Next Obligation. (* Mem.load *)
  pose proof (cklr_load inj). repeat rstep.
  destruct H0 as [[? ?] ?]; eauto.
  destruct H0 as [[? ?] ?]; eauto.
Qed.

Next Obligation. (* Mem.store *)
  intros nb chunk m1 m2 [[Hm Hwf] Hnb] _ _ [b1 ofs1 b2 delta Hptr] v1 v2 Hv.
  simpl. red.
  destruct (Mem.store chunk m1 b1 ofs1 v1) as [m1'|] eqn:Hm1'; [|rauto].
  edestruct Mem.store_mapped_inject as (m2' & Hm2' & Hm'); eauto.
  rewrite Hm2'. rstep.
  exists nb; split; [rauto|].
  split; [rauto|].
  apply Mem.nextblock_store in Hm1'.
  apply Mem.nextblock_store in Hm2'.
  destruct Hnb. red. rewrite Hm1', Hm2'. constructor.
Qed.

Next Obligation. (* Mem.loadbytes *)
  intros nb m1 m2 [[Hm Hwf] Hnb] _ _ [b1 ofs1 b2 delta Hptr] sz.
  simpl. red.
  destruct (Mem.loadbytes m1 b1 ofs1 sz) as [vs1|] eqn:Hvs1; [|rauto].
  edestruct Mem.loadbytes_inject as (vs2 & Hvs2 & Hvs); eauto.
  rewrite Hvs2. rauto.
Qed.

Next Obligation. (* Mem.storebytes *)
  intros nb m1 m2 [[Hm Hwf] Hnb] [b1 ofs1] [b2 ofs2] Hptr vs1 vs2 Hvs.
  simpl. red.
  destruct (Mem.storebytes m1 _ _ _) as [m1'|] eqn:Hm1'; [|constructor].
  assert (vs1 = nil \/ vs1 <> nil) as [Hvs1|Hvs1].
  { destruct vs1; constructor; congruence. }
  - subst. inv Hvs.
    edestruct (Mem.range_perm_storebytes m2 b2 ofs2 nil) as [m2' Hm2'].
    {
      intros ofs. simpl. xomega.
    }
    rewrite Hm2'.
    constructor.
    exists nb; split; try rauto.
    split.
    + split; eauto.
      eapply Mem.storebytes_empty_inject; eauto.
    + red.
      apply Mem.nextblock_storebytes in Hm1'. rewrite Hm1'.
      apply Mem.nextblock_storebytes in Hm2'. rewrite Hm2'.
      assumption.
  - assert (ptr_inject (Mem.flat_inj nb) (b1, ofs1) (b2, ofs2)) as Hptr'.
    {
      destruct Hptr as [Hptr|Hptr]; eauto.
      inversion Hptr as [_ _ [xb1 xofs1 xb2 delta Hb]]; clear Hptr; subst.
      unfold ptrbits_unsigned.
      erewrite Mem.address_inject; eauto.
      apply Mem.storebytes_range_perm in Hm1'.
      eapply Hm1'.
      destruct vs1; try congruence.
      simpl. xomega.
    }
    inv Hptr'.
    edestruct Mem.storebytes_mapped_inject as (m2' & Hm2' & Hm'); eauto.
    rewrite Hm2'. repeat rstep.
    exists nb; split; [rauto|].
    split; [rauto|].
    red.
    apply Mem.nextblock_storebytes in Hm1'. rewrite Hm1'.
    apply Mem.nextblock_storebytes in Hm2'. rewrite Hm2'.
    assumption.
Qed.

Next Obligation. (* Mem.perm *)
  intros nb m1 m2 [[Hm Hwf] Hnb] _ _ [b1 ofs1 b2 delta Hb] p k H.
  eapply Mem.perm_inject; eauto.
Qed.

Next Obligation. (* Mem.valid_block *)
  intros nb m1 m2 [[Hm Hwf] Hnb] b1 b2 [delta Hb].
  split; intro.
  - eapply Mem.valid_block_inject_2; eauto.
  - eapply Mem.valid_block_inject_1; eauto.
Qed.

Next Obligation. (* Mem.meminj_no_overlap *)
  destruct H as [[? ?] ?].
  eapply Mem.mi_no_overlap; rauto.
Qed.

Next Obligation. (* representable *)
  destruct H as [[? ?] ?].
  rewrite <- (Ptrofs.unsigned_repr ofs1) by xomega.
  eapply Mem.mi_representable; try rauto.
  rewrite Ptrofs.unsigned_repr by xomega.
  assumption.
Qed.

Next Obligation.
  destruct H as [[? ?] ?].
  eapply Mem.aligned_area_inject; rauto.
Qed.

Next Obligation. 
  destruct H as [[? ?] ?].
  eapply Mem.disjoint_or_equal_inject; rauto.
Qed.
