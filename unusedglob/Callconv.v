Require Export LogicalRelations.
Require Export KLR.
Require Export OptionRel.
Require Export BoolRel.
Require Export Valuesrel.

Require Import Coqlib.
Require Import Integers.
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import LanguageInterface.

Record cklr' :=
  {
    world: Type;
    wacc: relation world;

    cklr_kf : KripkeFrame unit world := {| acc w := wacc; |};

    mi: world -> meminj;
    match_mem: klr world mem mem;
    match_stbls: klr world Genv.symtbl Genv.symtbl;

    acc_preorder:
      PreOrder wacc;

    mi_acc:
      Monotonic mi (wacc ++> inject_incr);
    mi_acc_separated w w' m1 m2:
      match_mem w m1 m2 ->
      wacc w w' ->
      inject_separated (mi w) (mi w') m1 m2;

    match_stbls_acc:
      Monotonic match_stbls (wacc ++> subrel);
    match_stbls_proj w:
      Related (match_stbls w) (Genv.match_stbls' (mi w)) subrel;
    match_stbls_support w se1 se2 m1 m2:
      match_stbls w se1 se2 ->
      match_mem w m1 m2 ->
      Mem.sup_include (Genv.genv_sup se1) (Mem.support m1) ->
      Mem.sup_include (Genv.genv_sup se2) (Mem.support m2);

    cklr_alloc:
      Monotonic
        (@Mem.alloc)
        (|= match_mem ++> - ==> - ==>
         <> match_mem * block_inject_sameofs @@ [mi]);

    cklr_free:
      Monotonic
        (@Mem.free)
        (|= match_mem ++> %% ptrrange_inject @@ [mi] ++>
         k1 option_le (<> match_mem));

    cklr_load:
      Monotonic
        (@Mem.load)
        (|= - ==> match_mem ++> % ptr_inject @@ [mi] ++>
         k1 option_le (Val.inject @@ [mi]));

    cklr_store:
      Monotonic
        (@Mem.store)
        (|= - ==> match_mem ++> % ptr_inject @@ [mi] ++> Val.inject @@ [mi] ++>
         k1 option_le (<> match_mem));

    cklr_loadbytes:
      Monotonic
        (@Mem.loadbytes)
        (|= match_mem ++> % ptr_inject @@ [mi] ++> - ==>
         k1 option_le (k1 list_rel (memval_inject @@ [mi])));

    cklr_storebytes:
      Monotonic
        (@Mem.storebytes)
        (|= match_mem ++> % rptr_inject @@ [mi] ++>
         k1 list_rel (memval_inject @@ [mi]) ++>
         k1 option_le (<> match_mem));

    cklr_perm:
      Monotonic
        (@Mem.perm)
        (|= match_mem ++> % ptr_inject @@ [mi] ++> - ==> - ==> k impl);

    cklr_valid_block:
      Monotonic
        (@Mem.valid_block)
        (|= match_mem ++> block_inject @@ [mi] ++> k iff);

    cklr_no_overlap w m1 m2:
      match_mem w m1 m2 ->
      Mem.meminj_no_overlap (mi w) m1;

    cklr_representable w m1 m2 b1 ofs1 b2 delta:
      match_mem w m1 m2 ->
      Mem.perm m1 b1 ofs1 Max Nonempty \/
      Mem.perm m1 b1 (ofs1 - 1) Max Nonempty ->
      mi w b1 = Some (b2, delta) ->
      0 <= ofs1 <= Ptrofs.max_unsigned ->
      delta >= 0 /\ 0 <= ofs1 + delta <= Ptrofs.max_unsigned;

    (* similar to Mem.aligned_area_inject for memory injections.
       Needed by Clight assign_of (By_copy) and memcpy. *)
    cklr_aligned_area_inject:
      forall w m m' b ofs al sz b' delta,
        match_mem w m m' ->
        (al = 1 \/ al = 2 \/ al = 4 \/ al = 8) ->
        sz > 0 ->
        (al | sz) ->
        Mem.range_perm m b ofs (ofs + sz) Cur Nonempty ->
        (al | ofs) ->
        mi w b = Some (b', delta) ->
        (al | ofs + delta);

    (* similar to Mem.disjoint_or_equal_inject for memory injections.
       Needed by Clight assign_of (By_copy) and memcpy. *)
    cklr_disjoint_or_equal_inject:
      forall w m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
        match_mem w m m' ->
        mi w b1 = Some (b1', delta1) ->
        mi w b2 = Some (b2', delta2) ->
        Mem.range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty ->
        Mem.range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty ->
        sz > 0 ->
        b1 <> b2 \/
        ofs1 = ofs2 \/
        ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
        b1' <> b2' \/
        (ofs1 + delta1 = ofs2 + delta2)%Z \/
        ofs1 + delta1 + sz <= ofs2 + delta2 \/
        ofs2 + delta2 + sz <= ofs1 + delta1;

    cklr_perm_inv w m1 m2 b1 ofs1 b2 ofs2 k p:
      match_mem w m1 m2 ->
      ptr_inject (mi w) (b1, ofs1) (b2, ofs2) ->
      Mem.perm m2 b2 ofs2 k p ->
      Mem.perm m1 b1 ofs1 k p \/ ~Mem.perm m1 b1 ofs1 Max Nonempty;

    cklr_sup_include w m1 m2 m1' m2':
      match_mem w m1 m2 ->
      (<> match_mem)%klr w m1' m2' ->
      Mem.sup_include (Mem.support m1) (Mem.support m1') <->
      Mem.sup_include (Mem.support m2) (Mem.support m2');

  }.
 

Record callconv' {li1 li2} :=
  mk_callconv' {
    ccworld' : Type;
    match_senv': ccworld' -> Genv.symtbl -> Genv.symtbl -> Prop;
    match_query': ccworld' -> query li1 -> query li2 -> Prop;
    match_reply': ccworld' -> reply li1 -> reply li2 -> Prop;

    match_senv_public_preserved':
      forall w se1 se2,
        match_senv' w se1 se2 ->
        forall id, Genv.public_symbol se2 id = Genv.public_symbol se1 id;
    (*match_senv_valid_for:
      forall w se1 se2 sk,
        match_senv w se1 se2 ->
        Genv.valid_for sk se1 ->
        Genv.valid_for sk se2; *)
  }.

Global Existing Instance cklr_kf.
Global Existing Instance acc_preorder.
Global Existing Instance mi_acc.
Global Instance mi_acc_params: Params (@mi) 2 := {}.
Global Existing Instance match_stbls_acc.
Global Instance match_stbls_params: Params (@match_stbls) 3 := {}.

Global Existing Instances cklr_alloc.
Local Existing Instances cklr_free.
Local Existing Instances cklr_load.
Local Existing Instances cklr_store.
Local Existing Instances cklr_loadbytes.
Global Existing Instances cklr_storebytes.
Local Existing Instances cklr_perm.
Global Existing Instances cklr_valid_block.


Arguments callconv': clear implicits.

Inductive cc_c_query' R (w: world R): relation c_query :=
  | cc_c_query_intro vf1 vf2 sg vargs1 vargs2 m1 m2:
      Val.inject (mi R w) vf1 vf2 ->
      Val.inject_list (mi R w) vargs1 vargs2 ->
      match_mem R w m1 m2 ->
      vf1 <> Vundef ->
      cc_c_query' R w (cq vf1 sg vargs1 m1) (cq vf2 sg vargs2 m2).

Inductive cc_c_reply' R (w: world R): relation c_reply :=
  | cc_c_reply_intro vres1 vres2 m1' m2':
      Val.inject (mi R w) vres1 vres2 ->
      match_mem R w m1' m2' ->
      cc_c_reply' R w (cr vres1 m1') (cr vres2 m2').

Program Definition cc_c' (R: cklr'): callconv' li_c li_c :=
  {|
    ccworld' := world R;
    match_senv' := match_stbls R;
    match_query' := cc_c_query' R;
    match_reply' := (<> cc_c_reply' R)%klr;
  |}.
Next Obligation.
  intros. eapply match_stbls_proj in H. eapply Genv.mge_public'; eauto.
Qed.

Require Import Inject.

Record inj_stbls' (w: inj_world) (se1 se2: Genv.symtbl): Prop :=
  {
    inj_stbls_match: Genv.match_stbls' (injw_meminj w) se1 se2;
    inj_stbls_next_l: Mem.sup_include (Genv.genv_sup se1) (injw_sup_l w);
    inj_stbls_next_r: Mem.sup_include (Genv.genv_sup se2) (injw_sup_r w);
  }.

Global Instance inj_stbls_subrel':
  Monotonic inj_stbls' (inj_incr ++> subrel).
Proof.
  intros w w' Hw se1 se2 Hse.
  destruct Hse; inv Hw. cbn in *.
  constructor; cbn; try extlia.
  eapply Genv.match_stbls_incr'; eauto.
  intros. edestruct H0; eauto.
  split; eauto. eauto. eauto.
Qed.

Program Definition inj' : cklr' :=
  {|
    world := inj_world;
    wacc := inj_incr;
    mi := injw_meminj;
    match_stbls := inj_stbls';
    match_mem := inj_mem;
  |}.

Next Obligation. (* mi_acc_separated *)
  eapply inj_acc_separated; eauto.
Qed.

Next Obligation.
  destruct 1. cbn. auto.
Qed.

Next Obligation.
  destruct H. inv H0; cbn in *. eauto.
Qed.

Next Obligation. (* Mem.alloc *)
  exact inj_cklr_alloc.
Qed.


Next Obligation. (* Mem.free *)
  intros [f nb1 nb2] m1 m2 Hm [[b1 lo1] hi1] [[b2 lo2] hi2] Hr.
  simpl. red.
  destruct (Mem.free m1 b1 lo1 hi1) as [m1'|] eqn:Hm1'; [|rauto].
  inv Hr. cbn in H0. inv H0. inv Hm.
  edestruct Mem.free_parallel_inject as (m2' & Hm2' & Hm'); eauto.
  replace (lo1 + delta + sz) with (lo1 + sz + delta) by extlia.
  rewrite Hm2'.
  repeat (econstructor; eauto); try congruence;
    erewrite <- Mem.support_free; eauto.
Qed.

Next Obligation. (* Mem.load *)
  intros [f nb1 nb2] chunk m1 m2 Hm _ _ [b1 ofs1 b2 delta Hptr].
  cbn in *. red. inv Hm.
  destruct (Mem.load chunk m1 b1 ofs1) as [v1|] eqn:Hv1; [|rauto].
  edestruct Mem.load_inject as (v2 & Hv2 & Hv); eauto.
  rewrite Hv2. repeat (econstructor; eauto).
Qed.

Next Obligation. (* Mem.store *)
  intros [f nb1 nb2] chunk m1 m2 Hm _ _ [b1 ofs1 b2 delta Hptr] v1 v2 Hv.
  red in Hv |- *. cbn in *. inv Hm.
  destruct (Mem.store chunk m1 b1 ofs1 v1) as [m1'|] eqn:Hm1'; [|rauto].
  edestruct Mem.store_mapped_inject as (m2' & Hm2' & Hm'); eauto.
  rewrite Hm2'.
  repeat (econstructor; eauto); try congruence;
    erewrite <- Mem.support_store; eauto.
Qed.

Next Obligation. (* Mem.loadbytes *)
  intros [f nb1 nb2] m1 m2 Hm _ _ [b1 ofs1 b2 delta Hptr] sz.
  red. cbn in *. inv Hm.
  destruct (Mem.loadbytes m1 b1 ofs1 sz) as [vs1|] eqn:Hvs1; [|rauto].
  edestruct Mem.loadbytes_inject as (vs2 & Hvs2 & Hvs); eauto.
  rewrite Hvs2. rauto.
Qed.

Next Obligation. (* Mem.storebytes *)
  intros [f nb1 nb2] m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr vs1 vs2 Hvs.
  red in Hvs |- *. cbn in *. inv Hm.
  destruct (Mem.storebytes m1 _ _ _) as [m1'|] eqn:Hm1'; [|constructor].
  assert (vs1 = nil \/ vs1 <> nil) as [Hvs1|Hvs1].
  { destruct vs1; constructor; congruence. }
  - subst. inv Hvs.
    edestruct (Mem.range_perm_storebytes m2 b2 ofs2 nil) as [m2' Hm2'].
    {
      intros ofs. simpl. extlia.
    }
    rewrite Hm2'.
    constructor.
    eexists; split; repeat rstep.
    erewrite <- (Mem.support_storebytes m1); eauto.
    erewrite <- (Mem.support_storebytes m2); eauto.
    constructor; eauto.
    eapply Mem.storebytes_empty_inject; eauto.
  - assert (ptr_inject f (b1, ofs1) (b2, ofs2)) as Hptr'.
    {
      destruct Hptr as [Hptr|Hptr]; eauto.
      inversion Hptr as [_ _ [xb1 xofs1 xb2 delta Hb]]; clear Hptr; subst.
      unfold ptrbits_unsigned.
      erewrite Mem.address_inject; eauto.
      apply Mem.storebytes_range_perm in Hm1'.
      eapply Hm1'.
      destruct vs1; try congruence.
      simpl. extlia.
    }
    inv Hptr'.
    edestruct Mem.storebytes_mapped_inject as (m2' & Hm2' & Hm'); eauto. rauto.
    rewrite Hm2'.
    repeat (econstructor; eauto); try congruence;
      erewrite <- Mem.support_storebytes; eauto.
Qed.

Next Obligation. (* Mem.perm *)
  intros [f nb1 nb2] m1 m2 Hm _ _ [b1 ofs1 b2 delta Hb] p k H.
  eapply Mem.perm_inject; eauto.
Qed.

Next Obligation. (* Mem.valid_block *)
  intros [f nb1 nb2] m1 m2 Hm b1 b2 [delta Hb].
  split; intro.
  - eapply Mem.valid_block_inject_2; eauto.
  - eapply Mem.valid_block_inject_1; eauto.
Qed.

Next Obligation. (* Mem.meminj_no_overlap *)
  destruct H as [f m1 m2 nb1].
  eapply Mem.mi_no_overlap; eauto.
Qed.

Next Obligation. (* representable *)
  destruct H as [f m1 m2 nb1].
  rewrite <- (Ptrofs.unsigned_repr ofs1) by extlia.
  eapply Mem.mi_representable; eauto.
  rewrite Ptrofs.unsigned_repr by extlia.
  assumption.
Qed.

Next Obligation.
  destruct H.
  eapply Mem.aligned_area_inject; eauto.
Qed.

Next Obligation. 
  destruct H.
  eapply Mem.disjoint_or_equal_inject; eauto.
Qed.

Next Obligation. (* perm_inv *)
  destruct H. inv H0.
  eapply Mem.perm_inject_inv; eauto.
Qed.

Next Obligation. (* nextblock incr *)
  destruct H0 as (w' & Hw' & Hm').
  destruct H. inv Hm'. inv Hw'.
  split; auto.
Qed.
