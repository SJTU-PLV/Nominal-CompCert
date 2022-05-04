Require Import Maps.
Require Import Valuesrel.
Require Import Globalenvs.
Require Import CKLR.
Require Import Builtinsrel.
Require Export Events.


(** * External functions *)

Global Instance eventval_match_rel f:
  Monotonic
    (@eventval_match)
    (symbols_inject f ++> - ==> - ==> set_le (Val.inject f)).
Proof.
  intros ge1 ge2 (Hps & Hifs & Hpfs & Hbv) ev ty v Hv.
  destruct Hv; try (eexists; split; constructor).
  edestruct Hpfs as (b2 & Hb & Hid2); eauto.
  exists (Vptr b2 ofs); split; econstructor; eauto.
  rewrite Ptrofs.add_zero. reflexivity.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @eventval_match : typeclass_instances.

Global Instance volatile_load_rel R w:
  Monotonic
    (@volatile_load)
    (symbols_inject (mi R w) ++> - ==> match_mem R w ++>
     % ptrbits_inject (mi R w) ++> - ==> set_le (Val.inject (mi R w))).
Proof.
  intros ge1 ge2 Hge chunk m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr t v1 Hv1.
  simpl in *.
  pose proof Hge as (_ & Hifs & _ & Hbv).
  destruct Hv1.
  - transport H1.
    exists (Val.load_result chunk x). split.
    + inv Hptr.
      edestruct (Hifs id) as [Hdelta Hid2]; eauto. subst.
      rewrite Ptrofs.add_zero.
      erewrite <- Hbv in H by eauto.
      constructor; eauto.
    + rauto.
  - transport H0.
    exists x. split.
    + inv Hptr.
      constructor; eauto.
    + rauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @volatile_load : typeclass_instances.

Lemma val_load_result_idemp chunk v:
  Val.load_result chunk (Val.load_result chunk v) = Val.load_result chunk v.
Proof.
  destruct chunk, v; simpl; try reflexivity.
  - rewrite Int.sign_ext_widen; eauto. extlia.
  - rewrite Int.zero_ext_widen; eauto. extlia.
  - rewrite Int.sign_ext_widen; eauto. extlia.
  - rewrite Int.zero_ext_widen; eauto. extlia.
Qed.

Global Instance volatile_store_rel R:
  Monotonic
    (@volatile_store)
    (|= symbols_inject @@ [mi R] ++> - ==> match_mem R ++>
     % ptrbits_inject @@ [mi R] ++> Val.inject @@ [mi R] ++> - ==>
     k1 set_le (<> match_mem R)).
Proof.
  intros w ge1 ge2 Hge chunk m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr v1 v2 Hv t m1' H.
  simpl in *.
  pose proof Hge as (_ & Hifs & _ & Hbv).
  destruct H.
  - exists m2. split.
    + inv Hptr.
      edestruct (Hifs id) as [Hdelta Hid2]; eauto. subst.
      rewrite Ptrofs.add_zero.
      erewrite <- Hbv in H by eauto.
      constructor; eauto.
      eapply eventval_match_inject; eauto.
      rauto.
    + rauto.
  - transport H0.
    exists x. split.
    + inv Hptr.
      erewrite <- Hbv in H by eauto.
      constructor; eauto.
    + rauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @volatile_store : typeclass_instances.

Notation extcall_sem_rel R :=
  (|= symbols_inject @@ [mi R] ++>
   Val.inject_list @@ [mi R] ++>
   match_mem R ++>
   - ==>
   % k1 set_le (<> Val.inject @@ [mi R] * match_mem R))%rel.

Lemma val_inject_vptr_inv f b1 ofs1 y:
  Val.inject f (Vptr b1 ofs1) y ->
  exists b2 ofs2,
    y = Vptr b2 ofs2 /\
    ptrbits_inject f (b1, ofs1) (b2, ofs2).
Proof.
  inversion 1; subst.
  eexists _, _.
  split; eauto.
Qed.

Global Instance volatile_load_sem_rel R:
  Monotonic (@volatile_load_sem) (- ==> extcall_sem_rel R).
Proof.
  intros chunk w ge1 ge2 Hge vargs1 vargs2 Hvargs m1 m2 Hm t [vres1 m1'] H.
  simpl in *.
  destruct H.
  inv Hvargs. inv H4.
  apply val_inject_vptr_inv in H2 as (b2 & o2 & Hy & Hptr). subst.
  transport H.
  eexists (_, _). simpl. split.
  - constructor; eauto.
  - rauto.
Qed.

Global Instance volatile_store_sem_rel R:
  Monotonic (@volatile_store_sem) (- ==> extcall_sem_rel R).
Proof.
  intros chunk w ge1 ge2 Hge vargs1 vargs2 Hvargs m1 m2 Hm t [vres1 m1'] H.
  simpl in *.
  destruct H.
  inv Hvargs. inv H4. inv H6.
  apply val_inject_vptr_inv in H2 as (b2 & o2 & Hy & Hptr). subst.
  transport H.
  eexists (_, _). simpl. split.
  - constructor; eauto.
  - rauto.
Qed.

Lemma val_inject_vptrofs_inv f n y:
  Val.inject f (Vptrofs n) y ->
  y = Vptrofs n.
Proof.
  inversion 1; subst.
  reflexivity.
Qed.

Global Instance extcall_malloc_sem_rel R:
  Monotonic (@extcall_malloc_sem) (extcall_sem_rel R).
Proof.
  intros w ge1 ge2 Hge vargs1 vargs2 Hvargs m1 m2 Hm t [vres1 m1'] H.
  simpl in *.
  destruct H.
  inv Hvargs. inv H5. apply val_inject_vptrofs_inv in H3. subst.
  edestruct cklr_alloc as (w' & Hw' & HH); eauto.
  transport H. clear HH.
  assert (ptr_inject (mi R w') (b, (-size_chunk Mptr)) (x0, (-size_chunk Mptr)))
    by rauto.
  transport H0.
  eexists (_, _). simpl. split.
  - econstructor; eauto.
  - exists w''; split; rauto.
Qed.

Global Instance extcall_free_sem_rel R:
  Monotonic (@extcall_free_sem) (extcall_sem_rel R).
Proof.
  intros w ge1 ge2 Hge vargs1 vargs2 Hvargs m1 m2 Hm t [vres1 m1'] H.
  simpl in *.
  destruct H.
+ inv Hvargs. inv H6.
  apply val_inject_vptr_inv in H4 as (b2 & lo2 & ? & Hptr). subst.
  assert (ptr_inject (mi R w) (b,  Ptrofs.unsigned lo  - size_chunk Mptr)
                              (b2, Ptrofs.unsigned lo2 - size_chunk Mptr)).
  {
    rewrite <- ?Z.add_opp_r.
    apply ptr_inject_shift.
    eapply ptrbits_ptr_inject; eauto.
    eapply Mem.free_range_perm in H1.
    eapply H1. pose proof (size_chunk_pos Mptr). extlia.
  }
  transport H. apply val_inject_vptrofs_inv in H4. subst.
  assert
    (ptrrange_inject (mi R w)
      (b,  Ptrofs.unsigned lo  - size_chunk Mptr,
           Ptrofs.unsigned lo  + Ptrofs.unsigned sz)
      (b2, Ptrofs.unsigned lo2 - size_chunk Mptr,
           Ptrofs.unsigned lo2 + Ptrofs.unsigned sz)).
  {
    eapply ptr_ptrrange_inject. split.
    - rauto.
    - extlia.
  }
  transport H1.
  eexists (_, _). simpl. split.
  - econstructor; eauto.
  - rauto.
+ inv Hvargs. inv H1. inv H3.
  eexists (_, _). simpl. split.
  - econstructor; eauto.
  - rauto.
Qed.

Global Instance extcall_memcpy_sem_rel R:
  Monotonic (@extcall_memcpy_sem) (- ==> - ==> extcall_sem_rel R).
Proof.
  intros sz al w ge1 ge2 Hge vargs1 vargs2 Hvargs m1 m2 Hm t [vres1 m1'] H.
  simpl in *.
  destruct H.
  inv Hvargs. apply val_inject_vptr_inv in H9 as (bdst' & odst' & ? & ?); subst.
  inv H11. apply val_inject_vptr_inv in H10 as (bsrc' & osrc' & ? & ?); subst.
  inv H13.
  generalize H5 H6.
  transport H5.
  transport H6.
  intros Hlb1 Hsb1.
  eexists (_, _). simpl. split.
  - econstructor; eauto.
    + intro. rewrite Hw' in H9. inv H9.
      eapply Mem.loadbytes_range_perm in Hlb1.
      erewrite cklr_address_inject; eauto.
      eapply cklr_aligned_area_inject; eauto.
      * intros ofs Hofs.
        eapply Mem.perm_storebytes_1; eauto.
        eapply Mem.perm_implies.
        eapply Hlb1; eauto.
        constructor.
      * eapply Mem.perm_storebytes_1; eauto.
        eapply Hlb1. extlia.
    + intro. rewrite Hw' in H8. inv H8.
      erewrite cklr_address_inject; eauto.
      eapply cklr_aligned_area_inject; eauto.
      * pose proof Hsb1 as Hrp1.
        eapply Mem.storebytes_range_perm in Hrp1.
        erewrite Mem.loadbytes_length in Hrp1 by eauto.
        rewrite Z2Nat.id in Hrp1 by extlia.
        intros ofs Hofs.
        eapply Mem.perm_storebytes_1; eauto.
        eapply Mem.perm_implies; eauto.
        constructor.
      * eapply Mem.perm_storebytes_1; eauto.
        eapply Mem.storebytes_range_perm; eauto.
        erewrite Mem.loadbytes_length; eauto.
        rewrite Z2Nat.id by extlia.
        extlia.
    + assert (sz > 0 \/ sz = 0) as [Hsz | Hsz] by extlia.
      * rewrite Hw' in H8. inv H8.
        rewrite Hw' in H9. inv H9.
        erewrite !cklr_address_inject; eauto.
        eapply cklr_disjoint_or_equal_inject; eauto.
        -- intros ofs Hofs.
           eapply Mem.loadbytes_range_perm in Hlb1.
           eapply Mem.perm_storebytes_1; eauto.
           eapply Mem.perm_cur_max; eauto.
           eapply Mem.perm_implies; eauto.
           constructor.
        -- intros ofs Hofs.
           eapply Mem.perm_storebytes_1; eauto.
           eapply Mem.perm_cur_max; eauto.
           eapply Mem.storebytes_range_perm in Hsb1.
           eapply Mem.perm_implies; eauto.
           eapply Hsb1; eauto.
           erewrite Mem.loadbytes_length; eauto.
           rewrite Z2Nat.id by extlia; eauto.
           constructor.
        -- eapply Mem.perm_storebytes_1; eauto.
           eapply Mem.storebytes_range_perm; eauto.
           erewrite Mem.loadbytes_length; eauto.
           rewrite Z2Nat.id by extlia; eauto.
           extlia.
        -- eapply Mem.perm_storebytes_1; eauto.
           eapply Mem.loadbytes_range_perm; eauto.
           extlia.
      * subst. right. extlia.
  - rauto.
Qed.

Global Instance extcall_annot_sem_rel R:
  Monotonic (@extcall_annot_sem) (- ==> - ==> extcall_sem_rel R).
Proof.
  intros text targs w ge1 ge2 Hge vargs1 vargs2 Hvargs m1 m2 Hm t [vres1 m1'] H.
  simpl in *.
  destruct H.
  eexists (_, _). simpl. split.
  - econstructor; eauto.
    eapply eventval_list_match_inject; eauto.
  - rauto.
Qed.

Global Instance extcall_annot_val_sem_rel R:
  Monotonic (@extcall_annot_val_sem) (- ==> - ==> extcall_sem_rel R).
Proof.
  intros text targs w ge1 ge2 Hge vargs1 vargs2 Hvargs m1 m2 Hm t [vres1 m1'] H.
  simpl in *.
  destruct H.
  inv Hvargs. inv H4.
  eexists (_, _). simpl. split.
  - econstructor; eauto.
    eapply eventval_match_inject; eauto.
  - rauto.
Qed.

Global Instance extcall_debug_sem_rel R:
  Monotonic (@extcall_debug_sem) (extcall_sem_rel R).
Proof.
  intros w ge1 ge2 Hge vargs1 vargs2 Hvargs m1 m2 Hm t [vres1 m1'] H.
  simpl in *.
  destruct H.
  eexists (_, _). simpl. split.
  - econstructor; eauto.
  - rauto.
Qed.

Require Import OptionRel.

Global Instance known_builtin_sem_rel R:
  Monotonic (@known_builtin_sem) (- ==> extcall_sem_rel R).
Proof.
  intros b w ge1 ge2 Hge vargs1 vargs2 Hvargs m1 m2 Hm t [vres1 m1'] H.
  destruct H as [vargs1 vres1 m1 H].
  pose proof (builtin_function_sem_rel R b) as Hbs. red in Hbs.
  transport H.
  eexists (_, _). simpl. split.
  - econstructor; eauto.
  - rauto.
Qed.

Axiom external_functions_sem_rel:
  forall R, Monotonic (@external_functions_sem) (- ==> - ==> extcall_sem_rel R).

Axiom inline_assembly_sem_rel:
  forall R, Monotonic (@inline_assembly_sem) (- ==> - ==> extcall_sem_rel R).

Global Existing Instance external_functions_sem_rel.
Global Existing Instance inline_assembly_sem_rel.

Global Instance builtin_or_external_sem_rel R:
  Monotonic (@builtin_or_external_sem) (- ==> - ==> extcall_sem_rel R).
Proof.
  unfold builtin_or_external_sem.
  intros name sg.
  destruct Builtins.lookup_builtin_function; rauto.
Qed.

Global Instance external_call_rel R:
  Monotonic
    (@external_call)
    (- ==> |= Genv.match_stbls @@ [mi R] ++> Val.inject_list @@ [mi R] ++>
     match_mem R ++> - ==> % k1 set_le (<> Val.inject @@ [mi R] * match_mem R)).
Proof.
  intros ef w se1 se2 Hse.
  assert (symbols_inject (mi R w) se1 se2).
  {
    repeat split; intros.
    + apply (Genv.mge_public Hse); auto.
    + edestruct @Genv.find_symbol_match as (? & ? & ?); eauto. congruence.
    + edestruct @Genv.find_symbol_match as (? & ? & ?); eauto. congruence.
    + edestruct @Genv.find_symbol_match as (? & ? & ?); eauto.
    + simpl; unfold Genv.block_is_volatile, Genv.find_var_info, Genv.find_def.
      edestruct (Genv.mge_info Hse _ H); subst; reflexivity.
  }
  destruct ef; simpl; try rauto.
  - repeat intro. destruct a0. contradiction.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  rel_curry_set_le_transport @external_call : typeclass_instances.


(** * [eval_builtin_args] *)

Global Instance senv_symbols_address_inject f:
  Monotonic
    (@Genv.symbol_address)
    (Genv.match_stbls f ++> - ==> - ==> Val.inject f).
Proof.
  intros se1 se2 Hse id ofs.
  unfold Genv.symbol_address.
  destruct (Genv.find_symbol se1 id) as [b1|] eqn:Hb1; auto.
  edestruct @Genv.find_symbol_match as (b2 & Hb & Hb2); eauto.
  rewrite Hb2. econstructor; eauto. rewrite Ptrofs.add_zero. auto.
Qed.

Global Instance eval_builtin_arg_rel R w:
  Monotonic
    (@eval_builtin_arg)
    (forallr -, Genv.match_stbls (mi R w) ++>
     (- ==> Val.inject (mi R w)) ++>
     Val.inject (mi R w) ++> match_mem R w ++> - ==> set_le (Val.inject (mi R w))).
Proof.
  intros A ge1 ge2 Hge f1 f2 Hf v1 v2 Hv m1 m2 Hm arg r Hr.
  revert v2 Hv.
  induction Hr; intros ? ?;
  try (transport_hyps; eexists; split; [constructor; eauto | rauto]).
  - edestruct IHHr1 as (vhi' & Hvhi' & Hvhi); eauto.
    edestruct IHHr2 as (vlo' & Hvlo' & Hvlo); eauto.
    eexists. split; [ constructor; eauto | rauto ].
  - edestruct IHHr1 as (va1 & Hva1 & Hva1'); eauto.
    edestruct IHHr2 as (va2 & Hva2 & Hva2'); eauto.
    eexists. split; [ constructor; eauto | rauto ].
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @eval_builtin_arg : typeclass_instances.

Global Instance eval_builtin_args_rel R w:
  Monotonic
    (@eval_builtin_args)
    (forallr -, Genv.match_stbls (mi R w) ++>
     (- ==> Val.inject (mi R w)) ++>
     Val.inject (mi R w) ++> match_mem R w ++> - ==>
     set_le (Val.inject_list (mi R w))).
Proof.
  unfold eval_builtin_args.
  repeat rstep.
  intros vl Hvl.
  induction Hvl.
  - eexists; split; constructor; eauto.
  - destruct IHHvl as (? & ? & ?).
    transport H3.
    eexists; split; constructor; eauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @eval_builtin_args : typeclass_instances.
