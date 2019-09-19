Require Import Coqlib.
Require Import Errors.
Require Import Mapsrel.
Require Import Integers.
Require Import Floats.
Require Import Valuesrel.
Require Import AST.
Require Import CKLR.
Require Import Eventsrel.
Require Import Globalenvsrel.
Require Import Smallstep.
Require Import Ctypes.
Require Import Coprel.

Require Import LogicalRelations.
Require Import OptionRel.
Require Import KLR.
Require Export Clight.


Definition genv_valid R w ge :=
  Globalenvsrel.genv_valid R w (genv_genv ge).

Lemma genv_genv_valid R w ge:
  genv_valid R w ge ->
  Globalenvsrel.genv_valid R w (genv_genv ge).
Proof.
  eauto.
Qed.

Hint Resolve genv_genv_valid.

Global Instance genv_genv_valid_rel R w:
  Monotonic
    (@genv_genv)
    (psat (genv_valid R w) ++> psat (Globalenvsrel.genv_valid R w)).
Proof.
  intros ge _ [Hge].
  constructor; assumption.
Qed.

(** NB: we have to use [option_rel] here not [option_le], because
  otherwise it is difficult to state the monotonicity property of
  [blocks_of_env] (we would have to introduce some kind of "subset"
  list relator) *)
Definition env_match R w :=
  PTreeRel.r (option_rel (block_inject_sameofs (mi R w) * @eq type)).

Global Instance env_match_acc:
  Monotonic (@env_match) (forallr - @ R, acc tt ++> subrel).
Proof.
  unfold env_match. rauto.
Qed.

Global Instance empty_env_match R w:
  Monotonic (@empty_env) (env_match R w).
Proof.
  unfold env_match, empty_env. rauto.
Qed.

Definition temp_env_match R w: rel temp_env temp_env :=
  PTreeRel.r (option_le (Val.inject (mi R w))).

Global Instance temp_env_match_acc:
  Monotonic (@temp_env_match) (forallr - @ R, acc tt ++> subrel).
Proof.
  unfold temp_env_match. rauto.
Qed.

Global Instance deref_loc_match R w:
  Monotonic
    (@deref_loc)
    (- ==> match_mem R w ++> % ptrbits_inject (mi R w) ++>
     set_le (Val.inject (mi R w))).
Proof.
  repeat rstep.
  intros a H1.
  assert (Val.inject (mi R w) (Vptr (fst x1) (snd x1)) (Vptr (fst y0) (snd y0))) as VAL.
  {
    rstep.
    destruct x1; destruct y0; assumption.
  }
  inversion H0; subst.
  repeat red.
  simpl in * |- * .
  inversion H1; subst; eauto using @deref_loc_reference, @deref_loc_copy.
  generalize (cklr_loadv R w chunk _ _ H _ _ VAL).
  rewrite H4.
  inversion 1; subst.
  symmetry in H7.
  eauto using @deref_loc_value.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @deref_loc : typeclass_instances.

(** [assign_loc] is somewhat involved. *)

Lemma assign_loc_match_alignof_blockcopy R w m1 m2 b1 ofs1 b2 ofs2 env ty:
  match_mem R w m1 m2 ->
  ptrbits_inject (mi R w) (b1, ofs1) (b2, ofs2) ->
  sizeof env ty > 0 ->
  Mem.range_perm m1 b1 (Ptrofs.unsigned ofs1) (Ptrofs.unsigned ofs1 + sizeof env ty) Cur Nonempty ->
  (alignof_blockcopy env ty | Ptrofs.unsigned ofs1) ->
  (alignof_blockcopy env ty | Ptrofs.unsigned ofs2).
Proof.
  intros Hm Hptr Hsz Hperm H.
  inv Hptr.
  erewrite (cklr_address_inject R w); eauto.
  eapply (cklr_aligned_area_inject R w); eauto.
  + eapply alignof_blockcopy_1248.
  + eapply sizeof_alignof_blockcopy_compat.
  + eapply Hperm.
    omega.
Qed.

Global Instance assign_loc_match R:
  Monotonic
    (@assign_loc)
    (|= - ==> - ==> match_mem R ++>
     % ptrbits_inject @@ [mi R] ++>
     Val.inject @@ [mi R] ++>
     k1 set_le (<> match_mem R)).
Proof.
  intros w ce ty m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr v1 v2 Hv m1' Hm1'.
  destruct Hm1' as [v1 chunk m1' | b1' ofs1' bytes1 m1'].
  - transport_hyps.
    eexists; split; [ | rauto].
    eapply assign_loc_value; eauto.
  - assert
      (sizeof ce ty > 0 ->
       Mem.range_perm m1 b1
         (Ptrofs.unsigned ofs1)
         (Ptrofs.unsigned ofs1 + sizeof ce ty)
         Cur Nonempty).
    {
      intro.
      eapply Mem.range_perm_implies.
      + replace (sizeof _ _) with (Z.of_nat (length bytes1)).
        * eapply Mem.storebytes_range_perm; eauto.
        * erewrite (Mem.loadbytes_length m1) by eauto.
          apply nat_of_Z_eq.
          omega.
      + constructor.
    }
    assert
      (sizeof ce ty > 0 ->
       Mem.range_perm m1 b1'
         (Ptrofs.unsigned ofs1')
         (Ptrofs.unsigned ofs1' + sizeof ce ty)
         Cur Nonempty).
    {
      intro.
      eapply Mem.range_perm_implies.
      + eapply Mem.loadbytes_range_perm; eauto.
      + constructor.
    }
    simpl.
    rinversion Hv; clear Hv; inv Hvl.
    transport_hyps.
    eexists; split; [eapply assign_loc_copy | ]; simpl.
    + assumption.
    + eauto using assign_loc_match_alignof_blockcopy.
    + eauto using assign_loc_match_alignof_blockcopy.
    + assert (sizeof ce ty = 0 \/ sizeof ce ty <> 0) as [Hsz | Hsz] by xomega.
      {
        rewrite Hsz.
        right.
        omega.
      }
      assert (Hsz' : sizeof ce ty > 0).
      {
        pose proof (sizeof_pos ce ty).
        omega.
      }
      inv Hptr.
      inv H7.
      erewrite !(cklr_address_inject R w); eauto.
      eapply (cklr_disjoint_or_equal_inject R w); eauto.
      * intros ofs Hofs.
        eapply Mem.perm_cur_max.
        eapply H6; eauto.
      * intros ofs Hofs.
        eapply Mem.perm_cur_max.
        eapply H5; eauto.
      * eapply H5; eauto.
        omega.
      * eapply H6; eauto.
        omega.
    + eassumption.
    + eassumption.
    + rauto.
Qed.

Hint Extern 1 (Related _ _ _) =>
  eapply assign_loc_match : typeclass_instances.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @assign_loc : typeclass_instances.

Global Instance alloc_variables_match R:
  Monotonic
    (@alloc_variables)
    (|= - ==> env_match R ++> match_mem R ++> - ==>
     % k1 set_le (<> (env_match R * match_mem R))).
Proof.
  intros w ge e1 e2 Henv m1 m2 Hm vars [e1' m1'] H.
  revert H w e2 m2 Henv Hm.
  simpl.
  induction 1 as [e1 m1 | e1 m1 id ty vars m1' b1 m1'' e1'' Hm1' Hm1'' IH].
  - intros.
    exists (e2, m2).
    split.
    + constructor.
    + rauto.
  - intros.
    edestruct (cklr_alloc R w m1 m2 Hm 0 (sizeof ge ty)) as (p' & Hp' & Hm' & Hb); eauto.
    destruct (Mem.alloc m2 0 (sizeof ge ty)) as [m2' b2] eqn:Hm2'.
    rewrite Hm1' in *. cbn [fst snd] in *.
    specialize (IH p' (PTree.set id (b2, ty) e2) m2').
    edestruct IH as ((e2'' & m2'') & Hvars & p'' & He'' & Hm''); eauto.
    {
      (** We only have [ptree_set_le], we would need support for
        multiple instances to declare [ptree_set_rel] as well. *)
      unfold env_match in *.
      intro j.
      destruct (ident_eq j id); subst.
      - rewrite !PTree.gss. rauto.
      - rewrite !PTree.gso by assumption. rauto.
    }
    eexists (e2'', m2'').
    split.
    + simpl.
      econstructor; eauto.
    + rauto.
Qed.

Global Instance bind_parameters_match R:
  Monotonic
    (@bind_parameters)
    (|= - ==> env_match R ++> match_mem R ++> - ==>
     k1 list_rel (Val.inject @@ [mi R]) ++>
     k1 set_le (<> match_mem R)).
Proof.
  intros w ge e1 e2 He m1 m2 Hm vars vl1 vl2 Hvl m1' H.
  revert H w He vl2 m2 Hvl Hm.
  induction 1 as [m1 | m1 id ty params v1 vl1 b1 m1' m1'' Hb1 Hm1' Hm1'' IH].
  - intros.
    exists m2.
    split; try rauto.
    inversion Hvl; subst.
    constructor.
  - intros.
    generalize He. intro He_.
    specialize (He id).
    pose proof (fun m => bind_parameters_cons ge e2 m id) as Hbp_cons.
    destruct He as [[xb1 xty] [b2 yty] [Hb Hty] | ]; try discriminate.
    simpl in *.
    inversion Hb1; clear Hb1.
    repeat subst.
    inversion Hvl as [ | xv1 v2 Hv xvl1 vl2' Hvl']; subst.
    assert (PTR: ptrbits_inject (mi R w) (b1, Ptrofs.zero) (b2, Ptrofs.zero))
      by rauto.
    edestruct (assign_loc_match R) as (m2' & Hm2' & w' & Hw' & Hm'); eauto.
    unfold klr_pullw in *.
    transport_hyps.
    edestruct (IH w') as (m2'' & Hm2'' & Hm''); eauto.
    + rauto.
    + rauto.
    + destruct Hm'' as (w'' & Hw'' & Hm'').
      eexists.
      split; eauto.
      rauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @bind_parameters : typeclass_instances.

Global Instance create_undef_temps_match R w:
  Monotonic
    (@create_undef_temps)
    (- ==> temp_env_match R w).
Proof.
  unfold temp_env_match.
  intros temps.
  induction temps as [ | [id t] temps IHtemps]; simpl; try rauto.
Qed.

Global Instance bind_parameter_temps_match R w:
  Monotonic
    (@bind_parameter_temps)
    (- ==> list_rel (Val.inject (mi R w)) ++> temp_env_match R w ++>
     option_rel (temp_env_match R w)).
Proof.
  intros formals args1 args2 Hargs.
  revert formals.
  induction Hargs as [ | v1 v2 Hv args1 args2 Hargs IH].
  - intros [|]; simpl; intros; rauto.
  - intros [| [id t] formals]; simpl; repeat rstep.
    eapply IH.
    rauto.
Qed.

Global Instance block_of_binding_match R w:
  Monotonic
    (@block_of_binding)
    (- ==> eq * (block_inject_sameofs (mi R w) * eq) ++>
     ptrrange_inject (mi R w)).
Proof.
  intros ge (id1 & b1 & ty1) (id2 & b2 & ty2) (Hid & Hb & Hty).
  simpl in *.
  eapply block_sameofs_ptrrange_inject; intuition auto.
  congruence.
Qed.

Global Instance blocks_of_env_match R w:
  Monotonic
    (@blocks_of_env)
    (- ==> env_match R w ++> list_rel (ptrrange_inject (mi R w))).
Proof.
  unfold blocks_of_env. rauto.
Qed.

Global Instance set_opttemp_match R w:
  Monotonic
    (@set_opttemp)
    (- ==> Val.inject (mi R w) ++> temp_env_match R w ++> temp_env_match R w).
Proof.
  unfold set_opttemp. rauto.
Qed.



Global Instance subrel_refl_rstep {A B} (R : rel A B) :
  RStep True (subrel R R) | 25.
Proof.
  firstorder.
Qed.

(** [select_switch_default], [select_switch_case], [select_switch]
  and [seq_of_label_statement] are entierly about syntax. *)
Lemma eval_expr_lvalue_match R w (ge: genv):
  genv_valid R w ge ->
  forall e1 e2, env_match R w e1 e2 ->
  forall le1 le2, temp_env_match R w le1 le2 ->
  forall m1 m2, match_mem R w m1 m2 ->
  (forall expr v1,
     eval_expr ge e1 le1 m1 expr v1 ->
     exists v2,
       eval_expr ge e2 le2 m2 expr v2 /\
       Val.inject (mi R w) v1 v2) /\
  (forall expr b1 ofs,
     eval_lvalue ge e1 le1 m1 expr b1 ofs ->
     exists b2 ofs2,
       eval_lvalue ge e2 le2 m2 expr b2 ofs2 /\
       ptrbits_inject (mi R w) (b1, ofs) (b2, ofs2)).
Proof.
  intros Hge e1 e2 He le1 le2 Hle m1 m2 Hm.
  apply eval_expr_lvalue_ind;
  try solve
    [ intros;
      split_hyps;
      transport_hyps;
      repeat (repeat rstep; econstructor) ].

  - intros id b1 ty Hb1.
    red in He.
    transport_hyps.
    destruct x as [b2 ty'], H0 as (Hb & Hty).
    simpl in *; subst.
    repeat (repeat rstep; econstructor).

  - intros id b1 ty He1 Hb1.
    red in He. (* XXX *)
    transport_hyps.
    eexists; eexists; split.
    + eapply eval_Evar_global; eauto.
    + apply block_sameofs_ptrbits_inject; eauto using genv_valid_find_symbol.

  - intros expr ty b1 ofs H1 IH.
    destruct IH as (ptr2 & H2 & Hptr).
    inversion Hptr; clear Hptr; subst.
    eexists; eexists; split; eauto.
    constructor; eauto.

  - intros expr fid ty b1 ofs1 sid sflist satt delta H1 IH Hs Hf Hdelta.
    destruct IH as (ptr2 & H2 & Hptr).
    rinversion Hptr; inv Hptrl.
    eauto 6 using @eval_Efield_struct, ptrbits_inject_shift.

  - intros expr fid ty b1 ofs1 uid uflist uatt H1 IH Hu.
    destruct IH as (ptr2 & H2 & Hptr).
    rinversion Hptr; inv Hptrl.
    eauto using @eval_Efield_union.
Qed.

Global Instance eval_expr_match R w:
  Monotonic
    (@eval_expr)
    (psat (genv_valid R w) ==>
     env_match R w ++> temp_env_match R w ++>
     match_mem R w ++> - ==>
     set_le (Val.inject (mi R w))).
Proof.
  intros ge _ [Hge] e1 e2 He le1 le2 Hle m1 m2 Hm expr v1 Hv1.
  edestruct eval_expr_lvalue_match; eauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @eval_expr : typeclass_instances.

Global Instance eval_lvalue_match R w:
  Monotonic
    (@eval_lvalue)
    (psat (genv_valid R w) ==> env_match R w ++> temp_env_match R w ++>
     match_mem R w ++> - ==>
     % set_le (ptrbits_inject (mi R w))).
Proof.
  intros ge _ [Hge] e1 e2 He le1 le2 Hle m1 m2 Hm expr [b1 ofs] Hp1.
  simpl in *.
  edestruct eval_expr_lvalue_match as [_ H]; eauto.
  edestruct H as (b2 & ofs2 & H'); eauto.
  exists (b2, ofs2).
  split_hyps.
  split; eauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  rel_curry_set_le_transport @eval_lvalue : typeclass_instances.

Global Instance eval_exprlist_match R w:
  Monotonic
    (@eval_exprlist)
    (psat (genv_valid R w) ==> env_match R w ++> temp_env_match R w ++>
     match_mem R w ++> - ==> - ==>
     set_le (list_rel (Val.inject (mi R w)))).
Proof.
  intros ge1 ge2 Hge e1 e2 He le1 le2 Hle m1 m2 Hm exprlist tys vs1 Hvs1.
  induction Hvs1 as [|expr exprs ty tys v1 v1' v1s Hv1 Hv1' Hv1s IHv1s]; simpl.
  - exists nil.
    split; constructor.
  - split_hyps.
    transport_hyps.
    eexists.
    split; econstructor; eauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @eval_exprlist : typeclass_instances.

Inductive cont_match R (w: world R): rel cont cont :=
  | Kstop_match:
      Monotonic (@Kstop) (cont_match R w)
  | Kseq_match:
      Monotonic (@Kseq) (- ==> cont_match R w ++> cont_match R w)
  | Kloop1_match:
      Monotonic (@Kloop1) (- ==> - ==> cont_match R w ++> cont_match R w)
  | Kloop2_match:
      Monotonic (@Kloop2) (- ==> - ==> cont_match R w ++> cont_match R w)
  | Kswitch_match:
      Monotonic (@Kswitch) (cont_match R w ++> cont_match R w)
  | Kcall_match:
      Monotonic
        (@Kcall)
        (- ==> - ==>
         env_match R w ++>
         temp_env_match R w ++>
         cont_match R w ++>
         cont_match R w).

Global Existing Instance Kstop_match.
Global Existing Instance Kseq_match.
Global Existing Instance Kloop1_match.
Global Existing Instance Kloop2_match.
Global Existing Instance Kswitch_match.
Global Existing Instance Kcall_match.

Global Instance cont_match_le:
  Monotonic (@cont_match) (forallr - @ R, acc tt ++> subrel).
Proof.
  repeat red.
  intros R x y H x0 y0 H0.
  revert y H.
  induction H0; constructor; auto; rauto.
Qed.

Global Instance call_cont_match R w:
  Monotonic
    (@call_cont)
    (cont_match R w ++> (cont_match R w /\ lsat is_call_cont)).
Proof.
  intros k1 k2 Hk.
  induction Hk; simpl; try rauto.
  (* XXX prob is now we don't just try I *)
  reexists. rstep. apply I. red. simpl.
  destruct IHHk. split. constructor; eauto. constructor.
Qed.

Global Instance is_call_cont_match_strong R w:
  Monotonic (@is_call_cont) (cont_match R w ++> iff).
Proof.
  intros k1 k2 Hk.
  destruct Hk; rauto.
Qed.

Hint Extern 10 (Transport _ _ _ (is_call_cont _) _) =>
  eapply impl_transport : typeclass_instances.

Inductive state_match R w: rel state state :=
  | State_rel:
      Monotonic
        (@State)
        (- ==> - ==>
         cont_match R w ++>
         env_match R w ++>
         temp_env_match R w ++>
         match_mem R w ++>
         state_match R w)
  | Callstate_rel:
      Monotonic
        (@Callstate)
        (- ==>
         list_rel (Val.inject (mi R w)) ++>
         cont_match R w ++>
         match_mem R w ++>
         state_match R w)
  | Returnstate_rel:
      Monotonic
        (@Returnstate)
        (Val.inject (mi R w) ++>
         cont_match R w ++>
         match_mem R w ++>
         state_match R w).

Global Existing Instance State_rel.
Global Existing Instance Callstate_rel.
Global Existing Instance Returnstate_rel.

Scheme statement_ind_mutual := Induction for statement Sort Prop
  with ls_ind_mutual := Induction for labeled_statements Sort Prop.

Global Instance find_label_match R w:
  Monotonic
    (@find_label)
    (- ==> - ==> cont_match R w ++> option_rel (eq * cont_match R w)).
Proof.
  intros lbl s.
  pattern s.
  pose proof Some_rel.
  eapply statement_ind_mutual with
    (P0 := fun ls =>
               (cont_match R w ++> option_rel (eq * cont_match R w))%rel
               (find_label_ls lbl ls)
               (find_label_ls lbl ls));
  simpl; intros;
  repeat rstep.
Qed.

Global Instance function_entry2_match R:
  Monotonic
    (@function_entry2)
    (|= - ==> - ==> k1 list_rel (Val.inject @@ [mi R]) ++> match_mem R ++>
     %% k1 set_le (<> env_match R * temp_env_match R * match_mem R)).
Proof.
  intros w ge f vargs1 vargs2 Hvargs m1 m2 Hm [[e1 le1] m1'] H.
  simpl in *.
  destruct H as [Hfvnr Hfpnr Hfvpd Hm1' Hle1].
  pose proof (empty_env_match R w) as Hee.
  destruct (alloc_variables_match R w ge _ _ Hee _ _ Hm _ (e1, m1') Hm1')
    as ((e2 & m2') & Hm2' & p' & Hp' & He & Hm').
  transport Hle1.
  exists (e2, x, m2').
  simpl in *.
  split.
  - constructor; eauto.
  - rauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  rel_curry2_set_le_transport @function_entry2 : typeclass_instances.

Global Instance step2_rel R:
  Monotonic
    (@step2)
    (|= (fun w => psat (genv_valid R w)) ++>
        state_match R ++> - ==> k1 set_le (<> state_match R)).
Proof.
  intros w xge ge Hge s1 s2 Hs t s1' H1.
  pose proof (coreflexivity _ _ Hge); subst.
  deconstruct H1 ltac:(fun x => pose (c := x)); inv Hs;
  try
    (transport_hyps;
       repeat match goal with
         | H: cont_match _ _ (_ _) _ |- _ =>
           let Hl := fresh H "l" in
           let Hr := fresh H "r" in
           rinversion_tac H Hl Hr; clear H; inv Hl
         | H: (eq * cont_match _ _)%rel (_, _) _ |- _ =>
           let Hl := fresh H "l" in
           let Hr := fresh H "r" in
           rinversion_tac H Hl Hr; clear H; inv Hl
       end;
       subst;
       eexists; split;
         [ eapply c; eauto; fail
         | eexists; split; rauto ]).

  - transport_hyps.
    eexists; split.
    eapply c; eauto.
    {
      clear - Hge e3 e4 H3. destruct Hge as [Hge].
      destruct H3; try discriminate. simpl in *.
      destruct Ptrofs.eq_dec; inv e3.
      assert (b2 = fb) by eauto using genv_valid_block_inject_eq; subst.
      eapply genv_valid_funct_ptr in e4; eauto. red in e4.
      assert (delta = 0) by congruence. subst.
      change (Ptrofs.add _ _) with Ptrofs.zero.
      destruct Ptrofs.eq_dec; congruence.
    }
    eexists; split; rauto.
Qed.

Global Instance step_rel_params:
  Params (@step2) 3.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @step2 : typeclass_instances.

Lemma semantics2_rel R p:
  forward_simulation (cc_c R) (cc_c R) (Clight.semantics2 p) (Clight.semantics2 p).
Proof.
  pose (ms := fun w s1 s2 => genv_valid R w (globalenv p) /\
                             klr_diam tt (state_match R) w s1 s2).
  apply forward_simulation_step with ms.
  - reflexivity.
  - destruct 1. auto.
  - intros w _ _ [id sg vargs1 vargs2 m1 m2 Hvargs Hm] s1 Hs1.
    inv Hs1. simpl in *. subst.
    assert (genv_valid R w (globalenv p)) by (eapply cklr_wf; eauto).
    exists (Callstate (Block.glob id) vargs2 Kstop m2). split.
    + econstructor; eauto.
      eapply val_casted_list_inject; rauto.
    + split; eauto.
      exists w; split; try rauto.
  - intros w s1 s2 q1 [Hge Hs] Hq1.
    destruct Hs as (w' & Hw' & Hs).
    destruct Hq1. inv Hs.
    eexists w', (cq id sg _ _). repeat apply conj.
    + assert (Hge': genv_valid R w' (globalenv p)) by (eapply cklr_wf; eauto).
      econstructor; simpl; eauto.
    + econstructor.
      eassumption.
    + intros r1 [vres2 m2'] s1' (w'' & Hw'' & Hvres & Hm') Hs1'.
      inv Hs1'. cbn [fst snd] in *.
      eexists. split.
      * constructor.
      * split; eauto.
        exists w''. split; [rauto | ].
        constructor; rauto.
  - intros w s1 s2 r1 (Hge & w' & Hw' & Hs) H. destruct H as [v1' m1'].
    inv Hs. inv H4.
    eexists (_, _). split.
    + simpl. rauto.
    + constructor.
  - intros w s1 t s1' Hstep s2 (Hge & w' & Hw' & Hs).
    simpl in Hstep.
    assert (Hge': genv_valid R w' (globalenv p))
      by (destruct Hs; eapply cklr_wf; eauto).
    apply psat_intro in Hge'.
    transport Hstep.
    eexists; split; try rauto.
    split; rauto.
Qed.
