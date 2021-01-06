Require Import Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.
Require Import Mach LanguageInterface CallconvAlgebra CKLR CKLRAlgebra.
Require Import Eventsrel.
Require Import Linking.
Require Import Asm.

Lemma free_same m b lo hi m':
  Mem.free m b lo hi = Some m' ->
  lo >= hi ->
  m = m'.
Proof.
  intros H H'.
  apply Mem.free_result in H.
  destruct m as [cont acc next]. destruct m' as [cont' acc' next'].
  unfold Mem.unchecked_free in H. simpl in H. inv H.
  apply Mem.mkmem_ext; auto; clear -H'.
Admitted.

Lemma ptrofs_add_0 ofs: Ptrofs.add ofs (Ptrofs.repr 0) = ofs.
Admitted.

Section PROG.
  Context (p: program).
  Definition genv_match R w: relation genv :=
    (match_stbls R w) !! (fun se => Genv.globalenv se p).
  Global Instance genv_genv_match R w:
    Related
      (genv_match R w)
      (Genv.match_genvs (mi R w) (match_globdef (fun _ => eq) eq p))
      subrel.
  Proof.
    unfold genv_match. rstep.
    intros ge1 ge2 Hge. destruct Hge as [se1 se2].
    eapply Genv.globalenvs_match.
    - red. intuition auto.
      induction (AST.prog_defs p)
        as [ | [id [f|[ ]]] ? ?];
        repeat (econstructor; eauto using incl_refl, linkorder_refl).
      apply linkorder_refl.
    - apply match_stbls_proj; auto.
  Qed.

  Lemma match_prog {C} `{!Linking.Linker C} (c: C):
    Linking.match_program_gen (fun _ => eq) eq c p p.
  Proof.
    repeat apply conj; auto.
    induction (AST.prog_defs p) as [ | [id [f|v]] defs IHdefs];
      repeat (econstructor; eauto).
    - apply Linking.linkorder_refl.
    - destruct v; constructor; auto.
  Qed.
  
  Global Instance find_funct_inject R w ge1 v1 ge2 v2 f:
    Transport (genv_match R w * Val.inject (mi R w)) (ge1, v1) (ge2, v2)
              (Genv.find_funct ge1 v1 = Some f)
              (Genv.find_funct ge2 v2 = Some f).
  Proof.
    intros [Hge Hv] Hf. cbn in *.
    destruct Hge. apply match_stbls_proj in H. cbn in Hf.
    edestruct @Genv.find_funct_match as (?&?&?&?&?); eauto using (match_prog tt).
    cbn in *. subst. auto.
  Qed.
  Instance transport_find_symbol_genv R w ge1 ge2 id b1:
    Transport (genv_match R w) ge1 ge2
              (Genv.find_symbol ge1 id = Some b1)
              (exists b2,
                  Genv.find_symbol ge2 id = Some b2 /\
                  block_inject_sameofs (mi R w) b1 b2).
  Proof.
    intros Hge Hb1. edestruct @Genv.find_symbol_match as (b2 & ? & ?); eauto.
    destruct Hge. eapply match_stbls_proj. eauto.
  Qed.

  Global Instance genv_match_acc R:
    Monotonic (genv_match R) (wacc R ++> subrel).
  Proof.
    intros w w' Hw' _ _ [se1 se2 Hge].
    eapply (match_stbls_acc R w w') in Hge; eauto.
    eapply (rel_push_rintro (fun se => Genv.globalenv se p) (fun se => Genv.globalenv se p));
      eauto.
  Qed.

  Definition regset_inject R (w: world R): rel regset regset :=
    forallr - @ r, (Val.inject (mi R w)).

  Inductive inject_ptr_sameofs (mi: meminj): val -> val -> Prop :=
  | inj_ptr_sameofs:
      forall b1 b2 ofs,
        mi b1 = Some (b2, 0%Z) ->
        inject_ptr_sameofs mi (Vptr b1 ofs) (Vptr b2 ofs)
  | inj_ptr_undef:
      forall v,
        inject_ptr_sameofs mi Vundef v.
  
  Definition regset_inject' R (w: world R): rel regset regset :=
    fun rs1 rs2 =>
      forall r: preg,
        (r <> PC -> Val.inject (mi R w) (rs1 r) (rs2 r)) /\
        (r = PC -> inject_ptr_sameofs (mi R w) (rs1 r) (rs2 r)).

  Global Instance regset_inj_subrel R w:
    Related
      (regset_inject' R w)
      (regset_inject R w)
      subrel.
  Proof.
    repeat rstep.
    intros rs1 rs2 rel.
    unfold regset_inject', regset_inject in *.
    intros r. destruct (PregEq.eq r PC) as [-> | ].
    - specialize (rel PC) as [? H].
      destruct H. auto. econstructor. eauto.
      symmetry. apply ptrofs_add_0.
      constructor.
    - apply rel. auto.
  Qed.
  
  Inductive outcome_match R (w: world R): rel outcome outcome :=
  | Next_match:
      Monotonic
        (@Next')
        (regset_inject R w ++> match_mem R w ++> - ==> outcome_match R w)
  | Stuck_match o:
      outcome_match R w Stuck o.

  Inductive state_match R w: rel Asm.state Asm.state :=
  | State_rel:
      Monotonic
        (@Asm.State)
        (regset_inject R w ++> match_mem R w ++> - ==> state_match R w).
  Inductive state_match' R w: rel Asm.state Asm.state :=
  | State_rel':
      Monotonic
        (@Asm.State)
        (regset_inject' R w ++> match_mem R w ++> - ==> state_match' R w).

  Global Instance set_inject R w:
    Monotonic
      (@Pregmap.set val)
      (- ==> (Val.inject (mi R w)) ++> regset_inject R w ++> regset_inject R w).
  Proof.
    unfold regset_inject, Pregmap.set.
    repeat rstep.
  Qed.

  Lemma set_inject' R w:
    forall r: PregEq.t,
      r <> PC ->
      forall v1 v2: val,
        Val.inject (mi R w) v1 v2 ->
        forall rs1 rs2: regset,
          regset_inject' R w rs1 rs2 ->
          regset_inject' R w (rs1 # r <- v1) (rs2 # r <- v2).
  Proof.
    intros r Hr.
    unfold regset_inject', Pregmap.set.
    intros v1 v2 Hv rs1 rs2 Hrs r'.
    split.
    - intros. destruct (PregEq.eq r' r). auto.
      destruct (PregEq.eq r' PC). congruence. apply Hrs. auto.
    - intros. destruct (PregEq.eq r' r). congruence.
      apply Hrs. auto.
  Qed.
  
  Global Instance nextinstr_inject R w:
    Monotonic
      (@nextinstr)
      (regset_inject R w ++> regset_inject R w).
  Proof.
    unfold nextinstr.
    repeat rstep.
    apply set_inject; auto.
    apply Val.offset_ptr_inject; auto.
  Qed.

  Global Instance undef_regs_inject R:
    Monotonic
      (@undef_regs)
      (|= - ==> regset_inject R ++> regset_inject R).
  Proof.
    repeat rstep. revert x0 y H.
    induction x.
    - auto.
    - intros. cbn.
      apply IHx. apply set_inject; auto.
  Qed.

  Global Instance eval_addrmode32_inject R w:
    Monotonic
      (@eval_addrmode32)
      (genv_match R w ++> - ==> regset_inject R w ++> Val.inject (mi R w)).
  Proof.
    unfold eval_addrmode32. 
    repeat rstep; auto. 
    apply genv_genv_match; auto.
  Qed.
  Global Instance eval_addrmode64_inject R w:
    Monotonic
      (@eval_addrmode64)
      (genv_match R w ++> - ==> regset_inject R w ++> Val.inject (mi R w)).
  Proof.
    unfold eval_addrmode64.
    repeat rstep; auto.
    apply genv_genv_match; auto.
  Qed.
  Global Instance eval_addrmode_inject R w:
    Monotonic
      (@eval_addrmode)
      (genv_match R w ++> - ==> regset_inject R w ++> Val.inject (mi R w)).
  Proof.
    unfold eval_addrmode.
    repeat rstep.
    apply eval_addrmode64_inject; auto.
    apply eval_addrmode32_inject; auto.
  Qed.

  Global Instance exec_load_match R:
    Monotonic
      (@exec_load)
      (|= genv_match R ++> - ==> match_mem R ++>  - ==> regset_inject R ++> - ==> outcome_match R).
  Proof.
    unfold exec_load.
    repeat rstep.
    destruct (Mem.loadv _ _ _) eqn:Heq.
    - eapply transport in Heq.
      2: { apply cklr_loadv; eauto. eapply eval_addrmode_inject; eauto. }
      destruct Heq as (b & Hb & vinj).
      rewrite Hb. constructor.
      repeat apply set_inject; rstep.
      repeat apply set_inject; rstep.
      auto. auto.
    - constructor.
  Qed.

  Global Instance regset_inject_acc:
    Monotonic
      (@regset_inject)
      (forallr - @ R, acc tt ++> subrel).
  Proof.
    unfold regset_inject.
    repeat rstep.
    intros rs1 rs2 Hrs i. rauto.
  Qed.
  
  Global Instance exec_store_match R:
    Monotonic
      (@exec_store)
      (|= genv_match R ++> - ==> match_mem R ++> - ==> regset_inject R ++> - ==> - ==> <> outcome_match R).
  Proof.
    unfold exec_store.
    repeat rstep.
    destruct (Mem.storev _ _ _ _) eqn:Heq.
    - eapply transport in Heq.
      2: { apply cklr_storev. eauto. eapply eval_addrmode_inject. eauto. eauto. apply H1. }
      destruct Heq as (b & Hb & w' & Hw' & Hmm).
      exists w'. split. auto.
      rewrite Hb. constructor.
      unfold nextinstr_nf. rstep.
      apply undef_regs_inject. apply undef_regs_inject.
      rauto. auto.
    - exists w. split. rauto. constructor.
  Qed.
  
  Global Instance val_negativel_inject f:
    Monotonic (@Val.negativel) (Val.inject f ++> Val.inject f).
  Proof.
    unfold Val.negativel. rauto.
  Qed.
  Global Instance val_subl_overflow_inject f:
    Monotonic (@Val.subl_overflow) (Val.inject f ++> Val.inject f ++> Val.inject f).
  Proof.
    unfold Val.subl_overflow. rauto.
  Qed.

  Ltac match_regs :=
    match goal with
    | [ Hrs: regset_inject _ _ _ _ |-
        _ (match _ ?r with | _ => _ end) (match _ ?r with | _ => _ end) ] =>
      let H := fresh "H" in
      specialize (Hrs r) as H; inv H; try rstep
    | _ => idtac
    end.
  
  Global Instance eval_testcond_le R w:
    Monotonic
      (@eval_testcond)
      (- ==> regset_inject R w ++> option_le eq).
  Proof.
    intros c rs1 rs2 Hrs.
    unfold eval_testcond. destruct c; repeat match_regs.
  Qed.
  
  Local Hint Resolve Stuck_match.
  
  Global Instance goto_label_inject R w:
    Monotonic
      (@goto_label)
      (- ==> - ==> regset_inject' R w ++> match_mem R w ++> outcome_match R w).
  Proof.
    intros f l rs1 rs2 Hrs' m1 m2 Hm.
    apply regset_inj_subrel in Hrs' as Hrs.
    unfold goto_label. destruct (label_pos _ _ _); auto.
    specialize (Hrs' PC). destruct Hrs' as [? HPC].
    exploit HPC; auto. intros [ | ]; auto.
    constructor; auto. apply set_inject; auto.
    eapply Val.inject_ptr. eauto.
    symmetry. apply ptrofs_add_0.
  Qed.

  Ltac match_simpl :=
    repeat
      match goal with
      | [ |- (<> outcome_match _)%klr _ (exec_store _ _ _ _ _ _ _) (exec_store _ _ _ _ _ _ _) ] =>
        apply exec_store_match; auto
      | [ |- (<> outcome_match _)%klr _ (exec_load _ _ _ _ _ _) (exec_load _ _ _ _ _ _) ] =>
        eexists; split; [rauto | apply exec_load_match; auto]
      | [ |- (<> outcome_match _)%klr _ (Next _ _) (Next _ _) ] =>
        eexists; split; [rauto | constructor; auto]
      | [ |- (<> outcome_match _)%klr _ Stuck _ ] =>
        eexists; split; [rauto | constructor]
      | [ |- (regset_inject _ _ (nextinstr _) (nextinstr _))] => rstep
      | [ |- (regset_inject _ _ (nextinstr_nf _) (nextinstr_nf _))] => unfold nextinstr_nf; rstep
      | [ |- (regset_inject _ _ (undef_regs _ _) (undef_regs _ _))] => apply undef_regs_inject
      | [ |- (regset_inject _ _ (_ # _ <- _) (_ # _ <- _))] => apply set_inject
      | [ |- (Val.inject _ (Genv.symbol_address _ _ _) (Genv.symbol_address _ _ _))] => rstep
      | [ Hrs: regset_inject _ _ _ _ |-
          _ (match _ ?r with | _ => _ end) (match _ ?r with | _ => _ end) ] =>
        let H := fresh "H" in
        specialize (Hrs r) as H; inv H; try repeat rstep
      | [ |- _ (match ?x with | _ => _ end) (match ?x with | _ => _ end)] => repeat rstep
      | [ |- regset_inject _ _ _ (match ?x with | _ => _ end)] => destruct x
      | [ |- (Val.inject _ _ _)] => try rstep
      | [ |- option_le _ _ _ ] => rstep
      | [ |- Genv.match_stbls _ _ _ ] => apply genv_genv_match
      | _ => idtac
      end; auto.

  Definition init_nb_match R w: rel block block :=
    (Val.inject (mi R w) ++> eq) @@ inner_sp.
  
  Global Instance inner_sp_rel R w:
    Monotonic
      (@inner_sp)
      (init_nb_match R w ++> Val.inject (mi R w) ++> eq).
  Proof.
    unfold init_nb_match. repeat rstep. apply H. auto.
  Qed.
 
  Global Instance exec_instr_match R:
    Monotonic
      (@exec_instr)
      (|= init_nb_match R ++>
       genv_match R ++> - ==> - ==>
       regset_inject' R ++> match_mem R ++>
       (<> outcome_match R)).
  Proof.
    intros w b1 b2 Hb ge1 ge2 Hge f i rs1 rs2 Hrs' m1 m2 Hm.
    (* destruct i; cbn; repeat match_simpl. *)
    destruct i; cbn; apply regset_inj_subrel in Hrs' as Hrs;
      unfold compare_ints, compare_longs, compare_floats, compare_floats32, undef_regs;
      match_simpl; repeat rstep; try rauto; auto; match_simpl.
    - apply eval_addrmode32_inject; auto.
    - apply eval_addrmode64_inject; auto.
    - eexists; split; [rauto | apply goto_label_inject; auto].
      apply set_inject'; [discriminate | auto | ].
      apply set_inject'; [discriminate | auto | auto ].
    - rewrite inner_sp_rel; eauto.         (* inner_sp *)
      eexists; split; [rauto | constructor; auto; match_simpl ].
    - destruct m as [m1' b1']. destruct n as [m2' b2'].
      destruct H1 as (Hw & Hm' & Hb'). cbn [fst snd] in *.
      destruct (Mem.store _ _ _ _) eqn: Hst.
      2: { match_simpl. }
      eapply transport in Hst as (mx & Hst' & Hmx).
      2: { clear Hst. repeat rstep. eapply regset_inject_acc; eauto. }
      rewrite Hst'. clear Hst'. destruct Hmx as (w'' & Hw'' & Hmx).
      destruct (Mem.store _ _ _ _) eqn: Hst.
      2: { match_simpl. }
      eapply transport in Hst as (my & Hst' & Hmy).
      2: { clear Hst. repeat rstep. eapply regset_inject_acc; [ | eauto]. rauto. }
      rewrite Hst'. clear Hst'. destruct Hmy as (w''' & Hw''' & Hmy).
      exists w'''. split. rauto.
      constructor; [ match_simpl | rauto ].
      + apply block_sameofs_ptrbits_inject.
        split; auto. eapply block_inject_sameofs_incr; [ | eauto ]. rstep. cbn in *; rauto.
      + eapply regset_inject_acc; [ | eauto ]. rauto.
      + rauto.
    - destruct (Mem.loadv _ _ _) as [ ra1 | ] eqn: Hld.
      2: { match_simpl. }
      eapply transport in Hld as (ra2 & Hld' & Hra).
      2: { clear Hld. repeat rstep. eapply Hrs. }
      rewrite Hld'. clear Hld'.
      destruct (Mem.loadv _ _ _) as [| rsp1] eqn: Hld.
      2: { match_simpl. }
      eapply transport in Hld as (rsp2 & Hld' & Hrsp).
      2: { clear Hld. repeat rstep. eapply Hrs. }
      rewrite Hld'. clear Hld'.
      specialize (Hrs SP) as Hsp. inv Hsp; match_simpl.
      erewrite cklr_weak_valid_pointer_address_inject; eauto.
      destruct Mem.free eqn: Hfree.
        2: { match_simpl. }
        eapply transport in Hfree as (m' & Hfree' & Hm').
        2: { clear Hfree. repeat rstep. eauto. }
        destruct Hm' as (w' & Hw' & Hm').
        rewrite Hfree'.
        exists w'. split. rauto. constructor; auto. rstep.
        apply set_inject. rstep.
        apply set_inject. rstep.
        eapply regset_inject_acc; eauto.
      + admit.
  Admitted.

  Global Instance find_funct_ptr_inject R w ge1 b1 ge2 b2 f:
    Transport (genv_match R w * block_inject_sameofs (mi R w)) (ge1, b1) (ge2, b2)
              (Genv.find_funct_ptr ge1 b1 = Some f)
              (Genv.find_funct_ptr ge2 b2 = Some f).
  Proof.
    intros [Hge Hb] Hf. cbn in *.
    destruct Hge. apply match_stbls_proj in H. unfold Genv.find_funct_ptr in *.
    destruct Genv.find_def as [[|]|] eqn:Hfd; try congruence. inv Hf.
    edestruct @Genv.find_def_match as (tg &?&?&?); eauto using (match_prog tt).
    inv H0. inv H1. rewrite H4. auto.
  Qed.

  Lemma reg_inj_strengthen R w ge1 ge2 rs1 rs2 b ofs f:
    genv_match R w ge1 ge2 -> 
    rs1 PC = Vptr b ofs ->
    Genv.find_funct_ptr ge1 b = Some f ->
    regset_inject R w rs1 rs2 ->
    regset_inject' R w rs1 rs2.
  Proof.
    intros Hge Hpc Hf Hrs r'.
    split.
    - intros. apply Hrs.
    - intros ->. specialize (Hrs PC). rewrite Hpc in *.
      inv Hrs. eapply genv_genv_match in Hge.
      unfold Genv.find_funct_ptr in Hf.
      destruct (Genv.find_def ge1 b) eqn: Hfd; try congruence.
      edestruct @Genv.find_def_match_genvs as (?&?&?&?); eauto.
      rewrite H3 in *. rewrite ptrofs_add_0. constructor. auto.
  Qed.

  Global Instance set_res_inject R w:
    Monotonic
      (@set_res)
      (- ==> Val.inject (mi R w) ++> regset_inject R w ++> regset_inject R w).
  Proof.
    unfold set_res. intros res.
    induction res.
    - repeat rstep. match_simpl.
    - repeat rstep.
    - repeat rstep.
  Qed.

  Global Instance extcall_arg_inject R w:
    Monotonic
      (@extcall_arg)
      (regset_inject R w ++> match_mem R w ++> - ==> set_le (Val.inject (mi R w))).
  Proof.
    intros rs1 rs2 Hrs m1 m2 Hm l v Hv.
    inv Hv.
    - eexists. split.
      + eapply extcall_arg_reg.
      + auto.
    - eapply transport in H0.
      2: { clear H0. apply cklr_loadv; eauto. rstep. rstep.  apply Hrs. eauto. }
      destruct H0 as (v' & Hv' & vv).
      exists v'. split.
      + eapply extcall_arg_stack; eauto.
      + auto.
  Qed.

  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_le_transport @extcall_arg_inject : typeclass_instances.
  
  Global Instance extcall_arg_pair_inject R w:
    Monotonic
      (@extcall_arg_pair)
      (regset_inject R w ++> match_mem R w ++> - ==> set_le (Val.inject (mi R w))).
  Proof.
    intros rs1 rs2 Hrs m1 m2 Hm lp vs Hvs.
    inv Hvs.
    - eapply extcall_arg_inject in H as (?&?&?); eauto.
      eexists. split; eauto. constructor. auto.
    - eapply extcall_arg_inject in H as (?&?&?); eauto.
      eapply extcall_arg_inject in H0 as (?&?&?); eauto.
      eexists. split. econstructor; eauto.
      rstep; eauto.
  Qed.  
  
  Global Instance extcall_arguments_inject R w:
    Monotonic
      (@extcall_arguments)
      (regset_inject R w ++> match_mem R w ++> - ==> set_le (Val.inject_list (mi R w))).
  Proof.
    unfold extcall_arguments.
    intros rs1 rs2 Hrs m1 m2 Hm sg args1 H.
    remember (loc_arguments sg) as ls. clear Heqls.
    induction H.
    - exists nil. split; constructor.
    - destruct IHlist_forall2 as (bs & IH).
      eapply extcall_arg_pair_inject in H; eauto.
      destruct H as (b' & Hb & bb).
      eexists (b' :: bs). split.
      + constructor. auto. apply IH.
      + constructor. auto. apply IH.
  Qed.

  Global Instance set_pair_inject R w:
    Monotonic
      (@set_pair)
      (- ==> Val.inject (mi R w) ++> regset_inject R w ++> regset_inject R w).
  Proof.
    unfold set_pair.
    repeat rstep; match_simpl.
  Qed.

  Global Instance under_caller_save_regs_inject R w:
    Monotonic
      (@undef_caller_save_regs)
      (regset_inject R w ++> regset_inject R w).
  Proof.
    unfold undef_caller_save_regs.
    repeat rstep. intros r.
    destruct (_ || _).
    apply H. auto.
  Qed.

  Global Instance step_rel R:
    Monotonic
      (@step)
      (|= init_nb_match R ==> genv_match R ++>
          state_match R ++> - ==> k1 set_le (<> state_match R)).
  Proof.
    intros w b1 b2 Hb ge1 ge2 Hge s1 s2 Hs t s1' H1.
    destruct H1 as [ b ofs f i rs m rs' m' live HPC Hf Hi He |
                     b ofs f ef args res rs m vargs t vres rs' m' HPC Hf Hi Hargs Hec Hnext |
                     b ef args res rs m t rs' m' HPC Hf Hargs Hec Hnext ].
    - destruct s2 as [rs2 m2 live2]. inv Hs.
      assert (Hrs' := reg_inj_strengthen _ _ _ _ _ _ _ _ _ Hge HPC Hf H1).
      destruct (exec_instr_match R w b1 b2 Hb ge1 ge2 Hge f i rs rs2 Hrs' m m2 H6) as (w' & Hw' & Ho).
      rewrite He in Ho. inv Ho. exists (State y y0 live). split.
      + specialize (Hrs' PC) as [? Hpc].
        exploit Hpc. auto. intros H'. inv H'; try congruence.
        rewrite HPC in H0. inv H0.
        eapply exec_step_internal; eauto.
        * eapply find_funct_ptr_inject; eauto.
          split; cbn; eauto.
      + exists w'. split. auto. split; auto.
    - destruct s2 as [rs2 m2 live2]. inv Hs.
      specialize (H1 SP) as Hsp. simpl in Hsp.
      eapply transport in Hargs.
      2: {
        clear Hargs. apply eval_builtin_args_rel; eauto.
        apply genv_genv_match. apply Hge.
        apply H1. }
      destruct Hargs as (vargs' & Hvargs' & Hvs).
      eapply transport in Hec.
      2: {
        clear Hec. apply external_call_rel; eauto.
        rstep. apply genv_genv_match. eauto.
      }
      destruct Hec as (vres' & m2' & Hec' & Hv).
      assert (Hrs' := reg_inj_strengthen _ _ _ _ _ _ _ _ _ Hge HPC Hf H1).
      specialize (Hrs' PC) as [H Hpc]. exploit Hpc. auto. clear H Hpc.
      intros Hpc. inv Hpc; try congruence. rewrite HPC in H. inv H. apply symmetry in H0.
      eapply find_funct_ptr_inject in Hf.
      2: { split. apply Hge. apply H2. }
      eexists. split.
      + eapply exec_step_builtin; eauto.
      + destruct Hv as (w' & Hw' & Hv & Hm').
        cbn [fst snd] in *.
        exists w'. split; auto.
        apply State_rel; auto.
        repeat match_simpl.
        apply set_res_inject; auto.
        match_simpl. eapply regset_inject_acc; eauto.
    - destruct s2 as [rs2 m2 live2]. inv Hs.
      eapply extcall_arguments_inject in Hargs as (args' & Hargs' & Haa); eauto.
      eapply transport in Hec.
      2: {
        clear Hec. apply external_call_rel; eauto.
        rstep. apply genv_genv_match. apply Hge.
      }
      destruct Hec as (vres' & m2' & Hec' & (w' & Hw' & Hv & Hm)).
      assert (Hrs' := reg_inj_strengthen _ _ _ _ _ _ _ _ _ Hge HPC Hf H1).
      specialize (Hrs' PC) as [H Hpc]. exploit Hpc. auto. clear H Hpc.
      intros Hpc. inv Hpc; try congruence. rewrite HPC in H. inv H. apply symmetry in H0.
      eapply find_funct_ptr_inject in Hf.
      2: { split. apply Hge. apply H2. }
      eexists. split.
      + eapply exec_step_external; eauto.
      + exists w'. split; auto.
        rewrite inner_sp_rel; eauto.
        apply State_rel; auto.
        match_simpl. eapply regset_inject_acc; eauto.
        apply set_pair_inject. auto.
        apply under_caller_save_regs_inject.
        eapply regset_inject_acc; eauto.
  Qed.
 
End PROG.
  
Lemma semantics_asm_rel p R:
  forward_simulation (cc_asm R) (cc_asm R) (Asm.semantics p) (Asm.semantics p).
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn -[semantics] in *.
  pose (ms := fun s1 s2 =>
                klr_diam tt (genv_match p R * (init_nb_match R * state_match R))
                         w
                         (Genv.globalenv se1 p, s1)
                         (Genv.globalenv se2 p, s2)).
  apply forward_simulation_step with (match_states := ms); cbn.
  - intros [rs1 m1] [rs2 m2] [Hrs Hm].
    eapply Genv.is_internal_match; eauto.
    + repeat apply conj; auto.
      induction (prog_defs p) as [ | [id [f|v]] defs IHdefs]; repeat (econstructor; eauto).
      * instantiate (2 := fun _ => eq). reflexivity.
      * instantiate (1 := eq). destruct v. constructor. auto.
    + eapply match_stbls_proj; auto.
    + intros. rewrite H. auto.
    + admit.                    (* PC <> Vundef *)
  - intros [rs1 m1] [rs2 m2] [nb1 s1] Hs [Hq Hnb]. inv Hs. inv Hq.
    assert (Hge: genv_match p R w (Genv.globalenv se1 p) (Genv.globalenv se2 p)).
    {
      cut (match_stbls R w (Genv.globalenv se1 p) (Genv.globalenv se2 p)); eauto.
      eapply (rel_push_rintro (fun se => Genv.globalenv se p) (fun se => Genv.globalenv se p)).
    }
    specialize (H PC) as Hpc.
    transport_hyps.
    exists (Mem.nextblock m2, State rs2 m2 true).
    repeat apply conj; auto.
    + econstructor.
      * eauto. 
      * specialize (H SP) as Hsp. inv Hsp; try congruence.
      * specialize (H RA) as Hsp. inv Hsp; try congruence.
    + cbn. esplit. split. rauto.
      split; cbn; auto.
      split; cbn; auto.
      * unfold init_nb_match. intros v1 v2 Hv.
        unfold inner_sp. inv Hv; try congruence. 2: { admit. }
        edestruct cklr_valid_block as [Hl Hr]; try rstep; eauto.
        destruct plt; destruct plt; try congruence; exfalso.
        -- apply n. apply Hl. auto.
        -- apply n. apply Hr. auto.
      * constructor; auto.
  - intros [nb1 s1] [nb2 s2] [rs1 m1] (w' & Hw' & Hge & Hb & Hs) H. cbn in *.
    inv H. inv Hs.
    eexists. split.
    + constructor.
    + exists w'. split; auto. constructor; auto.
  - intros [nb1 s1] [nb2 s2] qx1 (w' & Hw' & Hge & Hb & Hs) H. cbn [fst snd] in *.
    inversion Hs as [rs1 rs2 Hrs m1 m2 Hm live]. subst.
    inv H. specialize (Hrs PC) as Hpc. simpl in Hpc.
    transport_hyps.
    eexists w', _. repeat apply conj.
    + econstructor. eauto.
    + constructor; eauto.
    + rauto.
    + intros [rrs1 rm1] [rrs2 rm2] [rb1 rst1] (w'' & Hw'' & Hr) [H H1].
      inv H.
      eexists (_, _). repeat apply conj.
      * econstructor. admit.
      (*   remember (Mem.alloc rm1 0 0) as mres. destruct mres as [m1' b1]. *)
      (*   remember (Mem.alloc rm2 0 0) as mres. destruct mres as [m2' b2]. *)
      (*   assert (Hb1: b1 = Mem.nextblock rm1). eapply Mem.alloc_result. eauto. *)
      (*   assert (Hb2: b2 = Mem.nextblock rm2). eapply Mem.alloc_result. eauto. *)
      (*   edestruct (cklr_alloc R w'') as (w''' & Hw''' & Hmm). apply Hr. *)
      (*   rewrite <- Heqmres in Hmm. rewrite <- Heqmres0 in Hmm. *)
      (*   destruct Hmm as [Hm' Hb']. cbn [fst snd] in *. *)
      (*   unfold Ple in *. SearchAbout Pos.le Pos.lt. *)
      (*   rewrite Pos.le_nlt in *. *)
      (*   assert (Hvb: ~ Mem.valid_block m1 b1). subst b1. apply H7. *)
      (*   assert (inject_separated (mi R w') (mi R w''') m1 m2). *)
      (*   { admit. } *)
      (*   exploit H. 2: apply Hb'. *)
      (*   SearchAbout Mem.valid_block. *)
      (*   eapply Mem.mi_freeblocks. admit. *)
      (*   apply Hvb. subst b2. intros. apply H0. *)
      * reflexivity.
      * exists w''. split. rauto.
        assert (init_nb_match R w'' nb1 nb2).
        {
          unfold init_nb_match. intros v1 v2 Hv. specialize (Hb v1 v2).
          unfold inner_sp. inv Hv; auto. simpl in Hb.
          destruct (mi R w' b1) as [[b1' d] |] eqn: Hmi.
          - exploit mi_acc. apply Hw''. apply Hmi. intros Hmi'. rewrite Hmi' in H. clear Hmi'. inv H.
            exploit Hb. eapply Val.inject_ptr; eauto. auto.
          - assert (Hsp: inject_separated (mi R w') (mi R w'') m1 m2).
            { admit. }
            exploit Hsp. apply Hmi. apply H. intros [Hvb1 Hvb2].
            assert (nb1 <= Mem.nextblock m1)%positive. admit.
            assert (nb2 <= Mem.nextblock m2)%positive. admit.
            destruct (plt b1 nb1); destruct (plt b2 nb2);
              auto; unfold Mem.valid_block in *; unfold Plt in *; exfalso.
            apply Hvb1. SearchAbout Pos.lt.
            eapply Pos.lt_le_trans. eauto. eauto.
            apply Hvb2.
            eapply Pos.lt_le_trans. eauto. eauto.
        }
        inv Hr. repeat apply conj; cbn.
        -- eapply genv_match_acc.
           apply Hw''. apply Hge.
        -- auto.
        -- rewrite inner_sp_rel; try econstructor; eauto.
  - intros [nb1 s1] t [nb1' s1'] [Hstep ->] [nb2 s2] (w' & Hw' & Hge & Hnb & Hs).
    cbn [fst snd] in *.
    eapply step_rel in Hstep as (s2' & Hstep' & (w'' & Hw'' & ss)); eauto.
    eexists. split.
    + instantiate (1 := (_, _)). cbn.
      split. eauto. reflexivity.
    + split with (x:=w''). split; try rauto.
      split. cbn. eapply genv_match_acc. rauto. auto.
      split; cbn. rauto. auto.
  - apply well_founded_ltof.
Admitted.
