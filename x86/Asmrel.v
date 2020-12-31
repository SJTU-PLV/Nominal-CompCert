Require Import Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.
Require Import Mach LanguageInterface CallconvAlgebra CKLR CKLRAlgebra.
Require Import Asm.

Section PROG.
  Context (p: program).
  Definition genv_match R w: relation genv :=
    (match_stbls R w) !! (fun se => Genv.globalenv se p).

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

  Global Instance set_inject R w:
    Monotonic
      (@Pregmap.set val)
      (- ==> (Val.inject (mi R w)) ++> regset_inject R w ++> regset_inject R w).
  Proof.
    unfold regset_inject, Pregmap.set.
    repeat rstep.
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

  Global Instance symbol_address_inject R w:
    Monotonic
      (@Genv.symbol_address)
      (genv_match R w ++> - ==> - ==> Val.inject (mi R w)).
  Proof.
    unfold Genv.symbol_address.
    repeat rstep.
    destruct (Genv.find_symbol x x0) eqn: Heq.
    transport_hyps. rewrite H0. rauto.
    constructor.
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
    apply symbol_address_inject; auto.
  Qed.
  Global Instance eval_addrmode64_inject R w:
    Monotonic
      (@eval_addrmode64)
      (genv_match R w ++> - ==> regset_inject R w ++> Val.inject (mi R w)).
  Proof.
    unfold eval_addrmode64.
    repeat rstep; auto.
    apply symbol_address_inject; auto.
  Qed.
  Global Instance eval_addrmode_inject R w:
    Monotonic
      (@eval_addrmode)
      (genv_match R w ++> - ==> regset_inject R w ++> Val.inject (mi R w)).
  Proof.
    unfold eval_addrmode.
    repeat rstep.
    - unfold eval_addrmode64.
      repeat rstep; auto.
      apply symbol_address_inject; auto.
    - unfold eval_addrmode32.
      repeat rstep; auto.
      apply symbol_address_inject; auto.
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

  Ltac match_simpl :=
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
    | [ |- (regset_inject _ _ (undef_regs _ _) (undef_regs _ _))] => apply undef_regs_inject; auto
    | [ |- (regset_inject _ _ (_ # _ <- _) (_ # _ <- _))] => apply set_inject; auto
    | [ |- (Val.inject _ (Genv.symbol_address _ _ _) (Genv.symbol_address _ _ _))] =>
      apply symbol_address_inject; auto
    | [ |- (Val.inject _ _ _)] => auto || rstep; auto
    | [ |- option_le _ _ _ ] => rstep
    | _ => idtac
    end.

  Ltac ss :=
    eexists; split; [rauto | ].

  Global Instance inner_sp_inject R w rs1 rs2 m1 m2 b r:
    Transport (regset_inject R w * match_mem R w) (rs1, m1) (rs2, m2)
              (inner_sp (Mem.nextblock m1) (rs1 r) = b)
              (inner_sp (Mem.nextblock m2) (rs2 r) = b).
  Proof.
  Admitted.

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

  Global Instance exec_instr_match R:
    Monotonic
      (@exec_instr)
      (|= block_inject_sameofs @@ [mi R] ++>
       genv_match R ++> - ==> - ==>
       regset_inject R ++> match_mem R ++> 
       (<> outcome_match R)).
  Proof.
    intros w b1 b2 Hb ge1 ge2 Hge f i rs1 rs2 Hrs m1 m2 Hm.
    destruct i; cbn; repeat match_simpl.
    - apply eval_addrmode32_inject; auto.
    - apply eval_addrmode64_inject; auto.
      Local Hint Resolve Stuck_match.
    - ss. 
      pose (rinj:=Hrs RDX). inv rinj; auto.
      pose (rinj:=Hrs RAX). inv rinj; auto.
      pose (rinj:=Hrs r1). inv rinj; auto.
      destruct (Int.divmodu2 _ _ _) as [ [? ?] | ]; auto.
      constructor; auto. repeat match_simpl.
    - ss.
      pose (rinj:=Hrs RDX). inv rinj; auto.
      pose (rinj:=Hrs RAX). inv rinj; auto.
      pose (rinj:=Hrs r1). inv rinj; auto.
      destruct (Int64.divmodu2 _ _ _) as [ [? ?] | ]; auto.
      constructor; auto. repeat match_simpl.
    - ss.
      pose (rinj:=Hrs RDX). inv rinj; auto.
      pose (rinj:=Hrs RAX). inv rinj; auto.
      pose (rinj:=Hrs r1). inv rinj; auto.
      destruct (Int.divmods2 _ _ _) as [ [? ?] | ]; auto.
      constructor; auto. repeat match_simpl.
    - ss.
      pose (rinj:=Hrs RDX). inv rinj; auto.
      pose (rinj:=Hrs RAX). inv rinj; auto.
      pose (rinj:=Hrs r1). inv rinj; auto.
      destruct (Int64.divmods2 _ _ _) as [ [? ?] | ]; auto.
      constructor; auto. repeat match_simpl.
    - unfold compare_ints.
      repeat match_simpl; rauto.
    - unfold compare_longs.
      repeat match_simpl; rauto.
    - unfold compare_ints.
      repeat match_simpl; rauto.
    - unfold compare_longs.
      repeat match_simpl; rauto.
    - unfold compare_ints.
      repeat match_simpl; rauto.
    - unfold compare_longs.
      repeat match_simpl; rauto.
    - unfold compare_ints.
      repeat match_simpl; rauto.
    - unfold compare_longs.
      repeat match_simpl; rauto.
    - destruct (eval_testcond _ _) eqn: Heq; auto.
      admit.                    (* eval_testcond transport from option_le*)
    - admit.                    (* eval_testcond option_le *)
    - unfold compare_floats.
      pose (rinj:=Hrs r1). inv rinj; auto; try repeat match_simpl.
      pose (rinj:=Hrs r2). inv rinj; auto; try repeat match_simpl.
      + destruct (rs2 r2); repeat match_simpl.
        unfold undef_regs. repeat match_simpl.
      + destruct (rs2 r1); repeat match_simpl.
        destruct (rs2 r2); repeat match_simpl.
        unfold undef_regs. repeat match_simpl.
    - unfold compare_floats32.
      pose (rinj:=Hrs r1). inv rinj; auto; try repeat match_simpl.
      pose (rinj:=Hrs r2). inv rinj; auto; try repeat match_simpl.
      + destruct (rs2 r2); repeat match_simpl.
        unfold undef_regs. repeat match_simpl.
      + destruct (rs2 r1); repeat match_simpl.
        destruct (rs2 r2); repeat match_simpl.
        unfold undef_regs. repeat match_simpl.
    - admit.                     (* goto_label *)
    - admit.                     (* eval_testcond and goto_label *)
    - admit.
    - admit.
    - ss.                       (* inner_sp *)
      admit.
    - auto.
    - edestruct (cklr_alloc R w m1 m2 Hm 0 sz)
        as (w' & Hw' & Hm' & Hb').
      destruct (Mem.alloc m1 0 sz) as [m1' b1'].
      destruct (Mem.alloc m2 0 sz) as [m2' b2'].
      cbn [fst snd] in *.
      destruct (Mem.store _ _ _ _) eqn: Heq.
      edestruct (cklr_store R w' Mptr).
      apply Hm'. instantiate (1 := b1').
      

  Global Instance step_rel R:
    Monotonic
      (@step)
      (|= block_inject_sameofs @@ [mi R] ++> genv_match R ++>
          state_match R ++> - ==> k1 set_le (<> state_match R)).
  Proof.
    intros w b1 b2 Hb ge1 ge2 Hge s1 s2 Hs t s1' H1.
    inv H1.
  Admitted.
  
End PROG.

Lemma semantics_asm_rel p R:
  forward_simulation (cc_asm R) (cc_asm R) (Asm.semantics p) (Asm.semantics p).
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn -[semantics] in *.
  pose (ms := fun s1 s2 =>
                klr_diam tt (genv_match p R * state_match R)
                         w
                         (Genv.globalenv se1 p, s1)
                         (Genv.globalenv se2 p, s2)).
  apply forward_simulation_step with (match_states := ms); cbn.
  - intros [rs1 m1] [rs2 m2] [vm mm].
    cbn. eapply Genv.is_internal_match; eauto.
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
    assert (Hs': Genv.find_funct (Genv.globalenv se2 p) (rs2 PC) = Some (Internal f)).
    {
      specialize (H PC).
      transport_hyps. assumption.
    }
    assert (Hrsp: rs2 RSP <> Vundef).
    {
      specialize (H RSP).
      destruct H; congruence.
    }
    assert (Hra: rs2 RA <> Vundef).
    {
      specialize (H RA).
      destruct H; congruence.
    }
    exists (Mem.nextblock m2, State rs2 m2 true).
    repeat apply conj; auto.
    + econstructor. eassumption. assumption. assumption.
    + cbn. esplit. split. rauto.
      split. cbn. auto. cbn. constructor. apply H. apply H0. auto. auto. auto.
  - intros [nb1 s1] [nb2 s2] [rs1 m1] (w' & Hw' & Hge & Hs) H. cbn in *.
    inv H. inv Hs.
    eexists. split. econstructor.
    exists w'. split. apply Hw'. constructor. assumption. assumption.
  - intros [nb1 s1] [nb2 s2] qx1 (w' & Hw' & Hge & Hs) H. cbn in *.
    inv H. inv Hs.
    assert (Hff: Genv.find_funct (Genv.globalenv se2 p) (rs2 PC) = Some (External (EF_external id sg))).
    {
      specialize (H6 PC).
      transport_hyps. auto.
    }
    eexists w', _. repeat apply conj.
    econstructor. apply Hff. constructor. auto. auto. rauto.
    intros [rrs1 rm1] [rrs2 rm2] [rb1 rs1] (w'' & Hw'' & Hr) [H H1].
    inv H.
    eexists. repeat apply conj. instantiate (1 := (_, _)). cbn.
    split. econstructor. admit.
    reflexivity. exists w''. assert (Hw: w ~> w'). rauto.
    split. rauto.
    split; cbn.
    eapply genv_match_acc. apply Hw''. apply Hge.
    inv Hr. split. apply H. apply H1.
    apply (inner_sp_match p R w'' rrs1 rrs2 m m2). apply H.
    admit. 
    admit.                      (* external call *)
    admit.
  - intros [nb1 s1] t [nb1' s1'] [Hstep ->] [nb2 s2] (w' & Hw' & Hge & Hs).
    cbn [fst snd] in *.
 
    admit.                      (* step *)
  - apply well_founded_ltof.
    
