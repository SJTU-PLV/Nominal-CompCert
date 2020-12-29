Require Import Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.
Require Import Mach LanguageInterface CKLR.
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
  | Stuck_match:
      outcome_match R w Stuck Stuck.

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

  Global Instance exec_instr_match R:
    Monotonic
      (@exec_instr)
      (|= block_inject_sameofs @@ [mi R] ++>
       genv_match R ++> - ==> - ==>
       regset_inject R ++> match_mem R ++> 
       (<> outcome_match R)).
  Proof.
    intros w b1 b2 Hb ge1 ge2 Hge f i rs1 rs2 Hrs m1 m2 Hm.
    destruct i.
    - cbn. exists w. split. rauto. constructor; auto.
      rstep. apply set_inject; auto. 
    - cbn. exists w. split. rauto. constructor; auto.
      unfold nextinstr_nf. rstep.
      repeat apply set_inject; constructor || auto.
    - cbn. exists w. split. rauto. constructor; auto.
      unfold nextinstr_nf. rstep.
      repeat apply set_inject; constructor || auto.
    - 
      

  
  Global Instance step_rel R:
    Monotonic
      (@step)
      (|= block_inject_sameofs @@ [mi R] ++> genv_match R ++>
          state_match R ++> - ==> k1 set_le (<> state_match R)).
  Proof.
    intros w b1 b2 Hb ge1 ge2 Hge s1 s2 Hs t s1' H1.
    inv H1.
  Admitted.
  Global Instance inner_sp_inject R w rs1 rs2 m1 m2 b:
    Transport (regset_rel R w * match_mem R w) (rs1, m1) (rs2, m2)
              (inner_sp (Mem.nextblock m1) (rs1 RSP) = b)
              (inner_sp (Mem.nextblock m2) (rs2 RSP) = b).
  Proof.
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
    
