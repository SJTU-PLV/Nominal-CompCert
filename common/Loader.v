Require Import LogicalRelations.
Require Import OptionRel.
Require Import AST.
Require Import Values.
Require Import Integers.
Require Import LanguageInterface.
Require Import Globalenvs.
Require Import Memory.
Require Import Smallstep.

Definition semantics (L: open_sem li_c li_c) se id m: Smallstep.semantics li_null int :=
  let q := cq (Vptr id Ptrofs.zero) signature_main nil m in
  {|
    step := step (L se q);
    initial_state := initial_state (L se q);
    final_state s r := exists c, final_state (L se q) s c /\ cr_retval c = Vint r;
    at_external _ _ := False;
    after_external _ _ _ := False;
    globalenv := globalenv (L se q);
  |}.

Definition load (L: open_sem li_c li_c): option closed_sem :=
  let se := Genv.symboltbl (skel L) in
  match Genv.find_symbol se (prog_main (skel L)), Genv.init_mem (skel L) with
    | Some id, Some m => Some {| csem := semantics L se id m; symbolenv := se |}
    | _, _ => None
  end.

Lemma load_inj cc L1 L2 L1':
  open_fsim cc cc_inj L1 L2 ->
  load L1 = Some L1' ->
  exists L2',
    load L2 = Some L2' /\
    closed_fsim L1' L2'.
Proof.
  intros HL HL1'. unfold load in *.
  destruct HL as [Hskel HL]. rewrite Hskel in *.
  destruct Genv.find_symbol as [b | ] eqn:Hb; try discriminate.
  destruct Genv.init_mem as [m | ] eqn:Hm; try discriminate.
  inversion HL1'; clear HL1'; subst.
  eexists. split; eauto. red; cbn. split; auto.
  set (se := Genv.symboltbl (skel L2)).
  set (q := cq (Vptr b Ptrofs.zero) signature_main nil m).
  set (thr := Genv.genv_next se).
  set (w := mit (Mem.flat_inj thr) thr thr).
  specialize (HL w se se q q) as [Hvq [index order ms HL]]; auto.
  { admit. (* symboltbl validity *) }
  { subst w se. econstructor. admit. (* match_stbls vs. flat_inj *) }
  { constructor; eauto.
    - econstructor; cbn.
      + unfold Mem.flat_inj.
        destruct Coqlib.plt; eauto.
        elim n. eapply Genv.genv_symb_range. eauto.
      + reflexivity.
    - subst w thr se. cbn. erewrite Genv.init_mem_genv_next by eauto.
      eapply Genv.initmem_inject; eauto.
    - subst w thr se. cbn. erewrite Genv.init_mem_genv_next by eauto.
      reflexivity.
    - subst w thr se. cbn. erewrite Genv.init_mem_genv_next by eauto.
      reflexivity.
    - congruence. }
  econstructor. split; cbn.
  - eapply fsim_order_wf; eauto.
  - eapply fsim_match_initial_states; eauto.
  - intros i s1 s2 n Hs (r1 & Hr1 & Hrn1).
    edestruct @fsim_match_final_states as (r2 & Hr2 & Hr); eauto.
    exists n. split; auto.
    exists r2. split; auto.
    destruct Hr; cbn in Hrn1 |- *; subst.
    inversion H0; auto.
  - contradiction.
  - eapply fsim_simulation; eauto.
Qed.
