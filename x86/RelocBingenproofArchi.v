Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgramBytes.
Require Import Stacklayout Conventions.
Require Import Linking RelocProgLinking Errors.   
Require Import EncDecRet RelocBingen RelocBinDecode.
Require Import RelocProgSemantics RelocProgSemantics1.
Require Import TranslateInstr RelocProgSemantics2.
Require Import RelocProgSemantics RelocProgSemantics1 RelocProgSemanticsArchi1.
Require Import RelocProgSemanticsArchi RelocProgGlobalenvs.

Import ListNotations.
Local Open Scope error_monad_scope.

Lemma PTree_map_elements: forall A B (f:positive -> A -> B) m,
    let R := (fun p a b => f p a = b) in
    list_forall2
      (fun (i_x : positive * A) (i_y : positive * B) =>
         fst i_x = fst i_y /\ R (fst i_x) (snd i_x) (snd i_y))
      (PTree.elements m) (PTree.elements (PTree.map f m)).
Proof.
  intros.
  apply PTree.elements_canonical_order1;intros.
  - unfold R in *.
    rewrite PTree.gmap.
    rewrite H. simpl. exists (f i x). auto.
  - unfold R in *.
    rewrite PTree.gmap in H.
    unfold option_map in *. destr_in H.
    exists a. inv H. auto.
Qed.

Section WITH_INSTR_SIZE.
  Variable instr_size: instruction -> Z.
  Variable Instr_size: list Instruction -> Z.
(* used in gen_instr_map_refl *)
Lemma rev_id_eliminate_instr_eq: forall i1 i2 id,
    instr_eq i1 i2 ->
    instr_eq (rev_id_eliminate id i1) (rev_id_eliminate id i2).
Proof.
  intros.
  unfold instr_eq in H. destruct H.
    (* i = i1 *)
  subst. left. auto.

  (* i is not well defined *)
  destruct i1;try inv H;destr_in H;subst.
  1-10: try (try destruct H;subst;simpl;unfold instr_eq;auto).

  1-6 :
    try (try destr_in H;destruct H;subst;
         simpl;do 2 destr;
         unfold instr_eq; try rewrite Heqb; auto;
         
         destruct p; unfold instr_eq; try rewrite Heqb; auto).
 
  destruct H. subst. simpl. do 2 destr. unfold instr_eq. auto.
  destruct p; unfold instr_eq; auto.
  destruct H. subst. simpl. do 2 destr. unfold instr_eq. auto.
  destruct p; unfold instr_eq; auto.

  simpl. unfold instr_eq. right. auto.
  
Qed.

Lemma eval_addrmode_match_ge: forall ge1 ge2 a rs (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs),
    RelocProgSemanticsArchi.eval_addrmode ge1 a rs = eval_addrmode ge2 a rs.
Proof.
  unfold eval_addrmode. destruct Archi.ptr64;intros.
  - unfold eval_addrmode64.
    destruct a. f_equal.
    f_equal. destr.
    destruct p. eauto.
  - unfold eval_addrmode32.
    destruct a. f_equal.
    f_equal. destr.
    destruct p. eauto.
Qed.

Lemma exec_load_match_ge: forall sz ge1 ge2 chunk m a rs rd (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs) ,
          exec_load sz ge1 chunk m a rs rd = exec_load sz ge2 chunk m a rs rd.
Proof.
  unfold exec_load.
  intros. erewrite eval_addrmode_match_ge.
  eauto. auto.
Qed.

Lemma exec_store_match_ge: forall sz ge1 ge2 chunk m a rs rd l (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs) ,
          exec_store sz ge1 chunk m a rs rd l = exec_store sz ge2 chunk m a rs rd l.
Proof.
  unfold exec_store.
  intros. erewrite eval_addrmode_match_ge.
  eauto. auto.
Qed.

(* ad-hoc *)
Section PRESERVATION. 
(** Transformation *)
  Variable prog: RelocProgram.program.
  Variable tprog: program.
  
  
  Let ge := RelocProgSemantics1.globalenv instr_size prog.
  Let tge := RelocProgSemantics2.globalenv instr_size Instr_size tprog.
  
  Hypothesis symbol_address_pres: forall id ofs,
    RelocProgGlobalenvs.Genv.symbol_address ge id ofs =
    RelocProgGlobalenvs.Genv.symbol_address tge id ofs.
  Hypothesis find_instr_refl: forall b ofs i,
    Genv.genv_instrs ge b ofs = Some i ->
    exists i1, Genv.genv_instrs tge b ofs = Some i1
          /\ instr_eq i i1.
  Hypothesis find_ext_funct_refl: forall v,
    Genv.find_ext_funct ge v = Genv.find_ext_funct tge v.
  Hypothesis instr_eq_size: forall i1 i2, instr_eq i1 i2 -> instr_size i1 = instr_size i2.
  Hypothesis rev_transl_code_in: forall i c r,
    In i (rev_transl_code instr_size r c) ->
    exists i', In i' c /\ ((exists id, rev_id_eliminate id i' = i) \/ i = i').
  Hypothesis transl_instr_in_code: forall c i id,
    prog.(prog_sectable) ! id = Some (sec_text c) ->
    In i c ->
    exists i' e, translate_instr e i = OK i'.
  Hypothesis senv_refl:
    (Genv.genv_senv ge) = (Genv.genv_senv tge).

  
Lemma exec_instr_refl: forall i rs m,
    exec_instr instr_size ge i rs m = exec_instr instr_size tge i rs m.
Proof.
  destruct i;simpl;auto;intros.
  1-27: try (erewrite symbol_address_pres;eauto).
  1-24: try (erewrite exec_load_match_ge;eauto;eapply symbol_address_pres;eauto).
  1-12: try (erewrite exec_store_match_ge;eauto;eapply symbol_address_pres;eauto).
  do 3 f_equal.
  unfold eval_addrmode32.
  destruct a. f_equal.
  f_equal. destr.
  destruct p. eapply symbol_address_pres;eauto.
  do 3 f_equal.
  unfold eval_addrmode64.
  destruct a. f_equal.
  f_equal. destr.
  destruct p. eapply symbol_address_pres;eauto.
Qed.


Lemma eval_addrmode_refl: forall a rs,
    eval_addrmode ge a rs = eval_addrmode tge a rs.
Proof.
  intros.
  erewrite eval_addrmode_match_ge. eauto.
  apply symbol_address_pres.
Qed. 

  
Lemma step_simulation: forall st1 st2 t,
    step instr_size ge st1 t st2 ->
    step instr_size tge st1 t st2.
Proof.
  intros st1 st2 t STEP.
  inv STEP.
  - unfold Genv.find_instr in H1.
    exploit find_instr_refl;eauto.
    intros (i1 & FIND & MATCHINSTR).
    eapply exec_step_internal;eauto.
    erewrite <- find_ext_funct_refl;eauto.
    exploit instr_eq_size;eauto. intros SIZE.
    unfold instr_eq in MATCHINSTR. destruct MATCHINSTR.
    (* i = i1 *)
    subst. rewrite <- exec_instr_refl. auto.

  (* i is not well defined *)
    destruct i;try inv H3;simpl in H2;destr_in H3.
    (* Pmovzl_rr *)
    + inv H3. simpl.
      admit.
    (* Pmovls_rr *)
    + subst. simpl.
      admit.
    (* Pxorl_rr *)
    + destruct H3;subst.
      simpl.
      admit.
    (* Pxorq_rr r1 <> r2 *)
    + destruct H3;subst.
      destruct H4;subst.
      simpl. auto.
    (* Pxorq_rr *)
    + destruct H3;subst.
      simpl.
      admit.
    (* Pxorq_rr r1 <> r2 *)
    + destruct H3;subst.
      destruct H4;subst.
      simpl. auto.

    (* Pjmp_s *)
    + subst. simpl.
      rewrite <- symbol_address_pres.
      auto.
    (* Pjmp_r *)
    + subst. simpl. auto.
    (* Pcall_s *)
    + subst. simpl.
      rewrite SIZE in *.
      destr_in H2.
      (* rewrite <- symbol_address_pres. *)
      (* auto. *)
    (* Pcall_r *)
    + subst. simpl.
      rewrite SIZE in *.
      destr_in H2.
      
    (* Pmov_rm_a 32 *)
    + destr_in H3.
      destruct H3;subst.
      simpl.
      unfold exec_load in *.
      unfold Mem.loadv in *.
      rewrite <- eval_addrmode_refl.
      destr_in H2.
      destr_in Heqo.
      Transparent Mem.load. 
      assert (Mem.load  Many32 m b0
                        (Ptrofs.unsigned i) = Mem.load Mint32 m b0 (Ptrofs.unsigned i)).
      { unfold Mem.load.
        unfold Mem.valid_access_dec.
        cbn [size_chunk]. cbn [align_chunk].
        destruct (Mem.range_perm_dec m b0 (Ptrofs.unsigned i)
                                     (Ptrofs.unsigned i + 4) Cur Readable).
        destruct (Zdivide_dec 4 (Ptrofs.unsigned i)).
        unfold size_chunk_nat. cbn [size_chunk].
        f_equal. unfold decode_val.
        rewrite Heqb0.
        admit. auto. auto. }
      rewrite <- H3. rewrite Heqo.
      admit.

    (* Pmov_rm_a 64 *)
    + admit.
    (* Pmov_mr_a 32 *)
    + admit.
    (* Pmov_mr_a 64 *)
    + admit.
    (* Pmovsd_fm_a *)
    + admit.
    (* Pmovsd_mf_a *)
    + admit.
    + simpl. rewrite SIZE in *.
      auto.

  (* Pbuiltin instr impossible *)
  - unfold Genv.find_instr in H1.
    simpl in H1. apply gen_code_map_inv in H1.
    destruct H1 as (id & c & P1 & P2 & P3).
    generalize (PTree_map_elements _ (RelocProg.section instruction init_data) (rev_section instr_size (prog_reloctables prog)) (prog_sectable prog)). simpl.
    intros F.
    apply PTree.elements_correct in P2.
    exploit list_forall2_in_right;eauto.
    simpl.
    intros (x1 & In1 & ? &REV1).
    subst. destruct x1. apply PTree.elements_complete in In1.
    simpl in REV1.
    destruct s.  2-3:  simpl in REV1; congruence.
    simpl in REV1. destr_in REV1.
    + inv REV1. apply rev_transl_code_in in P3.
      destruct P3 as (i' & In' & P3').
      assert (i' = Pbuiltin ef args res).
      { destruct P3'.
        destruct H1 as (id & P3').
        destruct i';simpl in P3';repeat destr_in P3';try congruence.
        subst. auto. }
      subst.
      
      eapply transl_instr_in_code in In1;eauto.
      simpl in In1. destruct In1 as (? & ? & ?).
      inv H1.
      
    + inv REV1.
      eapply transl_instr_in_code in In1;eauto.
      destruct In1 as (? & ? & ?).
      inv H1.
      
  - 
    rewrite find_ext_funct_refl in H0.
    eapply exec_step_external;eauto.
    rewrite <- senv_refl. auto.
Admitted.

End PRESERVATION.

End WITH_INSTR_SIZE.
