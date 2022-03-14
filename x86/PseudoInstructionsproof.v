Require Import Smallstep.
Require Import Machregs.
Require Import Asm.
Require Import Integers.
Require Import List.
Require Import ZArith.
Require Import Memtype.
Require Import Memory.
Require Import Archi.
Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Values.
Require Import Conventions1.
Require Import AsmFacts.
Require Import RealAsm PseudoInstructions.
Require Import RealAsmproof.
Require Import AsmRegs.

Definition match_prog (p: Asm.program) (tp: Asm.program) :=
  Linking.match_program (fun _ f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = tp -> match_prog p tp.
Proof.
  intros. subst. eapply Linking.match_transform_program; eauto.
Qed.

Section PRESERVATION.

  Variable instr_size: instruction -> Z.
  Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.
  Hypothesis transf_instr_size : forall i, instr_size i = code_size instr_size (transf_instr i).

  Variable prog tprog: Asm.program.
  Hypothesis TRANSF: Linking.match_program (fun _ f1 f2 => f2 = transf_fundef f1) eq prog tprog.
  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof (Genv.find_symbol_match TRANSF).

  Lemma senv_preserved:
    Senv.equiv ge tge.
  Proof (Genv.senv_match TRANSF).

(*
  Lemma genv_next_preserved:
    Genv.genv_sup tge = Genv.genv_sup ge.
  Proof. apply senv_preserved. Qed.
*)
  Lemma functions_translated:
    forall b f,
      Genv.find_funct_ptr ge b = Some f ->
      Genv.find_funct_ptr tge b = Some (transf_fundef f).
  Proof. apply (Genv.find_funct_ptr_transf TRANSF). Qed.

  Lemma functions_transl:
    forall fb f,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      Genv.find_funct_ptr tge fb = Some (Internal (transf_function f)).
  Proof.
    intros. apply functions_translated in H; eauto.
  Qed.


  Lemma transf_code_size: forall c,
      code_size instr_size c = code_size instr_size (transf_code c).
  Proof.
    intros. induction c.
    - auto.
    - simpl. unfold transf_code. simpl.
      rewrite code_size_app.
      generalize (transf_instr_size a). intro.
      rewrite <- H. simpl. setoid_rewrite <- IHc. lia.
  Qed.

  Lemma public_preserved:
    forall id : ident, Genv.public_symbol (Genv.globalenv tprog) id = Genv.public_symbol (Genv.globalenv prog) id.
  Proof.
    apply senv_preserved.
  Qed.

  Inductive code_at: Z -> code -> code -> Prop :=
  | code_at_nil o c: code_at o c nil
  | code_at_cons o c i c':
      find_instr instr_size o c = Some i ->
      code_at (o + instr_size i) c c' ->
      code_at o c (i::c').

  Lemma code_at_app:
    forall b a c, code_at (code_size instr_size a) (a ++ (b ++ c)) b.
  Proof.
    induction b; intros.
    - constructor.
    - constructor.
      replace (code_size instr_size a0) with (0 + code_size instr_size a0) by lia.
      rewrite find_instr_app; eauto. lia.
      replace (a0 ++ (a::b) ++ c) with ((a0 ++ a::nil) ++ b ++ c).
      replace (code_size instr_size a0 + instr_size a) with (code_size instr_size (a0 ++ a::nil)).
      apply IHb.
      rewrite code_size_app. simpl. lia.
      simpl. rewrite app_ass. simpl. reflexivity.
  Qed.

  Lemma code_at_next:
    forall a i b, code_at (instr_size i) (i :: a ++ b) a.
  Proof.
    intros.
    generalize (code_at_app a (i::nil) b). simpl. auto.
  Qed.

  Lemma code_at_shift:
    forall i a c o,
      code_at (o - code_size instr_size a) c i -> code_at o (a ++ c) i.
  Proof.
    induction i; simpl; intros b c o CA. constructor.
    inv CA. constructor.
    replace o with ((o - code_size instr_size b) + code_size instr_size b) by lia.
    rewrite find_instr_app; eauto. eapply find_instr_pos_positive; eauto.
    apply IHi.
    replace (o + instr_size a - code_size instr_size b) with (o - code_size instr_size b + instr_size a). auto. lia.
  Qed.

  Lemma find_instr_transl:
    forall c o i,
      find_instr instr_size o c = Some i ->
      code_at o (transf_code c) (transf_instr i).
  Proof.
    induction c; simpl; intros; eauto. easy.
    repeat destr_in H.
    - unfold transf_code. simpl.
      destruct transf_instr eqn:TI.
      apply (f_equal (code_size instr_size)) in TI. rewrite <- transf_instr_size in TI. simpl in TI.
      generalize (instr_size_bound i); lia.
      simpl. constructor. simpl. auto.
      simpl. apply code_at_next.
    - specialize (IHc _ _ H1).
      unfold transf_code. simpl. fold (transf_code c).
      eapply code_at_shift. rewrite <- transf_instr_size; auto.
  Qed.

  Definition id_instr (i: instruction) : bool :=
    match i with
    | Pallocframe _ _ _
    | Pfreeframe _ _ _ => false
    | _ => true
    end.

  Hypothesis WF: wf_asm_prog instr_size ge.
  Hypothesis prog_no_rsp: asm_prog_no_rsp instr_size ge.

  Lemma exec_instr_Plea:
    forall ge f r a (rs: regset) m,
      exec_instr instr_size ge f (Plea r a) rs m =
      Next (nextinstr (Ptrofs.repr (instr_size (Plea r a))) (rs # r <- (eval_addrmode ge a rs))) m.
  Proof.
    unfold Plea, eval_addrmode.
    intros. destr.
  Qed.

  Lemma ptrofs_eq_unsigned: forall a b,
      Ptrofs.unsigned a = Ptrofs.unsigned b -> a = b.
  Proof.
    intros.
    rewrite <- (Ptrofs.repr_unsigned a).
    rewrite <- (Ptrofs.repr_unsigned b).
    rewrite H. reflexivity.
  Qed.

  Lemma eval_addrmode_offset_ptr:
    forall (rs: regset) (r: ireg) z (RSPPTR: exists b o, rs r = Vptr b o),
      eval_addrmode (Genv.globalenv tprog) (linear_addr r z) rs = Val.offset_ptr (rs r) (Ptrofs.repr z).
  Proof.
    unfold eval_addrmode. intros.
    destr.
    ++ unfold eval_addrmode64, linear_addr.
       destruct (RSPPTR) as (bb & o & RSPPTR'). rewrite RSPPTR'. simpl. rewrite Heqb.
       f_equal. rewrite Int64.add_zero_l. f_equal.
       erewrite Ptrofs.agree64_of_int_eq. eauto. apply Ptrofs.agree64_repr; auto.
    ++ unfold eval_addrmode32, linear_addr.
       destruct (RSPPTR) as (bb & o & RSPPTR'). rewrite RSPPTR'. simpl. rewrite Heqb.
       f_equal. rewrite Int.add_zero_l. f_equal.
       erewrite Ptrofs.agree32_of_int_eq. eauto. apply Ptrofs.agree32_repr; auto.
  Qed.

  Lemma id_instr_transf:
    forall i,
      id_instr i = true ->
      transf_instr i = i :: nil.
  Proof.
    destruct i; simpl; intros; congruence.
  Qed.  

  Lemma eval_addrmode64_senv_equiv:
    forall (ge1 ge2: genv) (EQ: Senv.equiv ge1 ge2) a rs,
      eval_addrmode64 ge1 a rs = eval_addrmode64 ge2 a rs.
  Proof.
    intros.
    unfold eval_addrmode64.
    destr. unfold Genv.symbol_address.
    destruct const. auto. destruct p.
    destruct EQ as (A & B & C). simpl in *. rewrite A. auto.
  Qed.

  Lemma eval_addrmode32_senv_equiv:
    forall (ge1 ge2: genv) (EQ: Senv.equiv ge1 ge2) a rs,
      eval_addrmode32 ge1 a rs = eval_addrmode32 ge2 a rs.
  Proof.
    intros.
    unfold eval_addrmode32.
    destr. unfold Genv.symbol_address.
    destruct const. auto. destruct p.
    destruct EQ as (A & B & C). simpl in *. rewrite A. auto.
  Qed.

  Lemma eval_addrmode_senv_equiv:
    forall (ge1 ge2: genv) (EQ: Senv.equiv ge1 ge2) a rs,
      eval_addrmode ge1 a rs = eval_addrmode ge2 a rs.
  Proof.
    unfold eval_addrmode.
    intros.
    destr; eauto using eval_addrmode64_senv_equiv, eval_addrmode32_senv_equiv.
  Qed.

  Lemma exec_load_senv_equiv:
    forall (ge1 ge2: genv) (EQ: Senv.equiv ge1 ge2) chunk m a rs r,
      exec_load ge1 chunk m a rs r =
      exec_load ge2 chunk m a rs r .
  Proof.
    unfold exec_load.
    intros; erewrite eval_addrmode_senv_equiv; eauto.
  Qed.

  Lemma exec_store_senv_equiv:
    forall (ge1 ge2: genv) (EQ: Senv.equiv ge1 ge2) chunk m a rs r lr,
      exec_store ge1 chunk m a rs r lr=
      exec_store ge2 chunk m a rs r lr.
  Proof.
    unfold exec_store.
    intros; erewrite eval_addrmode_senv_equiv; eauto.
  Qed.

  Lemma label_pos_app:
    forall a b l o,
      ~ In (Plabel l) a ->
      label_pos instr_size l o (a ++ b) = label_pos instr_size l (o + code_size instr_size a) b.
  Proof.
    induction a; simpl; intros; eauto.
    rewrite Z.add_0_r; auto.
    destr. destruct a; simpl in Heqb0; try congruence. destr_in Heqb0.
    rewrite IHa; auto. f_equal. lia.
  Qed.

  Lemma label_pos_transf:
    forall c l o,
      label_pos instr_size l o c =
      label_pos instr_size l o (transf_code c).
  Proof.
    induction c; simpl; intros; eauto.
    unfold transf_code. simpl. fold (transf_code c).
    destr.
    - destruct a; simpl in Heqb; try congruence.
      destr_in Heqb. subst. simpl. rewrite peq_true. reflexivity.
    - rewrite label_pos_app.
      rewrite <- transf_instr_size. auto.
      intro IN.
      destruct a; try now (simpl in *; unfold Padd, Psub, Plea in *; simpl in *; repeat destr_in IN; try intuition congruence).
      simpl in *. destr_in Heqb.
      simpl in *. unfold Padd, Psub, Plea in *. simpl in *. repeat destr_in IN. intuition congruence.
      unfold Padd, Psub, Plea in *. repeat destr_in H. intuition congruence. inv H0. inv H. auto. inv H.
      unfold Padd, Psub, Plea in *. repeat destr_in H. congruence. inv H0. inv H. auto.
  Qed.

  Lemma goto_label_senv_equiv:
    forall f l rs m rs' m',
      goto_label instr_size ge f l rs m = Next rs' m' ->
      goto_label instr_size tge (transf_function f) l rs m = Next rs' m'.
  Proof.
    unfold goto_label.
    intros.
    simpl; rewrite <- label_pos_transf. destr.
    destr.
    destr_in H. inv H. erewrite functions_translated; eauto.
  Qed.
(*
  Lemma goto_ofs_senv_equiv:
    forall sz ofs rs m rs' m',
      goto_ofs ge sz ofs rs m = Next rs' m' ->
      goto_ofs tge sz ofs rs m = Next rs' m'.
  Proof.
    unfold goto_ofs.
    intros.
    destr.
    destr_in H. inv H. erewrite functions_translated; eauto.
  Qed.
*)
  Lemma functions_only_translated:
    forall b,
      Genv.find_funct_ptr ge b = None ->
      Genv.find_funct_ptr tge b = None.
  Proof.
    destruct TRANSF as (A & B & C).
    unfold Genv.find_funct_ptr, Genv.find_def.
    unfold ge, tge, Genv.globalenv.
    assert (REC:   forall b : block,
               match NMap.get _ b (Genv.genv_defs (Genv.empty_genv Asm.fundef unit (prog_public prog))) with
               | Some (Gfun f) => Some f
               | Some (Gvar _) => None
               | None => None
               end = None ->
               match NMap.get _ b (Genv.genv_defs (Genv.empty_genv Asm.fundef unit (prog_public tprog))) with
               | Some (Gfun f) => Some f
               | Some (Gvar _) => None
               | None => None
               end = None).
    {
      simpl. intros b. auto.
    }
(*    assert (NEXT: Genv.genv_next (Genv.empty_genv Asm.fundef unit (prog_public prog)) =
                  Genv.genv_next (Genv.empty_genv Asm.fundef unit (prog_public tprog))).
    {
      reflexivity.
    } *)
    revert REC.
    generalize (Genv.empty_genv Asm.fundef unit (prog_public prog)) (Genv.empty_genv Asm.fundef unit (prog_public tprog)).
    revert A.
    simpl.
    unfold Asm.fundef.
    generalize (@prog_defs (fundef function) unit prog) (@prog_defs (fundef function) unit tprog).
    induction 1; simpl. eauto.
    intros t t0 REC. apply IHA.
    simpl. intro b. inv H. inv H1.
    +
    rewrite ! NMap.gsspec. rewrite H0.
    destruct (NMap.elt_eq b (Global (fst b1))). inv H3. congruence. auto.
    +
    rewrite ! NMap.gsspec. rewrite H0.
    destruct (NMap.elt_eq b (Global (fst b1))). inv H3. congruence. auto.
  Qed.

  Lemma goto_label_senv_equiv':
    forall f l rs m,
      goto_label instr_size ge f l rs m = Stuck ->
      goto_label instr_size tge (transf_function f) l rs m = Stuck.
  Proof.
    unfold goto_label.
    intros.
    simpl; rewrite <- label_pos_transf. destr.
    destr.
    destr_in H. erewrite functions_only_translated; eauto.
  Qed.
(*
  Lemma goto_ofs_senv_equiv':
    forall sz ofs rs m,
      goto_ofs ge sz ofs rs m = Stuck ->
      goto_ofs tge sz ofs rs m = Stuck.
  Proof.
    unfold goto_ofs.
    intros.
    destr.
    destr_in H. erewrite functions_only_translated; eauto.
  Qed.
*)
  Lemma goto_label_eq:
    forall f l rs m,
      goto_label instr_size ge f l rs m =
      goto_label instr_size tge (transf_function f) l rs m.
  Proof.
    intros.
    destruct (goto_label instr_size ge f l rs m) eqn:GL.
    symmetry; eapply goto_label_senv_equiv; eauto.
    symmetry; eapply goto_label_senv_equiv'; eauto.
  Qed.
(*
  Lemma goto_ofs_eq:
    forall sz ofs rs m,
      goto_ofs ge sz ofs rs m =
      goto_ofs tge sz ofs rs m.
  Proof.
    intros.
    destruct (goto_ofs ge sz ofs rs m) eqn:GL.
    symmetry; eapply goto_ofs_senv_equiv; eauto.
    symmetry; eapply goto_ofs_senv_equiv'; eauto.
  Qed.

  Lemma eval_ros_eq:
    forall ros rs,
      eval_ros ge ros rs = eval_ros tge ros rs.
  Proof.
    unfold eval_ros.
    intros. destr.
    unfold Genv.symbol_address.
    destruct senv_preserved as (A & B & C & D). simpl in *; rewrite B. auto.
  Qed.
  *)

  Lemma exec_instr_senv_equiv:
    forall f i rs m (ID : id_instr i = true),
      exec_instr instr_size ge f i rs m = exec_instr instr_size tge (transf_function f) i rs m.
  Proof.
    generalize senv_preserved as EQ.
    destruct i; simpl; intros; eauto; try (erewrite exec_load_senv_equiv; eauto); try (erewrite exec_store_senv_equiv; eauto).
    - unfold Genv.symbol_address.
    destruct EQ as (A & B & C).  simpl in *. rewrite A. auto.
    - erewrite eval_addrmode32_senv_equiv; eauto.
    - erewrite eval_addrmode64_senv_equiv; eauto.
    - eapply goto_label_eq; eauto.
    - unfold Genv.find_funct.
      unfold Genv.symbol_address.
      rewrite symbols_preserved.
      destruct (Genv.find_symbol ge symb); auto. rewrite pred_dec_true; auto.
      destr. erewrite functions_translated; eauto. erewrite functions_only_translated; eauto.
    - unfold Genv.find_funct. destruct (rs r); auto.
      destruct (Ptrofs.eq_dec i Ptrofs.zero); auto.
      destr. erewrite functions_translated; eauto. erewrite functions_only_translated; eauto.
    -
    destr. destr. eapply goto_label_eq; eauto.
    -
    destr. destr. destr. destr. eapply goto_label_eq; eauto.
    -
    destr. destr. eapply goto_label_eq; eauto.
    -
    destr. f_equal. f_equal. f_equal.       unfold Genv.symbol_address.
      rewrite symbols_preserved. auto.
Qed.

  Lemma pseudo_instructions_step:
    forall s1 t s2
           (STEP :step instr_size (Genv.globalenv prog) s1 t s2)
           (INV: real_asm_inv s1),
      plus (step instr_size ) (Genv.globalenv tprog) s1 t s2.
  Proof.
    intros s1 t s2 STEP INV.
    inv STEP.
    - exploit functions_transl. eauto. intros FFP.
      exploit find_instr_transl; eauto. intro CA.
      destruct (id_instr i) eqn:ID; [| destruct i; simpl in ID; try congruence].
      + pose proof (id_instr_transf _ ID) as NORMAL.
        rewrite NORMAL in CA. inv CA.  inv H8. eapply plus_one.
        econstructor. eauto. eapply FFP. eauto.
        erewrite <- exec_instr_senv_equiv; eauto.
      + (* Pallocframe -> Padd;Psub;Pstoreptr*)
        generalize (transf_instr_size (Pallocframe sz ofs_ra ofs_link)). intro PSIZE.
        simpl in PSIZE.
        generalize (instr_size_bound (Pallocframe sz ofs_ra ofs_link)). intro PSIZEB.
        subst; simpl in *. inv H2. inv CA. inv H8. inv H10.
        eapply plus_three.
        (*Padd*)
        econstructor. eauto. eapply FFP. eauto.
        unfold Padd. apply exec_instr_Plea.
        (*Psub*)
        econstructor.
        rewrite Asmgenproof0.nextinstr_pc. repeat rewrite Pregmap.gso by congruence.
        rewrite H. simpl. eauto. eauto.
        erewrite wf_asm_pc_repr'; eauto.
        rewrite PSIZE.
        generalize (instr_size_bound (Psub RSP RSP (align sz 8 - size_chunk Mptr))).
        unfold Padd.
        generalize (instr_size_bound (Plea RAX (linear_addr RSP (size_chunk Mptr)))).
        generalize (instr_size_bound (Pstoreptr (linear_addr RSP (Ptrofs.unsigned ofs_link)) RAX)).
        lia.
        unfold Psub, Padd. rewrite exec_instr_Plea. f_equal.
        destr_in H4. inv H4.
        (*Pstoreptr*)
        generalize (instr_size_bound (Plea RAX (linear_addr RSP (size_chunk Mptr)))). intro SPlea1.
        generalize (instr_size_bound (Plea RSP (linear_addr RSP (-(align sz 8 - size_chunk Mptr))))).
        intro SPlea2.
        generalize (instr_size_bound (Pstoreptr (linear_addr RSP (Ptrofs.unsigned ofs_link))RAX)). intro SPstore.
        assert (CSIZE: 0 <= code_size instr_size (transf_code (fn_code f)) <= Ptrofs.max_unsigned).
        {
          apply WF in H0. exploit wf_asm_code_bounded; eauto. intro.
          rewrite <- transf_code_size. auto.
        }
        econstructor. simpl_regs. rewrite H. simpl. eauto. eauto.
        erewrite code_bounded_repr; eauto.
        erewrite code_bounded_repr; eauto.
        unfold Padd. lia.
        erewrite code_bounded_repr; eauto.
        unfold Padd. lia.
        unfold Psub, Padd. lia.
        unfold Psub, Padd, Pstoreptr in *.
        destruct ptr64 eqn:PTR64.
        * (*64bit storeptr*)
          simpl. unfold exec_store.  unfold eval_addrmode. rewrite PTR64.
          unfold eval_addrmode64. simpl.
          simpl_regs.
          inv INV. inv RSPPTR. destruct H2. simpl in H2. rewrite H2. rewrite H2 in Heqo.
          unfold Val.offset_ptr, Mptr in *. simpl in *.
          repeat (rewrite PTR64 in *; simpl in *).
          assert (
              (Ptrofs.unsigned
              (Ptrofs.add (Ptrofs.add x (Ptrofs.neg (Ptrofs.sub (Ptrofs.repr (align sz 8)) (Ptrofs.repr 8)))) ofs_link))
                =
(Ptrofs.unsigned
         (Ptrofs.add (Ptrofs.add x (Ptrofs.of_int64 (Int64.add Int64.zero (Int64.repr (- (align sz 8 - 8))))))
            (Ptrofs.of_int64 (Int64.add Int64.zero (Int64.repr (Ptrofs.unsigned ofs_link))))))
            ).
                  {
                    exploit wf_allocframe_repr; eauto.
                    unfold Mptr. rewrite PTR64. simpl. intro.
                    f_equal. f_equal. f_equal. unfold Ptrofs.sub. rewrite Ptrofs.unsigned_repr.
           (* Ptrofs.neg (Ptrofs.sub (Ptrofs.repr (align sz 8)) (Ptrofs.repr 8)) =
             Ptrofs.of_int64 (Int64.add Int64.zero (Int64.repr (- (align sz 8 - 8))))*)
                    rewrite Int64.add_zero_l.
                    rewrite Ptrofs.unsigned_repr; auto. 2: vm_compute; split; congruence.
                    unfold Ptrofs.of_int64.
                    unfold Ptrofs.neg. simpl.
                    rewrite Ptrofs.unsigned_repr.
                    apply Ptrofs.eqm_repr_eq.
                    rewrite Ptrofs.unsigned_repr.
                    apply Int64.eqm_unsigned_repr_r.
                    apply Int64.eqm_refl.
                    assert (Int64.max_unsigned = Ptrofs.max_unsigned).
                    unfold Int64.max_unsigned. unfold Ptrofs.max_unsigned.
                    rewrite Ptrofs.modulus_eq64. auto. auto. rewrite <- H5.
                    apply Int64.unsigned_range_2.
                    lia. lia.
                    + rewrite Int64.add_zero_l.
                    unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr.
                    rewrite Ptrofs.repr_unsigned. auto.
                    assert (Int64.max_unsigned = Ptrofs.max_unsigned).
                    unfold Int64.max_unsigned. unfold Ptrofs.max_unsigned.
                    rewrite Ptrofs.modulus_eq64. auto. auto.
                    apply Ptrofs.unsigned_range_2.
                  }
                  auto.
         assert ( (Vptr bstack (Ptrofs.add x (Ptrofs.repr 8)))=
                (Vptr bstack (Ptrofs.add x (Ptrofs.of_int64 (Int64.add Int64.zero (Int64.repr 8)))))
           ). auto.
                  rewrite H4,H5 in Heqo.
                  destr_in Heqo. rewrite H10.
                  f_equal.
        apply Axioms.extensionality. intro r.
        destruct (preg_eq r PC).
        ++
          subst. simpl_regs. rewrite H. simpl. f_equal.
          generalize (wf_asm_pc_repr' instr_size instr_size_bound _ (WF _ _ H0) _ _ H1). intro REPR.
          apply ptrofs_eq_unsigned.
          rewrite Ptrofs.add_assoc. rewrite (Ptrofs.add_unsigned (Ptrofs.repr _)).
          rewrite Ptrofs.add_assoc. rewrite (Ptrofs.add_unsigned (Ptrofs.repr _)).
          erewrite Ptrofs.unsigned_repr. 2: lia.
          erewrite Ptrofs.unsigned_repr. unfold Psub,Padd in PSIZE.
          erewrite Ptrofs.unsigned_repr. 2: lia.
          erewrite Ptrofs.unsigned_repr. 2: lia.
          repeat rewrite ! REPR.
          rewrite PSIZE. lia. lia. lia.
          rewrite Ptrofs.unsigned_repr. 2: lia.
          rewrite Ptrofs.unsigned_repr. 2: lia.
          lia.
        ++ unfold nextinstr_nf.
          simpl_regs. regs_eq. simpl_regs. regs_eq. simpl_regs. regs_eq.
          f_equal. f_equal.  symmetry.
           exploit wf_allocframe_repr; eauto.
           unfold Mptr. rewrite PTR64. simpl. intro.
           unfold Ptrofs.sub. rewrite Ptrofs.unsigned_repr.
           rewrite Int64.add_zero_l.
           rewrite Ptrofs.unsigned_repr; auto. 2: vm_compute; split; congruence.
           unfold Ptrofs.of_int64.
           unfold Ptrofs.neg. simpl.
           rewrite Ptrofs.unsigned_repr.
           apply Ptrofs.eqm_repr_eq.
           rewrite Ptrofs.unsigned_repr.
           apply Int64.eqm_unsigned_repr_r.
           apply Int64.eqm_refl.
           assert (Int64.max_unsigned = Ptrofs.max_unsigned).
           unfold Int64.max_unsigned. unfold Ptrofs.max_unsigned.
           rewrite Ptrofs.modulus_eq64. auto. auto. rewrite <- H13.
           apply Int64.unsigned_range_2.
           lia. lia.
        * (*32bit storeptr*)
          simpl. unfold exec_store.  unfold eval_addrmode. rewrite PTR64.
          unfold eval_addrmode32. simpl.
          simpl_regs.
          inv INV. inv RSPPTR. destruct H2. simpl in H2. rewrite H2. rewrite H2 in Heqo.
          unfold Val.offset_ptr, Mptr in *. simpl in *.
          repeat (rewrite PTR64 in *; simpl in *).
          assert (
              (Ptrofs.unsigned
              (Ptrofs.add (Ptrofs.add x (Ptrofs.neg (Ptrofs.sub (Ptrofs.repr (align sz 8)) (Ptrofs.repr 4)))) ofs_link))
                =
(Ptrofs.unsigned
         (Ptrofs.add (Ptrofs.add x (Ptrofs.of_int (Int.add Int.zero (Int.repr (- (align sz 8 - 4))))))
            (Ptrofs.of_int (Int.add Int.zero (Int.repr (Ptrofs.unsigned ofs_link))))))
            ).
                  {
                    f_equal. f_equal. f_equal.
                    exploit wf_allocframe_repr; eauto.
                    unfold Mptr. rewrite PTR64. simpl. intro.
                    unfold Ptrofs.sub. rewrite Ptrofs.unsigned_repr.
                    rewrite Int.add_zero_l.
                    rewrite Ptrofs.unsigned_repr; auto. 2: vm_compute; split; congruence.
                    unfold Ptrofs.of_int.
                    unfold Ptrofs.neg. simpl.
                    rewrite Ptrofs.unsigned_repr.
                    apply Ptrofs.eqm_repr_eq.
                    rewrite Ptrofs.unsigned_repr.
                    exploit Ptrofs.eqm32. auto. intro. apply H5.
                    apply Int.eqm_unsigned_repr_r.
                    apply Int.eqm_refl.
                    assert (Int.max_unsigned = Ptrofs.max_unsigned).
                    unfold Int.max_unsigned. unfold Ptrofs.max_unsigned.
                    rewrite Ptrofs.modulus_eq32. auto. auto. rewrite <- H5.
                    apply Int.unsigned_range_2. lia. lia.
                    rewrite Int.add_zero_l.
                    unfold Ptrofs.of_int. rewrite Int.unsigned_repr.
                    rewrite Ptrofs.repr_unsigned. auto.
                    assert (Int.max_unsigned = Ptrofs.max_unsigned).
                    unfold Int.max_unsigned. unfold Ptrofs.max_unsigned.
                    rewrite Ptrofs.modulus_eq32. auto. auto. rewrite H4.
                    apply Ptrofs.unsigned_range_2.
                  }
                  auto.
         assert ( (Vptr bstack (Ptrofs.add x (Ptrofs.repr 4)))=
                (Vptr bstack (Ptrofs.add x (Ptrofs.of_int (Int.add Int.zero (Int.repr 4)))))
           ). auto.
                  rewrite H4,H5 in Heqo.
                  destr_in Heqo. rewrite H10.
                  f_equal.
        apply Axioms.extensionality. intro r.
        destruct (preg_eq r PC).
        ++
          subst. simpl_regs. rewrite H. simpl. f_equal.
          generalize (wf_asm_pc_repr' instr_size instr_size_bound _ (WF _ _ H0) _ _ H1). intro REPR.
          apply ptrofs_eq_unsigned.
          rewrite Ptrofs.add_assoc. rewrite (Ptrofs.add_unsigned (Ptrofs.repr _)).
          rewrite Ptrofs.add_assoc. rewrite (Ptrofs.add_unsigned (Ptrofs.repr _)).
          erewrite Ptrofs.unsigned_repr. 2: lia.
          erewrite Ptrofs.unsigned_repr. unfold Psub,Padd in PSIZE.
          erewrite Ptrofs.unsigned_repr. 2: lia.
          erewrite Ptrofs.unsigned_repr. 2: lia.
          repeat rewrite ! REPR.
          rewrite PSIZE. lia. lia. lia.
          rewrite Ptrofs.unsigned_repr. 2: lia.
          rewrite Ptrofs.unsigned_repr. 2: lia.
          lia.
        ++ unfold nextinstr_nf.
          simpl_regs. regs_eq. simpl_regs. regs_eq. simpl_regs. regs_eq.
          f_equal. f_equal.  symmetry.
           exploit wf_allocframe_repr; eauto.
           unfold Mptr. rewrite PTR64. simpl. intro.
           unfold Ptrofs.sub. rewrite Ptrofs.unsigned_repr.
           rewrite Int.add_zero_l.
           rewrite Ptrofs.unsigned_repr; auto. 2: vm_compute; split; congruence.
           unfold Ptrofs.of_int.
           unfold Ptrofs.neg. simpl.
           rewrite Ptrofs.unsigned_repr.
           apply Ptrofs.eqm_repr_eq.
           rewrite Ptrofs.unsigned_repr.
           exploit Ptrofs.eqm32. auto. intro. apply H13.
           apply Int.eqm_unsigned_repr_r.
           apply Int.eqm_refl.
           assert (Int.max_unsigned = Ptrofs.max_unsigned).
           unfold Int.max_unsigned. unfold Ptrofs.max_unsigned.
           rewrite Ptrofs.modulus_eq32. auto. auto. rewrite <- H13.
           apply Int.unsigned_range_2. lia. lia.
        * traceEq.
      + (*Pfreeframe*)
        subst; simpl in *. inv H2. inv CA. inv H7.
        eapply plus_one.
        econstructor. eauto. eapply FFP. eauto.
        unfold Padd. rewrite exec_instr_Plea.
        f_equal. apply Axioms.extensionality. intro r.
        generalize (transf_instr_size (Pfreeframe sz ofs_ra ofs_link)). intro. simpl in H2.
        rewrite H2. unfold Padd.
        regs_eq. auto.
        rewrite eval_addrmode_offset_ptr.
        2: inv INV; edestruct RSPPTR as ( bb & oo & EQ & _); eauto.
        f_equal.
        eapply wf_freeframe_repr; eauto.
    - exploit functions_transl. eauto. intros FFP.
      exploit find_instr_transl; eauto. intro CA.
      apply plus_one.
      inv CA. inv H9.
      eapply exec_step_builtin; eauto.
      eapply eval_builtin_args_preserved. apply senv_preserved. eauto.
      eapply external_call_symbols_preserved. apply senv_preserved. eauto.
    - exploit functions_translated. eauto. intros FFP.
      apply plus_one.
      eapply exec_step_external; eauto.
      eapply external_call_symbols_preserved. apply senv_preserved. eauto.
Qed.

  Theorem pseudo_instructions_correct:
    forward_simulation (RealAsm.semantics instr_size prog) (RealAsm.semantics instr_size tprog).
  Proof.
    eapply forward_simulation_plus with (match_states := fun s1 s2 : Asm.state => s1 = s2 /\ real_asm_inv s1).
    - simpl. apply public_preserved.
    - simpl; intros s1 IS1. inversion IS1.
      eapply Genv.init_mem_transf in H; eauto. eexists; split;[|split]; eauto.
      rewrite <- H3.
      econstructor; eauto.
      rewrite <- symbols_preserved in H2. fold tge.
      erewrite <- (Linking.match_program_main) in H2 by eauto. auto.
      eapply real_initial_inv; eauto. rewrite H3. eauto.
    - simpl; intros s1 s2 r (MS & INV) FS. subst. auto.
    - simpl. intros s1 t s2 STEP s1' (MS & INV). subst.
      eexists; split; [|split]; eauto.
      eapply pseudo_instructions_step; eauto.
      eapply real_asm_inv_inv; eauto.
  Qed.

End PRESERVATION.
