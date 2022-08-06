(* *******************  *)
(* Author: Jinhua Wu    *)
(* Date:   Jul 26th     *)
(* *******************  *)

Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgramBytes Globalenvs.
Require Import Stacklayout Conventions.
Require Import Linking Errors.
Require Import EncDecRet RelocBingen RelocBinDecode.
Require Import RelocProgSemantics RelocProgSemantics1.
Require Import TranslateInstr RelocProgSemantics2.

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

Lemma list_forall2_Forall2: forall A B (P: A -> B -> Prop) l1 l2,
    list_forall2 P l1 l2 <->
    Forall2 P l1 l2.
Proof.
  induction l1;intros.
  split;intros. inv H. auto.
  inv H. constructor.
  split;intros.
  inv H. constructor. auto. apply IHl1. auto.
  inv H. constructor. auto. apply IHl1. auto.
Qed.

Lemma list_forall2_app_inv_l: forall A B (P: A -> B -> Prop) l1 l2 l3,
    list_forall2 P (l1++l2) l3 ->
    exists l4 l5, l3 = l4 ++ l5 /\ list_forall2 P l1 l4 /\ list_forall2 P l2 l5.
  intros.
  apply list_forall2_Forall2 in H.
  exploit Forall2_app_inv_l;eauto. intros (l1' & l2' & ? & ? & ?).
  eexists. eexists. split;eauto.
  split;apply list_forall2_Forall2;auto.
Qed.

  
Section WITH_INSTR_SIZE.

Variable instr_size : instruction -> Z.
Variable Instr_size : list Instruction -> Z.

Hypothesis translate_instr_size: forall i e l l',
      translate_instr e i = OK l ->
      Instr_size (l ++ l') = instr_size i.

Hypothesis instr_eq_size: forall i1 i2, instr_eq i1 i2 -> instr_size i1 = instr_size i2.

Definition match_prog (p: RelocProgram.program) (tp: program) :=
  transf_program instr_size p = OK tp.


Lemma decode_instrs_bytes_app': forall l l' l1,
    decode_instrs_bytes l [] = OK l' ->
    decode_instrs_bytes l l1 = OK (l1 ++ l').
Admitted.
  
Lemma decode_instrs_bytes_app: forall l1 l2 l3,
    decode_instrs_bytes l1 [] = OK l3 ->
    decode_instrs_bytes (l1 ++ l2) [] = 
    decode_instrs_bytes l2 l3.
Admitted.

  
Lemma encode_into_byte_consistency: forall l bl,
    fold_left concat_byte l (OK []) = OK bl ->
    decode_instrs_bytes  bl [] = OK l.
Admitted.

Lemma transl_code_rev: forall n l l' ofs reloctbl reloctbl',
    length l = n ->
    fold_left (acc_instrs instr_size) l (OK ([],0,reloctbl)) = OK (l',ofs,reloctbl') ->
    ofs = code_size instr_size l /\ exists reloctbl1, reloctbl = reloctbl1 ++ reloctbl'.
Admitted.

Lemma decode_instr_len: forall l l' e i,
    decode_instr e l = OK (i,l') ->
    exists a l1, l = a :: l1 ++ l' /\ forall l2, decode_instr e (a::l1 ++ l2) = OK (i,l2).
Admitted.       


Definition decode_instrs_app_prop n :=
  forall l1 l1' l2 genl reloctbl1 reloctbl2,
    n = length l1 ->
    decode_instrs instr_size Instr_size l1 (genl,reloctbl1++reloctbl2) = OK (l1', reloctbl2) ->
    decode_instrs instr_size Instr_size (l1 ++ l2) (genl,reloctbl1++reloctbl2) = decode_instrs instr_size Instr_size l2 (l1',reloctbl2).

(* TODO: we should return the remaining Instruction list in decode_instrs function, i.e. decode_instrs xxx = OK (decode_result, remaining_reloctbl, remaining_Instruction_list). And we should ensure that decode_code always return empty remaining_Instruction_list*)
Lemma decode_instrs_app: forall n,
    decode_instrs_app_prop n.
  intros n.
  eapply Nat.strong_right_induction with (z:=O);eauto;try lia.
  unfold Morphisms.Proper.
  unfold Morphisms.respectful.
  intros. subst. split;auto.
  intros.
  unfold decode_instrs_app_prop.
  intros l1 l1' l2 genl reloctbl1 reloctbl2 LEN DEC.
  rewrite decode_instrs_eq in DEC.
  simpl in DEC.
  destruct l1.
  - inv DEC. repeat rewrite H3. simpl. auto.
  - destr_in DEC.
    + monadInv DEC. destr_in EQ0.
      exploit decode_instr_len;eauto.
      intros (a & l3 & P1 & P2). inv P1.
      exploit (H0 (length x0)).
      lia.
      simpl. rewrite app_length. lia.
      eauto.
      change ((genl ++ [x], [])) with ((genl ++ [x], @app relocentry [] [])) in EQ0.
      erewrite EQ0. f_equal. f_equal.
      destruct reloctbl1;destruct reloctbl2;simpl in Heql;try congruence.
      intros IH.
      cbn [app].
      rewrite decode_instrs_eq. rewrite <- app_assoc.
      rewrite P2. cbn [bind2].
      destr. rewrite IH. destruct reloctbl1;destruct reloctbl2;simpl in Heql;try congruence.
      simpl in n0. repeat rewrite app_length in n0.
      lia.
      
    +
      destr_in DEC.
      * 
      monadInv DEC.
      destr_in EQ0.
      exploit decode_instr_len;eauto.
      intros (a & l3 & P1 & P2). inv P1.
      cbn [app].
      erewrite decode_instrs_eq. rewrite <- app_assoc.
      rewrite P2.  cbn [bind2].
      destr. destr.
            
      exploit (H0 (length x0)).
      lia.
      simpl. rewrite app_length. lia.
      eauto.

      (*** 2022.8.7  *)
      
      change ((genl ++ [x], [])) with ((genl ++ [x], @app relocentry [] [])) in EQ0.
      erewrite EQ0. f_equal. f_equal.
      destruct reloctbl1;destruct reloctbl2;simpl in Heql;try congruence.
      intros IH.
      cbn [app].
      rewrite decode_instrs_eq. rewrite <- app_assoc.
      rewrite P2. cbn [bind2].
      destr. rewrite IH. destruct reloctbl1;destruct reloctbl2;simpl in Heql;try congruence.
      simpl in n0. repeat rewrite app_length in n0.
      lia.

      
    decode_instrs instr_size Instr_size l1 (genl,reloctbl1++reloctbl2) = OK (l1', reloctbl2) ->
    decode_instrs instr_size Instr_size (l1 ++ l2) (genl,reloctbl1++reloctbl2) = decode_instrs instr_size Instr_size l2 (l1',reloctbl2).
Proof.
  
  induction l1';intros.
  - rewrite decode_instrs_eq in H.
    destr_in H.
    + subst. inv H. simpl. repeat rewrite H2.
      auto.
    + subst. destr_in H.
      *
        Nat.strong_right_induction
        monadInv H. destr_in EQ0.
        rewrite decode_instrs_eq.
        cbn [app].
        exploit decode_instr_len;eauto.
        intros (a & l1 & P1 & P2). inv P1.
        rewrite <- app_assoc.
        erewrite P2. cbn [bind2].
        destr.
        --
    simpl in *. inv H.
    destruct l2.
    + rewrite H2. rewrite H2. auto.
    + rewrite H2. rewrite H2. auto.
  - repeat rewrite decode_instrs_eq in *.
    cbn [app] in *.
    unfold decode_instrs in H. unfold decode_instrs_func in H.
    
  induction fuel1;intros.
  - simpl in H1. destruct l1.
    + destruct fuel2;destruct l2.
      * simpl. auto.
      * simpl. auto.
      * inv H1. simpl. rewrite H4. rewrite H4. auto.
      * inv H1. rewrite H4. rewrite H4.
        auto.
    + inv H1.

  - simpl.
    cbn [decode_instrs] in H1.
    destruct l1.
    + inv H1. simpl. rewrite H4. rewrite H4.
      destruct l2;auto.
      * destruct fuel2;simpl;auto.
      * destruct reloctbl2.
        ++ destruct fuel2.
           -- simpl in H. lia.
           -- cbn [decode_instrs].
              destruct decode_instr eqn:DES;auto.
              destruct p. apply decode_instr_len in DES.
              destruct DES as (a & l2' & ? & UNUSE).
              simpl. eapply decode_instrs_fuel;auto.
              rewrite H1 in H. simpl in H. rewrite app_length in H.
              lia.
              rewrite H1 in H. simpl in H. rewrite app_length in H.
              lia.
        ++ destr.
           -- destruct fuel2.
              ** simpl in H;lia.
              ** cbn [decode_instrs]. simpl code_size.
                 rewrite Heqb.
                 destruct decode_instr eqn:DES;auto.
                 destruct p. apply decode_instr_len in DES.
                 destruct DES as (a & l2' & ? & UNUSE).
                 simpl. eapply decode_instrs_fuel;auto.
                 rewrite H1 in H. simpl in H. rewrite app_length in H.
                 lia.
                 rewrite H1 in H. simpl in H. rewrite app_length in H.
                 lia.
           -- destruct fuel2.
              ** simpl in H;lia.
              ** cbn [decode_instrs]. simpl code_size.
                 rewrite Heqb.
                 destruct decode_instr eqn:DES;auto.
                 destruct p. apply decode_instr_len in DES.
                 destruct DES as (a & l2' & ? & UNUSE).
                 simpl. eapply decode_instrs_fuel;auto.
                 rewrite H1 in H. simpl in H. rewrite app_length in H.
                 lia.
                 rewrite H1 in H. simpl in H. rewrite app_length in H.
                 lia.
    + cbn [app].
      destruct reloctbl1.
      * destruct reloctbl2;cbn [app] in *.
        -- monadInv H1. apply decode_instr_len in EQ.
           destruct EQ as (a & l2' & ? & DESGEN).
           inv H1. rewrite <- app_assoc.
           rewrite DESGEN. cbn [bind2].
           assert (decode_instrs instr_size Instr_size (fuel1 + fuel2)
    (x0 ++ l2) (genl ++ [x], []) = decode_instrs instr_size Instr_size (fuel1 + fuel2)
                                                 (x0 ++ l2) (genl ++ [x], []++[])) by auto.
           rewrite H1.
           erewrite  IHfuel1;eauto.
           simpl in H0. rewrite app_length in H0. lia.
        -- destr.
           **
Admitted.

  
Lemma instr_eq_list_len: forall l1 l2,
    Forall2 instr_eq l1 l2 ->
    code_size instr_size l1 = code_size instr_size l2.
Admitted.
  
Lemma decode_instrs_total_aux: forall c c' reloctbl reloctbl' ofs,
    fold_left (acc_instrs instr_size) c (OK ([], 0, reloctbl)) = OK (c', ofs, reloctbl') ->
    (* transl_code instr_size reloctbl c = OK c' -> *)
    exists c1 , decode_instrs' instr_size Instr_size reloctbl c' = OK (c1,reloctbl') /\ Forall2 instr_eq c c1.
Proof.
  intros c.
  assert (LEN: exists n, length c = n).
  { induction c. exists O. auto.
    destruct IHc.
    exists (S x). simpl. auto. }
  destruct LEN. generalize H. generalize x c.
  clear c x H. 
  induction x;intros.
  - rewrite length_zero_iff_nil in H. subst.
    simpl in *. inv H0.
    unfold decode_instrs'. simpl. exists [].
    split;auto.
  - exploit LocalLib.length_S_inv;eauto.
    intros (l' & a1 & A1 & B1). subst.
    clear H.
    rewrite fold_left_app in *.
    simpl in H0.
    unfold acc_instrs in H0 at 1.
    monadInv H0.
    (* transl_code property *)
    
    exploit transl_code_rev;eauto. intros (SIZE & (reloctbl1 & RELOCP)). subst.
    exploit IHx;eauto.
    clear EQ IHx.
    intros (c1 & P1 & P2).
    destruct ProdR.

    (* no reloctbl *)
    + monadInv EQ0.
      destr_in EQ2. inv EQ2.
      unfold decode_instrs' in *.
      monadInv P1.
      rewrite app_length.
      (* decode_instrs_bytes *)
      exploit decode_instrs_bytes_app;eauto. intros Q.
      rewrite Q. clear Q.
      exploit encode_into_byte_consistency;eauto. intros Q2.
      erewrite decode_instrs_bytes_app';eauto. simpl.
      (* decode_instrs *)
      clear EQ0 Q2 EQ1.
      rewrite app_length.

      erewrite decode_instrs_app;eauto.
      exploit translate_instr_consistency;eauto.
      erewrite app_nil_r. intros (i1 & M1 & M2).
      destruct x. simpl in M1. inv M1.
      cbn [length].
      unfold decode_instrs. rewrite M1.
      destruct x;simpl.

      exists (c1++[i1]). split;eauto.
      apply Forall2_app;eauto.
      exists (c1++[i1]). split;eauto.
      apply Forall2_app;eauto.

    + destr_in EQ0.
      * monadInv EQ0.
        destr_in EQ2. inv EQ2.
        unfold decode_instrs' in *.
        monadInv P1.
        (* decode_instrs_bytes *)
        rewrite app_length.
        exploit decode_instrs_bytes_app;eauto. intros Q.
        rewrite Q. clear Q.
        exploit encode_into_byte_consistency;eauto. intros Q2.
        erewrite decode_instrs_bytes_app';eauto. simpl.
        (* decode_instrs *)
        clear EQ0 Q2 EQ1.
        rewrite app_length.

        erewrite decode_instrs_app;eauto.
        exploit translate_instr_consistency;eauto.
        erewrite app_nil_r. intros (i1 & M1 & M2).
        (* instr_size preserve *)
        exploit translate_instr_size;eauto. rewrite app_nil_r.
        intros INSTRSIZE.
        destruct x. simpl in M1. inv M1.
        cbn [length].
        unfold decode_instrs.
        exploit instr_eq_list_len;eauto. intros LEN.
        rewrite <- LEN. rewrite INSTRSIZE.
        rewrite Heqb.
        rewrite M1.
        destruct x;simpl.

        exists (c1++[i1]). split;eauto.
        apply Forall2_app;eauto.
        exists (c1++[i1]). split;eauto.
        apply Forall2_app;eauto.
        
      * monadInv EQ0.
        destr_in EQ2. inv EQ2.
        unfold decode_instrs' in *.
        monadInv P1.
        (* decode_instrs_bytes *)
        rewrite app_length.
        exploit decode_instrs_bytes_app;eauto. intros Q.
        rewrite Q. clear Q.
        exploit encode_into_byte_consistency;eauto. intros Q2.
        erewrite decode_instrs_bytes_app';eauto. simpl.
        (* decode_instrs *)
        clear EQ0 Q2 EQ1.
        rewrite app_length.

        erewrite decode_instrs_app;eauto.
        exploit translate_instr_consistency;eauto.
        erewrite app_nil_r. intros (i1 & M1 & M2).
        (* instr_size preserve *)
        exploit translate_instr_size;eauto. rewrite app_nil_r.
        intros INSTRSIZE.
        destruct x. simpl in M1. inv M1.
        cbn [length].
        unfold decode_instrs.
        exploit instr_eq_list_len;eauto. intros LEN.
        rewrite <- LEN. rewrite INSTRSIZE.
        rewrite Heqb.
        rewrite M1.
        destruct x;simpl.

        exists (c1++[i1]). split;eauto.
        apply Forall2_app;eauto.
        exists (c1++[i1]). split;eauto.
        apply Forall2_app;eauto.
Qed.

Lemma decode_instrs_total: forall c c' reloctbl,
    transl_code instr_size reloctbl c = OK c' ->
    exists c1 reloctbl' , decode_instrs' instr_size Instr_size reloctbl c' = OK (c1,reloctbl') /\ Forall2 instr_eq c c1.
Proof.
  unfold transl_code;intros.
  monadInv H.
  apply decode_instrs_total_aux in EQ.
  destruct EQ.
  eexists x,ProdR. auto.
Qed.

Lemma decode_prog_code_section_total_aux: forall id sec sec' symbtbl reloctbl,
    acc_fold_section instr_size reloctbl id sec = OK sec' ->
    exists sec1, acc_decode_code_section instr_size Instr_size symbtbl reloctbl id sec' = OK sec1.
Proof.
  unfold acc_fold_section.
  intros.
  monadInv H.
  unfold transl_section in EQ.
  unfold acc_decode_code_section.
  destr_in EQ.
  - monadInv EQ.
    exploit decode_instrs_total;eauto. intros (c1 & reloctbl' & ? & ?).
    rewrite H. simpl. eexists;eauto.
  - monadInv EQ.
    eexists;eauto.
  - monadInv EQ.
    eexists;eauto.
Qed.

Lemma decode_prog_code_section_total: forall p tp,
    transf_program instr_size p = OK tp ->
    exists tp', decode_prog_code_section instr_size Instr_size tp = OK tp'.
Proof.
  unfold transf_program.
  intros. monadInv H.
  unfold transl_sectable in EQ.
  exploit PTree_fold_elements;eauto. intros A.
  clear EQ.
  unfold decode_prog_code_section. simpl.
  assert (exists t, PTree.fold
       (acc_PTree_fold
          (acc_decode_code_section instr_size Instr_size
             (prog_symbtable p) (prog_reloctables p))) x
       (OK (PTree.empty section1)) = OK t).
  { rewrite PTree.fold_spec.
    unfold section in *.
    revert A.
    generalize (PTree.elements x) as resl.
    unfold RelocProgram.section.
    generalize ((PTree.elements (prog_sectable p))).
    
    intros l.
    assert (LEN: exists n, length l = n).
    { induction l. exists O. auto.
      destruct IHl.
      exists (S x0). simpl. auto. }
    destruct LEN. generalize H. generalize l.
    clear l x H.
    induction x0;intros.
    - rewrite length_zero_iff_nil in H. subst.
      inv A.
      simpl in *. eexists. eauto.
    - exploit LocalLib.length_S_inv;eauto.
      intros (l' & a1 & A1 & B1). subst.
      clear H.
      apply list_forall2_app_inv_l in A.
      destruct A as (l4 & l5 & A1 & A2 & A3).
      inv A3. inv H3. destruct H1.
      rewrite H in *.
      exploit IHx0;eauto.
      intros (t & ?).
      rewrite fold_left_app. rewrite H1.
      simpl. 
      exploit decode_prog_code_section_total_aux;eauto.
      intros (sec1 & ?). rewrite H2. simpl. eauto. }

  destruct H. rewrite H. simpl. eauto.
Qed.

  
(* should be Hypothesis *)
Lemma translate_code_size: forall c1 c2 c3 r r',
          transl_code instr_size r c1 = OK c2 ->
          decode_instrs' instr_size Instr_size r c2 = OK (c3,r') ->
          code_size instr_size c1 = code_size instr_size c3.
Admitted.

Lemma rev_transl_code_size:forall r c,
    code_size instr_size c = code_size instr_size (RelocProgSemantics1.rev_transl_code instr_size r c).
Admitted.


Lemma transl_init_data_list_size: forall data l r,
    transl_init_data_list r data = OK l ->
    init_data_list_size data = Z.of_nat (length l).
Admitted.


Lemma store_init_data_list_app: forall ge m1 m2 b start d1 d2 ,
    store_init_data_list ge m1 b start (d1++d2) = Some m2 ->
    exists m1',  store_init_data_list ge m1 b start d1 = Some m1' /\
            store_init_data_list ge m1' b (start + init_data_list_size d1) d2 = Some m2.
Admitted.


(* exclude Vptr , Init_space is so difficult*)
Lemma transl_init_data_pres_mem: forall reloctbl d ge1 ge2 m1 m1' b ofs lm0 sz0 lb (MATCHGE: forall i ofs, RelocProgSemantics.Genv.symbol_address ge1 i ofs = RelocProgSemantics.Genv.symbol_address ge2 i ofs),
    store_init_data ge1 m1 b ofs d = Some m1' ->
    transl_init_data None d = OK lb ->
    match reloctbl with
    | h::_ => sz0 + (init_data_size d) <= h.(reloc_offset)
    | _ => True
    end ->
    exists lm, fold_left (acc_data ge2) lb (lm0,sz0,reloctbl) = (lm0 ++ lm, sz0 + init_data_size d, reloctbl) /\ init_data_size d =  Z.of_nat (length lm) /\ Mem.storebytes m1 b ofs lm = Some m1'.
Proof.
  intros.
  destruct d;simpl in H0;try congruence.
  - simpl in *. inv H0.
    generalize  (encode_int_length 1 (Int.unsigned i)).
    intros VALLEN.
    set (v:= (encode_int 1 (Int.unsigned i))) in *.
    destruct v eqn:ENC;simpl in VALLEN;try congruence.
    destruct l eqn:ENC';simpl in VALLEN;try congruence.
    simpl. 
    assert ([Byte i0] = encode_val Mint8unsigned (Vint i)).
    simpl. fold v. rewrite ENC. simpl. auto.
    rewrite H0.
    (* destruct reloctbl *)
    destruct reloctbl.
    + eexists.  split;eauto.
      split. rewrite encode_val_length. auto.      
      apply Mem.store_storebytes. auto.
    + Ltac solve_lt :=
        match goal with
        | |- context [?a && ?b] => assert (TMP: a = false) by (apply Z.leb_gt;lia);rewrite TMP;clear TMP;cbn [andb]
        end.
      repeat (solve_lt).
      eexists.  split;eauto.      
      split. rewrite encode_val_length. auto.      
      apply Mem.store_storebytes. auto.
  - simpl in *. inv H0.
    generalize  (encode_int_length 2 (Int.unsigned i)).
    intros VALLEN.
    set (v:= (encode_int 2 (Int.unsigned i))) in *.
    destruct v as [| b0 ?] eqn:ENC;simpl in VALLEN;try congruence.
    destruct l as [| b1 ?] eqn:ENC';simpl in VALLEN;try congruence.
    destruct l0 as [| b2 ?] eqn:ENC'';simpl in VALLEN;try congruence.

    assert ([Byte b0;Byte b1] = encode_val Mint16unsigned (Vint i)).
    simpl. fold v. rewrite ENC. simpl. auto.
    (* destruct reloctbl *)
    destruct reloctbl.
    + simpl.
      rewrite <- app_assoc. simpl. rewrite <- Z.add_assoc.
      simpl. rewrite H0.
      eexists.  split;eauto.
      split. rewrite encode_val_length. auto.      
      apply Mem.store_storebytes. auto.
    + do 2 (simpl;solve_lt).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- Z.add_assoc.
      simpl. eexists. split;eauto.
      rewrite H0.
      split. rewrite encode_val_length. auto.      
      apply Mem.store_storebytes. auto.


  - simpl in *. inv H0.
    generalize  (encode_int_length 4 (Int.unsigned i)).
    intros VALLEN.
    set (v:= (encode_int 4 (Int.unsigned i))) in *.
    destruct v as [| b0 ?] eqn:ENC0;simpl in VALLEN;try congruence.
    do 4 (destruct l as [| ?b ?] ;simpl in VALLEN;try congruence).
    assert ([Byte b0; Byte b1; Byte b2; Byte b3] = encode_val Mint32 (Vint i)).
    simpl. fold v. rewrite ENC0. simpl. auto.
    (* destruct reloctbl *)
    destruct reloctbl.
    + simpl.
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- Z.add_assoc.
      simpl. rewrite H0.
      eexists.  split;eauto.
      split. rewrite encode_val_length. auto.      
      apply Mem.store_storebytes. auto.
    + do 4 (simpl;solve_lt).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- Z.add_assoc.
      simpl. eexists. split;eauto.
      rewrite H0.
      split. rewrite encode_val_length. auto.      
      apply Mem.store_storebytes. auto.
    
  - simpl in *. inv H0.
    generalize  (encode_int_length 8(Int64.unsigned i)).
    intros VALLEN.
    set (v:= (encode_int 8 (Int64.unsigned i))) in *.
    destruct v as [| b0 ?] eqn:ENC0;simpl in VALLEN;try congruence.
    do 8 (destruct l as [| ?b ?] ;simpl in VALLEN;try congruence).
    assert ([Byte b0; Byte b1; Byte b2; Byte b3; Byte b4; 
    Byte b5; Byte b6; Byte b7] = encode_val Mint64 (Vlong i)).
    simpl. fold v. rewrite ENC0. simpl. auto.
        (* destruct reloctbl *)
    destruct reloctbl.
    + simpl.
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- Z.add_assoc.
      simpl. rewrite H0.
      eexists.  split;eauto.
      split. rewrite encode_val_length. auto.      
      apply Mem.store_storebytes. auto.
    + do 8 (simpl;solve_lt).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- Z.add_assoc.
      simpl. eexists. split;eauto.
      rewrite H0.
      split. rewrite encode_val_length. auto.      
      apply Mem.store_storebytes. auto.

  - simpl in *. inv H0.
    generalize  (encode_int_length 4 (Int.unsigned (Float32.to_bits f))).
    intros VALLEN.
    set (v:= (encode_int 4 (Int.unsigned (Float32.to_bits f)))) in *.
    destruct v as [| b0 ?] eqn:ENC0;simpl in VALLEN;try congruence.
    do 4 (destruct l as [| ?b ?] ;simpl in VALLEN;try congruence).
    assert ([Byte b0; Byte b1; Byte b2; Byte b3] = encode_val Mfloat32 (Vsingle f)).
    simpl. fold v. rewrite ENC0. simpl. auto.
        (* destruct reloctbl *)
    destruct reloctbl.
    + simpl.
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- Z.add_assoc.
      simpl. rewrite H0.
      eexists.  split;eauto.
      split. rewrite encode_val_length. auto.      
      apply Mem.store_storebytes. auto.
    + do 4 (simpl;solve_lt).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- Z.add_assoc.
      simpl. eexists. split;eauto.
      rewrite H0.
      split. rewrite encode_val_length. auto.      
      apply Mem.store_storebytes. auto.

      
  - simpl in *. inv H0.
    generalize  (encode_int_length 8 (Int64.unsigned (Float.to_bits f))).
    intros VALLEN.
    set (v:= (encode_int 8 (Int64.unsigned (Float.to_bits f)))) in *.
    destruct v as [| b0 ?] eqn:ENC0;simpl in VALLEN;try congruence.
    do 8 (destruct l as [| ?b ?] ;simpl in VALLEN;try congruence).
    assert ([Byte b0; Byte b1; Byte b2; Byte b3; Byte b4; 
    Byte b5; Byte b6; Byte b7] = encode_val Mfloat64 (Vfloat f)).
    simpl. fold v. rewrite ENC0. simpl. auto.
        (* destruct reloctbl *)
    destruct reloctbl.
    + simpl.
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- Z.add_assoc.
      simpl. rewrite H0.
      eexists.  split;eauto.
      split. rewrite encode_val_length. auto.      
      apply Mem.store_storebytes. auto.
    + do 8 (simpl;solve_lt).
      repeat rewrite <- app_assoc. simpl. repeat rewrite <- Z.add_assoc.
      simpl. eexists. split;eauto.
      rewrite H0.
      split. rewrite encode_val_length. auto.      
      apply Mem.store_storebytes. auto.

  (* so difficult *)
  - simpl in *. inv H0.
    destr_in H3. apply Z.leb_gt in Heqb0.
    destruct z;try lia.

    erewrite Z.max_l in *;try lia. inv H3.
    (* unfold Pos.to_nat.  *)
    (* Pos.iter_op_succ *)
      
    
    (* encode_val encode_int Int.zero *)
    (* Z.iter *)
    (* Pos.iter *)
    (* store_zeros_equation *)
    (* Require Import Recdef. *)
    (* generalize (Z.max_spec 0 z). intros [(? & ?) | (? & ?)]. *)
    (* rewrite Z.max_comm in H1. *)
    (* rewrite H1 in *. clear e H1. *)
    
    (* functional induction (store_zeros m1 b ofs z). *)
    (* lia.  *)
    (* apply zle_true in _x. *)
    (* store_zeros_ind *)
    (*               Vzero *)
    (* Mem.store_ *)
    (* inv H0. *)
    admit.
Admitted.

(* can be proved ?  *)
Lemma storebytes_append: forall m1 m2 m3 b start l1 l2,
    Mem.storebytes m1 b start l1 = Some m2 ->
    Mem.storebytes m2 b (start +  Z.of_nat (length l1)) l2 = Some m3 ->
    Mem.storebytes m1 b start (l1 ++ l2) = Some m3.
Admitted.



Lemma transl_init_data_list_pres_mem: forall n data reloctbl reloctbl' sz l b m1 m2 ge1 ge2
                                   (MATCHGE: forall i ofs, RelocProgSemantics.Genv.symbol_address ge1 i ofs = RelocProgSemantics.Genv.symbol_address ge2 i ofs),
    length data = n ->
    fold_left acc_init_data data (OK ([], 0, reloctbl)) = OK (l, sz, reloctbl') ->
    (* transl_init_data_list r data = OK l -> *)
    RelocProgSemantics.store_init_data_list ge1 m1 b 0 data = Some m2 ->
    exists bl, fold_left (acc_data ge2) l ([], 0, reloctbl) = (bl, sz, reloctbl') /\ init_data_list_size data = Z.of_nat (length bl) /\  Mem.storebytes m1 b 0 bl = Some m2.
          (* store_init_data_bytes ge2 r m1 b 0 l = Some m2. *)
Proof.
  induction n;intros.
  (* nil: unable to solve, storebytes impossiblely produce same memory *)
  (* apply length_zero_iff_nil in H. *)
  (* subst. simpl in *. inv H0. inv H1. *)
  (* simpl. eexists. split;eauto. split;eauto. *)
  (* Transparent Mem.storebytes. unfold Mem.storebytes. *)
  (* simpl. Mem.getN_ destr.  *)
  admit.
  
  exploit LocalLib.length_S_inv;eauto.
  intros (l' & a1 & A1 & B1). subst.
  clear H.
  rewrite fold_left_app in H0.
  simpl in H0. unfold acc_init_data in H0 at 1.
  monadInv H0.
  exploit store_init_data_list_app;eauto.
  intros (m1' & P1 & P2).
  destruct ProdR.
  - monadInv EQ0.
    
    exploit IHn;eauto.
    intros (bl & Q1 & Q2 & Q3).
    rewrite fold_left_app. 
    rewrite Q1. simpl in P2.
    destr_in P2. inv P2.
    exploit (transl_init_data_pres_mem []);eauto. simpl.
    intros (lm & ? & INITLEN & ?). erewrite H.
    eexists. split;eauto.
    split. erewrite LocalLib.init_data_list_size_app.
    rewrite app_length. simpl. rewrite INITLEN.
    lia. (* add size to transl_init_data_pres_mem *)
    eapply storebytes_append;eauto.
    rewrite Z.add_0_l.
    rewrite <- Q2. auto.
  - destr_in EQ0.
    + monadInv EQ0.
      exploit IHn;eauto.
      intros (bl & Q1 & Q2 & Q3).
      rewrite fold_left_app. rewrite Q1.
      destruct a1;simpl in EQ1;try congruence.
      destr_in EQ1. 
      apply Z.eqb_eq in Heqb0. subst.
      cbn [init_data_size] in *.
      apply andb_true_iff in Heqb1.
      destruct Heqb1 as (SYMB & ADDEND).
      rewrite Z.add_0_l in P2.
      simpl in P2. destr_in P2. inv P2.
      apply Pos.eqb_eq in SYMB.
      apply Z.eqb_eq in ADDEND.
      rewrite <- (Ptrofs.repr_unsigned i0)in Heqo. subst.
      rewrite <- ADDEND in Heqo.
      erewrite MATCHGE in Heqo.
      eapply Mem.store_storebytes in Heqo. unfold Mptr in *.

      destr_in EQ1.
      * monadInv EQ1.
       
        generalize  (encode_int_length 8 (Ptrofs.unsigned i0)).
        intros VALLEN.
        set (v:= (encode_int 8 (Ptrofs.unsigned i0))) in *.
        destruct v as [| b0 ?] eqn:ENC0;simpl in VALLEN;try congruence.
        do 8 (destruct l as [| ?b ?] ;simpl in VALLEN;try congruence).
        simpl. rewrite Heqb0.

        (* 7 *)
        assert ((reloc_offset r <=? reloc_offset r) &&
                (reloc_offset r <? reloc_offset r + 8) = true) by admit.
        rewrite H. clear H.
        rewrite Z.sub_diag. simpl.
        (* 6 *)
        rewrite Heqb0. 
        assert ((reloc_offset r <=? reloc_offset r + 1) &&
                (reloc_offset r + 1 <? reloc_offset r + 8) = true) by admit.
        rewrite H. clear H.
        repeat rewrite Z.add_sub_swap. rewrite Z.sub_diag. simpl.
        (* 5 *)
        rewrite Heqb0.
        assert ((reloc_offset r <=? reloc_offset r + 1 + 1) &&
                (reloc_offset r + 1 + 1 <? reloc_offset r + 8) = true) by admit.
        rewrite H. clear H.
        repeat rewrite Z.add_sub_swap. rewrite Z.sub_diag. simpl.
        (* 4 *)
        rewrite Heqb0.
        assert ((reloc_offset r <=? reloc_offset r + 1 + 1 + 1) &&
                (reloc_offset r + 1 + 1 + 1 <? reloc_offset r + 8) = true) by admit.
        rewrite H. clear H.
        repeat rewrite Z.add_sub_swap. rewrite Z.sub_diag. simpl.
        (* 3 *)
        rewrite Heqb0.
        assert ((reloc_offset r <=? reloc_offset r + 1 + 1 + 1 + 1) &&
                (reloc_offset r + 1 + 1 + 1 + 1 <? reloc_offset r + 8) = true) by admit.
        rewrite H. clear H.
        repeat rewrite Z.add_sub_swap. rewrite Z.sub_diag. simpl.
        (* 2 *)
        rewrite Heqb0.
        assert ((reloc_offset r <=? reloc_offset r + 1 + 1 + 1 + 1 + 1) &&
                (reloc_offset r + 1 + 1 + 1 + 1 + 1 <? reloc_offset r + 8)= true) by admit.
        rewrite H. clear H.
        repeat rewrite Z.add_sub_swap. rewrite Z.sub_diag. simpl.
        (* 1 *)
        rewrite Heqb0.
        assert ( (reloc_offset r <=? reloc_offset r + 1 + 1 + 1 + 1 + 1 + 1) &&
                 (reloc_offset r + 1 + 1 + 1 + 1 + 1 + 1 <? reloc_offset r + 8) = true) by admit.
        rewrite H. clear H.
        repeat rewrite Z.add_sub_swap. rewrite Z.sub_diag. simpl.
        (* 0 *)
        rewrite Heqb0.
        assert ((reloc_offset r <=? reloc_offset r + 1 + 1 + 1 + 1 + 1 + 1 + 1) &&
      (reloc_offset r + 1 + 1 + 1 + 1 + 1 + 1 + 1 <?
       reloc_offset r + 8) = true) by admit.
        rewrite H. clear H.
        repeat rewrite Z.add_sub_swap. rewrite Z.sub_diag. simpl.
        eexists. split. do 2 f_equal.
        lia.

        unfold Genv.symbol_address in *.
        destr_in Heqo.

        ++ destruct p.
           split. repeat rewrite app_length. cbn [length].
           rewrite LocalLib.init_data_list_size_app. simpl.
           rewrite Heqb0. lia.
           simpl. 
                      
           repeat rewrite <- app_assoc.
           eapply storebytes_append;eauto.
           rewrite Z.add_0_l. rewrite <- Q2.

           rewrite <- Heqo. f_equal.
        ++ split. repeat rewrite app_length. cbn [length].
           rewrite LocalLib.init_data_list_size_app. simpl.
           rewrite Heqb0. lia.
           simpl. 
                      
           repeat rewrite <- app_assoc.
           eapply storebytes_append;eauto.
           rewrite Z.add_0_l. rewrite <- Q2.

           rewrite <- Heqo. f_equal.

      (* 32bit *)
      *       admit.

    (* without relocentry *)
    + destr_in EQ0.
      monadInv EQ0.
      rewrite fold_left_app.
      rewrite Z.add_0_l in *.
      simpl in P2. destr_in P2.
      exploit IHn;eauto.
      intros (bl & Q1 & Q2 & Q3).
      rewrite Q1.
      
      exploit (transl_init_data_pres_mem (r::ProdR));eauto.
      eapply Z.leb_le. eauto.
      intros (lm & ? & INITLEN & ?). erewrite H.
      eexists. split;eauto.
      rewrite LocalLib.init_data_list_size_app. simpl.
      rewrite INITLEN.
      split. rewrite app_length. lia.
      eapply storebytes_append;eauto.
      rewrite Z.add_0_l.
      rewrite <- Q2. inv P2.  auto.
Admitted.


Lemma alloc_section_pres_mem: forall ge1 ge2 id sec sec1 sec2 m m0 reloctbl symbtbl
    (MATCHGE: forall i ofs, RelocProgSemantics.Genv.symbol_address ge1 i ofs = RelocProgSemantics.Genv.symbol_address ge2 i ofs),
    acc_fold_section instr_size reloctbl id sec = OK sec1 ->
    acc_decode_code_section instr_size Instr_size symbtbl reloctbl id sec1 = OK sec2 ->
    RelocProgSemantics.alloc_section instr_size ge1 symbtbl (Some m) id (RelocProgSemantics1.rev_section instr_size reloctbl id sec) = Some m0 ->
    alloc_section instr_size ge2 reloctbl (Some m) id sec2 = Some m0.
Proof.
  intros.
  destruct sec.

  (* code section *)
  - unfold acc_fold_section in H.
    monadInv H.
    simpl in EQ.
    monadInv EQ.
    unfold acc_decode_code_section in H0.
    monadInv H0.
    unfold alloc_section.
    simpl in H1.
    exploit translate_code_size;eauto.
    intros.
    destruct (reloctbl ! id).
    + simpl in *.
      rewrite <-  rev_transl_code_size in *.
      rewrite H in *.
        auto.
    + simpl in *. rewrite H in *. auto.

  (* rwdata section *)
  - unfold acc_fold_section in H.
    monadInv H.
    simpl in EQ. monadInv EQ.
    simpl in *. inv H0.
    exploit transl_init_data_list_size;eauto.
    intros. rewrite H in H1.
    destruct (Mem.alloc_glob id m 0 (Z.of_nat (Datatypes.length x))).
    destr. destr_in H1.    
    unfold transl_init_data_list in EQ0. monadInv EQ0.
    exploit transl_init_data_list_pres_mem;eauto.
    intros (bl & ? & ? & ?).
    unfold store_init_data_bytes.
    unfold reloctable in *.
    rewrite H0. simpl.
    rewrite H3. auto.

    (* rwdata section *)
  - unfold acc_fold_section in H.
    monadInv H.
    simpl in EQ. monadInv EQ.
    simpl in *. inv H0.
    exploit transl_init_data_list_size;eauto.
    intros. rewrite H in H1.
    destruct (Mem.alloc_glob id m 0 (Z.of_nat (Datatypes.length x))).
    destr. destr_in H1.    
    unfold transl_init_data_list in EQ0. monadInv EQ0.
    exploit transl_init_data_list_pres_mem;eauto.
    intros (bl & ? & ? & ?).
    unfold store_init_data_bytes.
    unfold reloctable in *.
    rewrite H0. simpl.
    rewrite H3. auto.

Qed.
               
Section PRESERVATION. 
(** Transformation *)
Variable prog: RelocProgram.program.
Variable tprog: program.
Hypothesis TRANSF: match_prog prog tprog.


Let ge := RelocProgSemantics1.globalenv instr_size prog.
Let tge := globalenv instr_size Instr_size tprog.

Lemma senv_refl:
  (Genv.genv_senv ge) = (Genv.genv_senv tge).
Admitted.


(* instruction map is mostly identical *)
Lemma find_instr_refl: forall b ofs i,
    Genv.genv_instrs ge b ofs = Some i ->
    exists i1, Genv.genv_instrs tge b ofs = Some i1
          /\ instr_eq i i1.
Proof.
  unfold ge,tge. unfold globalenv.
  unfold match_prog in TRANSF.
  exploit decode_prog_code_section_total;eauto.
  intros (tp' & A). rewrite A.
  simpl.
  unfold transf_program in *. monadInv TRANSF.
  unfold transl_sectable in EQ.
  unfold decode_prog_code_section in *.
  monadInv A. simpl in *.
  clear ge tge.
Admitted.

Lemma find_ext_funct_refl: forall v,
    Genv.find_ext_funct ge v = Genv.find_ext_funct tge v.
Admitted.
  

Lemma symbol_address_pres: forall id ofs,
    RelocProgSemantics.Genv.symbol_address ge id ofs =
    RelocProgSemantics.Genv.symbol_address tge id ofs.
Proof.
  intros.
  unfold ge, tge. unfold globalenv.
  exploit decode_prog_code_section_total;eauto.
  intros (tp' & A).
  rewrite A.
  unfold RelocProgSemantics.Genv.symbol_address.
  unfold RelocProgSemantics.Genv.find_symbol.
  unfold RelocProgSemantics.globalenv. simpl.
  unfold match_prog in TRANSF.
  unfold transf_program in TRANSF. monadInv TRANSF.
  unfold decode_prog_code_section in A. simpl in *.
  monadInv A. simpl.
  auto.
Qed.

Lemma transf_initial_state:forall st1 rs,
    RelocProgSemantics1.initial_state instr_size prog rs st1 ->
    exists st2, initial_state instr_size Instr_size tprog rs st2 /\ st1 = st2.
  intros st1 rs H.
  inv H. inv H1.
  unfold match_prog in TRANSF.
  exploit decode_prog_code_section_total;eauto.
  intros (tp' & A).
  (* to prove init_mem equal *)
  assert (TOPROVE: init_mem instr_size tp' = Some m).
  { unfold RelocProgSemantics.init_mem in H.
    unfold init_mem.
    simpl in H. destr_in H.

    (* alloc sections preserve memory *)
  assert (ALLOCSECS: alloc_sections instr_size (RelocProgSemantics.globalenv instr_size tp')
                         (prog_symbtable tp') (prog_reloctables tp') 
                         (prog_sectable tp') Mem.empty = Some m0).
  { 
    set (ge1:= (RelocProgSemantics.globalenv instr_size (RelocProgSemantics1.decode_program instr_size prog))) in *.
    set (ge2:= (RelocProgSemantics.globalenv instr_size tp')).
    (* globalenv property *)
    assert (GEProp: forall id ofs,RelocProgSemantics.Genv.symbol_address ge1 id ofs = RelocProgSemantics.Genv.symbol_address ge2 id ofs).
    { intros.
      exploit (symbol_address_pres).
      unfold ge,tge,ge1,ge2.
      unfold globalenv. rewrite A.
      unfold RelocProgSemantics1.globalenv. eauto. } (* end of GEProp *)
      
    unfold decode_prog_code_section in A.
    monadInv A. simpl.
    unfold transf_program in TRANSF. monadInv TRANSF.
    unfold transl_sectable in  EQ0. simpl in *.
    exploit PTree_fold_elements. apply EQ. intros F1. clear EQ.
    exploit PTree_fold_elements. apply EQ0. intros F2. clear EQ0.
    unfold RelocProgSemantics.alloc_sections in Heqo.
    unfold alloc_sections. rewrite PTree.fold_spec.
    rewrite PTree.fold_spec in Heqo.
    unfold RelocProg.sectable in *.
    generalize (PTree_map_elements _ _ (RelocProgSemantics1.rev_section instr_size (prog_reloctables prog)) (prog_sectable prog)).
    simpl. intros F3.
    (* induction on (prog_reloctables prog) *)
    set (l:= @PTree.elements RelocProgram.section (prog_sectable prog)) in *.
    set (l1:= @PTree.elements section x0) in *.
    set (l2 := @PTree.elements _ x) in *.
    unfold RelocProgram.section in F3,Heqo.
    (* Set Printing All. *)
    set (l3:= (@PTree.elements _
            (@PTree.map (RelocProg.section instruction init_data) _
               (RelocProgSemantics1.rev_section instr_size
                                                (prog_reloctables prog)) (prog_sectable prog)))) in *.
    
    clear ge tge H H0.
    revert F1 F2 F3 Heqo.
    generalize m0.
    generalize l l1 l2 l3. clear l l1 l2 l3.
    intros l.
    assert (LEN: exists n, length l = n).
    { induction l. exists O. auto.
      destruct IHl.
      exists (S x1). simpl. auto. }
    destruct LEN. revert H.
    generalize x1,l. clear x1 l.
    clear m m0.
    
    (* core proof *)
    
    induction x1;intros.
    - rewrite length_zero_iff_nil in H. subst.
      inv F3. inv F2. inv F1.
      simpl in Heqo. inv Heqo.
      simpl. auto.
    - exploit LocalLib.length_S_inv;eauto.
      intros (l' & a1 & A1 & B1). subst.
      clear H.
      exploit list_forall2_app_inv_l. apply F2.
      intros (? & ? & ? & ? & ?). subst.
      inv H1. inv H5.
      exploit list_forall2_app_inv_l. apply F3.
      intros (? & ? & ? & ? & ?). subst.
      inv H2. inv H7.
      exploit list_forall2_app_inv_l. apply F1.
      intros (? & ? & ? & ? & ?). subst.
      inv H4. inv H9.
      clear F1 F2 F3.
      rewrite fold_left_app in Heqo. simpl in Heqo.
      destruct ((fold_left
              (fun (a : option mem)
                 (p : positive *
                      RelocProg.section instruction init_data) =>
               RelocProgSemantics.alloc_section instr_size ge1
                 (prog_symbtable prog) a (fst p) 
                 (snd p)) x2 (Some Mem.empty))) eqn:FOLD.
      2:{ simpl in Heqo. inv Heqo. }
      exploit IHx1. eapply eq_refl.
      eapply H2. auto. eauto.
      eauto.
      clear IHx1 H2 H1 H0.
      intros FOLD1. rewrite fold_left_app.
      rewrite FOLD1. cbn [fold_left] in *.
      clear FOLD1 FOLD.
      destruct H3. destruct H5. destruct H7.
      rewrite <- H3 in *. rewrite <- H in *.
      unfold RelocProgram.section in *.
      rewrite H1 in *. clear H H1 H3.
      rewrite <- H2 in *. clear H2.
      exploit alloc_section_pres_mem;eauto. } (* end of assert ALLOCSECS *)

  rewrite ALLOCSECS.
  unfold decode_prog_code_section in A.
  monadInv A. simpl.
  unfold transf_program in TRANSF. monadInv TRANSF.
  simpl in *. auto. }           (* end of assert TOPROVE *)
  
  inv H0.
  
  set (ge2:= (RelocProgSemantics.globalenv instr_size tp')).
  set (rs0' := rs # PC <- (RelocProgSemantics.Genv.symbol_address ge2 tp'.(prog_main) Ptrofs.zero)
           # RA <- Vnullptr
           # RSP <- (Vptr stk (Ptrofs.sub (Ptrofs.repr (max_stacksize + align (size_chunk Mptr) 8)) (Ptrofs.repr (size_chunk Mptr))))) in *.
  
  exists (State rs0' m2).
  constructor;eauto. econstructor;eauto.
  econstructor;eauto.
  f_equal.
  
  
  (* globalenv property *)
  assert (GEProp: forall id ofs,RelocProgSemantics.Genv.symbol_address ge0 id ofs = RelocProgSemantics.Genv.symbol_address ge2 id ofs).
  { intros.
    exploit (symbol_address_pres).
    unfold ge,tge,ge0,ge2.
    unfold globalenv. rewrite A.
    unfold RelocProgSemantics1.globalenv. eauto. } (* end of GEProp *)
  intros.
  unfold rs0,rs0'.
  erewrite GEProp.
  unfold decode_prog_code_section in A.
  monadInv A. cbn [prog_main].
  unfold transf_program in TRANSF. monadInv TRANSF.
  cbn [prog_main]. auto.
Qed.

Lemma exec_instr_refl: forall i rs m,
    exec_instr instr_size ge i rs m = exec_instr instr_size tge i rs m.
Admitted.

Lemma eval_addrmode_refl: forall a rs,
    eval_addrmode ge a rs = eval_addrmode tge a rs.
Admitted.

  
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
      rewrite <- symbol_address_pres.
      auto.
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

  - unfold Genv.find_instr in H1.
  (* builtin instr impossible *)
    admit.
  - 
    rewrite find_ext_funct_refl in H0.
    eapply exec_step_external;eauto.
    rewrite <- senv_refl. auto.
Admitted.


Lemma transf_program_correct: forall rs,
    forward_simulation (RelocProgSemantics1.semantics instr_size prog rs) (semantics instr_size Instr_size tprog rs).
Proof.
  intros.
  eapply forward_simulation_step with (match_states:= fun (st1 st2:Asm.state) => st1 = st2).
  - simpl. unfold match_prog in TRANSF.
    exploit decode_prog_code_section_total;eauto.
    intros (tp' & ?).
    unfold globalenv. rewrite H. simpl.
    unfold transf_program in TRANSF.
    monadInv TRANSF. unfold decode_prog_code_section in H.
    simpl in *. monadInv H. simpl.
    auto.
  - intros. simpl.
    eapply transf_initial_state.
    auto.
  - simpl. intros. subst.
    auto.
  - simpl. intros.
    subst. fold tge. fold ge in H.
    exists s1'. split;auto.
    apply step_simulation. auto.
Qed.

End PRESERVATION.

End WITH_INSTR_SIZE.
