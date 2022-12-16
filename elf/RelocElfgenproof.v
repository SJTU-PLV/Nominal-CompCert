Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgramBytes RelocElf Globalenvs.
Require Import Stacklayout Conventions.
Require Import Linking RelocProgLinking RelocElfLinking Errors.
Require Import EncDecRet RelocElfgen.
Require Import RelocProgSemantics RelocProgSemantics1.
Require Import TranslateInstr RelocProgSemantics2 RelocElfSemantics.
Require Import SymbtableDecode ReloctablesEncode.
Require Import RelocProgGlobalenvs RelocProgSemanticsArchi.
Require Import ReloctablesEncodeArchi.
Import Hex Bits.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope string_byte_scope.

Lemma decode_encode_reloctable_correct: forall n l bs m1 m2 (M: match_idxmap m1 m2),
    let reloclen := if Archi.ptr64 then 24%nat else 8%nat in
    length l = n ->
    encode_reloctable m1 l = OK bs ->
    fold_left (acc_decode_reloctable_section Archi.ptr64 reloclen m2) bs (OK ([], [], 1%nat)) = OK (l, [], 1%nat).
Proof.
  induction n;intros.
  rewrite length_zero_iff_nil in H. subst.
  simpl in H0. inv H0.
  unfold decode_reloctable_section. simpl. auto.

  exploit LocalLib.length_S_inv;eauto.
  intros (l' & a1 & A1 & B1). subst.
  clear H.
  unfold encode_reloctable in H0. rewrite fold_left_app in H0.
  simpl in H0. unfold acc_reloctable in H0 at 1.
  monadInv H0. exploit IHn;eauto.
  intros. rewrite fold_left_app.
  unfold reloclen.
  rewrite H. clear H EQ IHn.
  exploit encode_relocentry_len;eauto.
  intros LEN. rename x0 into l.
  clear x.
  eapply ReloctablesDecode.decode_encode_relocentry in EQ1;eauto.
  destr.
  - do 25 (destruct l as [| ?b ?] ;simpl in LEN;try congruence).
    simpl in *. rewrite EQ1. simpl. auto.
  - do 9 (destruct l as [| ?b ?] ;simpl in LEN;try congruence).
    simpl in *. rewrite EQ1. simpl. auto.
Qed.

    
Lemma acc_decode_symbtable_section_eq: forall l l' m e strtbl id strtbl' t,
    let symblen:= if Archi.ptr64 then 24%nat else 16%nat in
    length l = symblen ->
    (if Archi.ptr64 then decode_symbentry64 l m = OK e
    else decode_symbentry32 l m = OK e) ->
    id_from_strtbl strtbl = OK (id, strtbl') ->
    fold_left (acc_decode_symbtable_section Archi.ptr64 symblen m) (l++l') (OK (t, strtbl, [], 1%nat)) = fold_left (acc_decode_symbtable_section Archi.ptr64 symblen m) l' (OK ((PTree.set id e t), strtbl', [], 1%nat)).
Proof.
  simpl. destruct Archi.ptr64.
  - intros.
    do 25 (destruct l as [| ?b ?] ;simpl in H;try congruence).
    clear H.
    simpl. rewrite H0.
    simpl. rewrite H1.
    simpl. auto.
  - intros.
    do 17 (destruct l as [| ?b ?] ;simpl in H;try congruence).
    clear H.
    simpl. rewrite H0.
    simpl. rewrite H1.
    simpl. auto.
Qed.


    
Lemma ident_to_index_injective_aux: forall n l s sz m1 (NOREP: list_norepet l),
    length l = n ->
    fold_left acc_ident_to_index l (PTree.empty Z, s) = (m1, sz) ->
    exists m2, fold_left acc_index_to_ident l (ZTree.empty ident, s) = (m2, sz) /\
          (forall i ofs, ofs >= sz -> m1 ! i <> Some ofs) /\
          (forall i1 i2 e, m1 ! i1 = Some e -> m1 ! i2 = Some e -> i1 = i2) /\
          (forall i ofs, m1 ! i = Some ofs -> ZTree.get ofs m2 = Some i).
Proof.
   induction n;intros;simpl.
   rewrite length_zero_iff_nil in H. subst.
   simpl in H0. inv H0.
   simpl. exists (ZTree.empty ident).
   split;auto.
   split. intros. rewrite PTree.gempty. congruence.
   
   split. intros.    rewrite PTree.gempty in H. congruence.
   (* split. intros. rewrite PTree.gempty in H. congruence. *)
   intros. rewrite PTree.gempty in H. congruence.
   exploit LocalLib.length_S_inv;eauto.
   intros (l' & a1 & A1 & B1). subst.
   clear H.
   rewrite fold_left_app in *.
   simpl in *.
   destruct fold_left eqn:FOLD in H0.
   (* rewrite app_length in H0. *)
   (* simpl in H0. *)
   (* rewrite Nat.add_comm in H0. *)
   (* simpl in H0. *)
   (* assert (s + Z.pos (Pos.of_succ_nat (Datatypes.length l')) = s + 1 + Z.of_nat (Datatypes.length l')). *)
   (* lia. rewrite H in H0. *)
   (* clear H. inv H0. *)
   (* assert (z = s + Z.of_nat (Datatypes.length l')) by lia. *)
   (* subst. clear H2. *)

   apply list_norepet_app in NOREP.
   destruct NOREP as (NOREP1 & NOREP2 & DIS).
   clear NOREP2.
   simpl in H0.     inv H0.
   exploit IHn;eauto.
   intros (m2' & FOLD2 & INCR & INJ  & M).
   rewrite FOLD2.
   simpl. eexists. split;eauto.

   split.
   intros. 
   rewrite PTree.gsspec. destr.
   unfold not. intros. inv H0. lia.
   apply INCR. lia.
   
   assert (INJ': forall (i1 i2 : positive) (e : Z),
  (PTree.set a1 z t) ! i1 = Some e ->
  (PTree.set a1 z t) ! i2 = Some e ->
  i1 = i2).
   { intros.
     rewrite PTree.gsspec in H.
     destr_in H. inv H.
     rewrite PTree.gsspec in H0.
     destr_in H0.
     exploit (INCR i2 e). lia.
     auto. intros. apply False_ind. auto.
     rewrite PTree.gsspec in H0.
     destr_in H0. inv H0.
     exploit (INCR i1 e). lia.
     auto. intros. apply False_ind. auto.
     eapply INJ;eauto. }
     
   split.
   
   auto.

   intros. 
   generalize H. intros BH.
   rewrite PTree.gsspec in H.
   destr_in H.
   inv H.  rewrite ZTree.gsspec. destr.
   rewrite ZTree.gsspec. destr. 
   rewrite <- e in *.
   assert ((PTree.set a1 ofs t) ! a1 = Some ofs).
   rewrite PTree.gsspec. destr.
   exploit INJ'. apply BH. apply H0.
   intros.  subst. congruence.
   apply M. auto.
Qed.

   
   
Lemma ident_to_index_injective: forall l s i ofs (NOREP: list_norepet l),
    (ident_to_index l s) ! i = Some ofs ->
    ZTree.get ofs (index_to_ident l s) = Some i.
Proof.
  unfold ident_to_index.
  unfold index_to_ident.
  intros.
  destruct fold_left eqn:FOLD in H.
  exploit ident_to_index_injective_aux;eauto.
  intros (m2 & P1 & P2 & P3 & P4).
  rewrite P1. simpl. auto.
Qed.



Lemma id_from_strtbl_result_aux: forall l1 l2 l3,
    ~ In (Byte.repr 0) l1 ->
    id_from_strtbl_aux (l1 ++ l2) l3 = id_from_strtbl_aux l2 (l3 ++ l1).
Proof.
  induction l1;intros;simpl in *.
  rewrite app_nil_r. auto.

  apply Decidable.not_or in H.
  destruct H. rewrite Byte.eq_false;auto.
  rewrite IHl1;auto.
  rewrite <- app_assoc. auto.
Qed.


Lemma id_from_strtbl_result: forall l l' i,
    SymbolString.find_symbol_pos i = Some l ->
    ~ In (Byte.repr 0) (map (fun p : positive => Byte.repr (Z.pos p)) l) ->
    id_from_strtbl ((map (fun p : positive => Byte.repr (Z.pos p)) l) ++ Byte.repr 0 :: l') = OK (i, l').
Proof.

  intros.
  unfold id_from_strtbl.
  rewrite id_from_strtbl_result_aux;eauto.
  simpl. rewrite Byte.eq_true.
  erewrite SymbolString.string_to_ident_symbol_to_pos. eauto.
  auto.
Qed.
   
Lemma combine_app: forall A B (l1 l1':list A) (l2 l2': list B),
    length l1 = length l2 ->
    combine (l1++l1') (l2++l2') = combine l1 l2 ++ combine l1' l2'.
Proof.
  induction l1;intros.
  - destruct l2;simpl in H;try congruence.
    simpl. auto.
  - destruct l2;simpl in H;try congruence.
    simpl. rewrite IHl1;auto.
Qed.


Definition match_prog (p: program) (tp: elf_file) :=
  gen_reloc_elf p = OK tp.

Lemma transf_program_match:
  forall p tp, gen_reloc_elf p = OK tp -> match_prog p tp.
Proof.
  auto.
Qed.

Section WITH_INSTR_SIZE.

Variable instr_size : instruction -> Z.

(* encode decode consistency *)

Record program_equiv {F V I D: Type} (p1 p2: RelocProg.program F V I D) :=
  mk_program_equiv {
      pe_symbtable: forall id,
        p1.(prog_symbtable) ! id = p2.(prog_symbtable) ! id;
      pe_sectable: forall id,
          p1.(prog_sectable) ! id = p2.(prog_sectable) ! id;
      pe_reloctable_map: forall id,
          p1.(prog_reloctables) ! id = p2.(prog_reloctables) ! id;
      (* external function *)
      pe_prog_defs: p1.(RelocProg.prog_defs) = p2.(RelocProg.prog_defs);
      (* main function *)
      pe_prog_main: p1.(RelocProg.prog_main) = p2.(RelocProg.prog_main);
      (* senv *)
      pe_prog_senv: p1.(RelocProg.prog_senv) = p2.(RelocProg.prog_senv)
    }.

Lemma program_equiv_sym: forall F V I D (p1 p2: RelocProg.program F V I D),
    program_equiv p1 p2 ->
    program_equiv p2 p1.
Proof.
  intros.
  eapply mk_program_equiv;symmetry.
  apply pe_symbtable;auto.
  apply pe_sectable;auto.
  apply pe_reloctable_map;auto.
  apply pe_prog_defs;auto.
  apply pe_prog_main;auto.
  apply pe_prog_senv;auto.
Qed.

  
(* most important *)
Lemma gen_reloc_elf_correct: forall p elf,
    gen_reloc_elf p = OK elf ->
    exists p', decode_elf elf = OK p' /\ program_equiv p p'.
Proof.
  unfold gen_reloc_elf,decode_elf.
  intros. monadInv H.
  do 3 destr_in EQ4.
  (* ptr64 *)
  assert ((get_ptr64 elf) = Archi.ptr64).
  unfold get_ptr64. inv EQ4.
  simpl. destruct Archi.ptr64;auto.
  rewrite H. clear H.
  
  inv EQ4. simpl in *. clear Heqb l.

  (* shstrtbl *)
  unfold gen_shstrtbl in EQ2.
  destr_in EQ2. destruct x.
  unfold update_elf_state in EQ2.
  simpl in EQ2. repeat rewrite app_nil_r in EQ2.
  repeat rewrite Z.add_0_r in EQ2.
  inv EQ2.
  simpl in *. do 2 rewrite removelast_last.
  rewrite last_last.
  clear Heqb.
  
  (* headers len *)
  repeat rewrite app_length in Heqb0.
  simpl in Heqb0.
  eapply Nat.eqb_eq in Heqb0.
  destruct e_headers. simpl in Heqb0. lia.
  simpl.
  
  (* reloc sections *)
  destruct ProdL0.
  unfold gen_reloc_sections_and_shstrtbl in EQ0.
  simpl in EQ0. monadInv EQ0.
  destr_in EQ3. unfold update_elf_state in EQ3.
  simpl in EQ3. inv EQ3.
  simpl.

  (* symbtable section *)
  destruct ProdL.
  unfold gen_symtbl_section_strtbl_and_shstr in EQ1.
  simpl in EQ1.
  monadInv EQ1. destr_in EQ3.
  unfold update_elf_state in EQ3.
  simpl in EQ3. inv EQ3.
  clear Heqb.

  (* text data sections *)
  unfold initial_elf_state in EQ.
  unfold gen_text_data_sections_and_shstrtbl in EQ.
  monadInv EQ. do 2 destr_in EQ3.
  unfold update_elf_state in EQ3.
  cbn [RelocElfgen.e_headers_idx] in EQ3.
  rewrite (Z.add_comm 1) in EQ3. simpl in EQ3.
  inv EQ3.

  (* null headers *)
  simpl in H1.
  inv H1.

  (* combine append *)
  erewrite combine_app.
  2: { repeat rewrite <- app_assoc.
       repeat rewrite app_length.
       simpl. lia. }
  rewrite fold_left_app.
  
  erewrite combine_app.
  2: { repeat rewrite <- app_assoc.
       repeat rewrite app_length.
       simpl. lia. }
  rewrite fold_left_app.

   erewrite combine_app.
  2: { repeat rewrite <- app_assoc.
       repeat rewrite app_length.
       simpl. lia. }
  rewrite fold_left_app.
  
  (* encode decode sections and section headers consistency *)
  repeat rewrite <- app_assoc.
  assert (C1: exists sectbl, fold_left (acc_section_header Archi.ptr64)
                (combine e_sections ProdR9)
                (OK (init_dec_state
                       (* skip '0' *)
                      (tail (e_shstrtbl ++
                       strtab_str ++
                       symtab_str ++ ProdR2 ++ shstrtab_str)))) =
                        OK {| dec_sectable := sectbl;
                              dec_symbtable := PTree.empty symbentry;
                              dec_reloctable := PTree.empty reloctable;
                              dec_shstrtbl := strtab_str ++ symtab_str ++ ProdR2 ++ shstrtab_str;
                              dec_strtbl := [] |} /\ (forall i e, In (i,e) (PTree.elements sectbl) <-> In (i,e) (PTree.elements p.(prog_sectable)))).
  { clear Heqb EQ0 e EQ2 Heqb0.
    clear ProdL1 ProdL0 ProdR6 ProdR4 ProdR5 ProdR3 ProdR1.
    unfold gen_section_header in EQ1.

    generalize (PTree.elements_keys_norepet (prog_sectable p)).
    intros NOREP.
    set (str:= strtab_str ++ symtab_str ++ ProdR2 ++ shstrtab_str).
    set (l:= (PTree.elements (prog_sectable p))) in *.
    assert (LEN: exists n, length l = n).
    { clear EQ1 NOREP.
      induction l. exists O. auto.
      destruct IHl.
      exists (S x). simpl. auto. }

    
    destruct LEN.
    generalize H EQ1 e0 NOREP.
    generalize e_sections ProdR9 e_sections_ofs e_shstrtbl e_shstrtbl_ofs str.
    generalize x l.    
    clear l x H EQ1 e0 NOREP.
    clear e_sections ProdR9 e_sections_ofs e_shstrtbl e_shstrtbl_ofs str.
    induction x;intros.
    - rewrite length_zero_iff_nil in H. subst.
      simpl in EQ1. inv EQ1.
      cbn [combine]. simpl.
      eexists. unfold init_dec_state.      
      split;eauto. simpl. intros.
      split;auto.
    - exploit LocalLib.length_S_inv;eauto.
      intros (l' & a1 & A1 & B1). subst.
      clear H.
      rewrite fold_left_app in *.
      fold ident in *.
      fold RelocProgramBytes.section in *.
      destruct ((fold_left (acc_sections_headers (prog_symbtable p)) l'
                           (OK ([], [], 0, [Byte.repr 0], 1)))) eqn:FOLD.
      repeat destruct p0.
      simpl in EQ1. destruct a1. 
      monadInv EQ1. destr_in EQ0.
      destruct s.

      (* text section *)
      + destr_in EQ0.
        inv EQ0.
        do 2 rewrite app_length in e0. simpl in e0.
        rewrite combine_app;try lia. rewrite fold_left_app.
        simpl.
        (* e_shstrtbl and l *)
        unfold acc_strtbl in EQ.
        destr_in EQ. destr_in EQ. simpl in EQ.
        inv EQ. repeat rewrite <- app_assoc.
        (* use induction *)
        exploit IHx;eauto. lia.
        rewrite map_app in NOREP.
        rewrite list_norepet_app in NOREP.
        simpl in NOREP.
        destruct NOREP as (NOREP1 & NOREP2 & DISJOINT).
        auto.
        intros (sectbl' & P1 & P2).
        erewrite P1. clear P1 IHx.
        simpl.
        (* id from strtbl *)
        simpl in n.
        erewrite id_from_strtbl_result;eauto.
        simpl.
        (* finish *)
        unfold update_sectable_shstrtbl. simpl.
        eexists. split;eauto.
        intros.
        (* norepeat *)
        rewrite map_app in NOREP.
        rewrite list_norepet_app in NOREP.
        simpl in NOREP.
        destruct NOREP as (NOREP1 & NOREP2 & DISJOINT).
        apply list_disjoint_sym in DISJOINT.
        unfold list_disjoint in DISJOINT.
        assert (I: In i [i]) by (simpl;auto).
        generalize (DISJOINT i). intros DIS.
        split.
        * intros.
          apply PTree.elements_complete in H.
          rewrite PTree.gsspec in H.
          destr_in H.
          -- inv H. rewrite in_app.
             right. simpl. auto.
          -- rewrite in_app.
             left. apply P2.
             apply PTree.elements_correct. auto.
        * rewrite in_app.
          intros [? | ?].
          -- assert (In i0 (map fst l')).
             apply in_map_iff.
             exists (i0,e). simpl. split;auto.
             apply (DIS i0 I) in H0.
             apply PTree.elements_correct.
             rewrite PTree.gsspec. destr.
             apply PTree.elements_complete.
             apply P2. auto.
          -- simpl in H. inv H.
             inv H0. apply PTree.elements_correct.
             rewrite PTree.gsspec.
             rewrite peq_true.
             auto.
             apply False_ind. auto.
             
      (* rwdata section *)
      + destr_in EQ0.
        inv EQ0.
        do 2 rewrite app_length in e0. simpl in e0.
        rewrite combine_app;try lia. rewrite fold_left_app.
        simpl.
        (* e_shstrtbl and l *)
        unfold acc_strtbl in EQ.
        destr_in EQ. destr_in EQ. simpl in EQ.
        inv EQ. repeat rewrite <- app_assoc.
        (* use induction *)
        exploit IHx;eauto. lia.
        rewrite map_app in NOREP.
        rewrite list_norepet_app in NOREP.
        simpl in NOREP.
        destruct NOREP as (NOREP1 & NOREP2 & DISJOINT).
        auto.
        intros (sectbl' & P1 & P2).
        erewrite P1. clear P1 IHx.
        simpl.
        (* id from strtbl *)
        simpl in n.
        erewrite id_from_strtbl_result;eauto.
        simpl.
        (* finish *)
        unfold update_sectable_shstrtbl. simpl.
        eexists. split;eauto.
        intros.
        (* norepeat *)
        rewrite map_app in NOREP.
        rewrite list_norepet_app in NOREP.
        simpl in NOREP.
        destruct NOREP as (NOREP1 & NOREP2 & DISJOINT).
        apply list_disjoint_sym in DISJOINT.
        unfold list_disjoint in DISJOINT.
        assert (I: In i [i]) by (simpl;auto).
        generalize (DISJOINT i). intros DIS.
        split.
        * intros.
          apply PTree.elements_complete in H.
          rewrite PTree.gsspec in H.
          destr_in H.
          -- inv H. rewrite in_app.
             right. simpl. auto.
          -- rewrite in_app.
             left. apply P2.
             apply PTree.elements_correct. auto.
        * rewrite in_app.
          intros [? | ?].
          -- assert (In i0 (map fst l')).
             apply in_map_iff.
             exists (i0,e). simpl. split;auto.
             apply (DIS i0 I) in H0.
             apply PTree.elements_correct.
             rewrite PTree.gsspec. destr.
             apply PTree.elements_complete.
             apply P2. auto.
          -- simpl in H. inv H.
             inv H0. apply PTree.elements_correct.
             rewrite PTree.gsspec.
             rewrite peq_true.
             auto.
             apply False_ind. auto.
             
      (* rodata *)
      + destr_in EQ0.
        inv EQ0.
        do 2 rewrite app_length in e0. simpl in e0.
        rewrite combine_app;try lia. rewrite fold_left_app.
        simpl.
        (* e_shstrtbl and l *)
        unfold acc_strtbl in EQ.
        destr_in EQ. destr_in EQ. simpl in EQ.
        inv EQ. repeat rewrite <- app_assoc.
        (* use induction *)
        exploit IHx;eauto. lia.
        rewrite map_app in NOREP.
        rewrite list_norepet_app in NOREP.
        simpl in NOREP.
        destruct NOREP as (NOREP1 & NOREP2 & DISJOINT).
        auto.
        intros (sectbl' & P1 & P2).
        erewrite P1. clear P1 IHx.
        simpl.
        (* id from strtbl *)
        simpl in n.
        erewrite id_from_strtbl_result;eauto.
        simpl.
        (* finish *)
        unfold update_sectable_shstrtbl. simpl.
        eexists. split;eauto.
        intros.
        (* norepeat *)
        rewrite map_app in NOREP.
        rewrite list_norepet_app in NOREP.
        simpl in NOREP.
        destruct NOREP as (NOREP1 & NOREP2 & DISJOINT).
        apply list_disjoint_sym in DISJOINT.
        unfold list_disjoint in DISJOINT.
        assert (I: In i [i]) by (simpl;auto).
        generalize (DISJOINT i). intros DIS.
        split.
        * intros.
          apply PTree.elements_complete in H.
          rewrite PTree.gsspec in H.
          destr_in H.
          -- inv H. rewrite in_app.
             right. simpl. auto.
          -- rewrite in_app.
             left. apply P2.
             apply PTree.elements_correct. auto.
        * rewrite in_app.
          intros [? | ?].
          -- assert (In i0 (map fst l')).
             apply in_map_iff.
             exists (i0,e). simpl. split;auto.
             apply (DIS i0 I) in H0.
             apply PTree.elements_correct.
             rewrite PTree.gsspec. destr.
             apply PTree.elements_complete.
             apply P2. auto.
          -- simpl in H. inv H.
             inv H0. apply PTree.elements_correct.
             rewrite PTree.gsspec.
             rewrite peq_true.
             auto.
             apply False_ind. auto.
             
      + simpl in EQ1. congruence. }

  (* rewrite C1 *)
  destruct C1 as (sectbl & C1 & C1').
  rewrite C1. clear C1.

  (* strtable section *)
  cbn [combine].
  cbn [fold_left].
  set (str:= strtab_str ++ symtab_str ++ ProdR2 ++ shstrtab_str).
  assert (C2: acc_section_header Archi.ptr64
             (OK
                {|
                dec_sectable := sectbl;
                dec_symbtable := PTree.empty symbentry;
                dec_reloctable := PTree.empty reloctable;
                dec_shstrtbl := str;
                dec_strtbl := [] |})
             (ProdR6,
             gen_strtab_sec_header ProdR6 e_shstrtbl_ofs
               e_sections_ofs) = (OK
                {|
                dec_sectable := sectbl;
                dec_symbtable := PTree.empty symbentry;
                dec_reloctable := PTree.empty reloctable;
                dec_shstrtbl := symtab_str ++ ProdR2 ++ shstrtab_str;
                dec_strtbl := ProdR6 |})).
  { unfold acc_section_header.
    unfold gen_strtab_sec_header. cbn [bind].
    cbn [sh_type]. cbn [dec_shstrtbl].
    unfold str.
    rewrite Encode.take_drop_length_app.
    auto. auto. }

  fold section in C2.
  rewrite C2. clear C2.
  clear str.

  (* sectbl and prog_sectable isomorphic *)
  assert (C1'' : forall i, sectbl ! i = (prog_sectable p) ! i).
  { intros.
    destruct (sectbl ! i) eqn: G.
    apply PTree.elements_correct in G. apply C1' in G.
    apply PTree.elements_complete in G.
    auto.
    destruct ((prog_sectable p) ! i) eqn: G'.
    apply PTree.elements_correct in G'. apply C1' in G'.
    apply PTree.elements_complete in G'.
    congruence.
    auto. }
  apply PTree.elements_extensional in C1''. clear C1'.

  (* sort symbol table not change *)
  assert (SORT: forall i e, In (i,e) (sort_symbtable (PTree.elements (prog_symbtable p))) <-> In (i,e) (PTree.elements (prog_symbtable p))). {
      unfold sort_symbtable.
      intros. split.
      - intros. apply in_app in H.
        destruct H.
        + apply filter_In in H. destruct H.
          auto.
        + apply filter_In in H. destruct H.
          auto.
      - intros.
        apply in_app.
        destruct (filter_local_symbe (i,e1)) eqn: F.
        + left. apply filter_In.
          split;auto.
        + right. apply filter_In.
          split;auto.
          unfold filter_local_symbe in F.
          unfold filter_global_symbe.
          destr_in F. }
  assert (SORTNOREP: list_norepet (map fst (sort_symbtable (PTree.elements (prog_symbtable p))))).
  { 
    unfold sort_symbtable.
    rewrite map_app.
    apply list_norepet_app.
    split.
    apply LocalLib.list_norepet_filter_fst_pres.
    apply PTree.elements_keys_norepet.
    split.
    apply LocalLib.list_norepet_filter_fst_pres.
    apply PTree.elements_keys_norepet.
    unfold list_disjoint. intros.
    apply in_map_iff in H. destruct H as (x0 & X1 & X2).
    apply in_map_iff in H0. destruct H0 as (y0 & Y1 & Y2).
    subst. apply filter_In in X2.
    apply filter_In in Y2.
    destruct X2. destruct Y2.
    unfold filter_local_symbe in H0.
    unfold filter_global_symbe in H2.
    destr_in H0. destr_in H2.
    destruct x0. destruct y0.
    simpl. apply PTree.elements_complete in H.
    apply PTree.elements_complete in H1.
    simpl in *. unfold not.
    intros. subst. rewrite H in H1. congruence. }
    
  set (dummy_entry:=(if Archi.ptr64
                     then SymbtableEncode.encode_dummy_symbentry64
                     else SymbtableEncode.encode_dummy_symbentry32)) in *.

  set (str:= symtab_str ++ ProdR2 ++ shstrtab_str).
  simpl.
  unfold decode_symbtable_section.
  assert (DUMMY: length dummy_entry = (if Archi.ptr64 then 24%nat else 16%nat)).
  destr.
  rewrite skipn_app. rewrite <- DUMMY. rewrite skipn_all.
  rewrite Nat.sub_diag. rewrite skipn_O.
  cbn [app].

  set (symblen:= (if Archi.ptr64 then 24%nat else 16%nat)) in *.
  rewrite DUMMY.
  
    (* symbol table section *)
  assert (C3: forall tl,
             exists symbtbl,
             fold_left
               (acc_decode_symbtable_section Archi.ptr64 symblen
              (index_to_ident (map fst (PTree.elements sectbl)) 1))
               ProdL0 (OK (PTree.empty symbentry, tail (ProdR6 ++ tl), [], 1%nat)) =
             OK (symbtbl, tl, [], 1%nat) /\ (forall i e, In (i,e) (PTree.elements symbtbl) <->
                         In (i,e) (sort_symbtable (PTree.elements (prog_symbtable p))))).

          (*    (acc_section_header Archi.ptr64 *)
          (* (OK *)
          (*    {| *)
          (*    dec_sectable := sectbl; *)
          (*    dec_symbtable := PTree.empty symbentry; *)
          (*    dec_reloctable := PTree.empty reloctable; *)
          (*    dec_shstrtbl := symtab_str ++ ProdR2 ++ shstrtab_str; *)
          (*    dec_strtbl := ProdR6 |}) *)
          (* (dummy_entry ++ ProdL0, *)
          (* gen_symtab_sec_header *)
          (*   (map snd *)
          (*      (sort_symbtable (PTree.elements (prog_symbtable p)))) *)
          (*   (e_shstrtbl_ofs + 8) (e_sections_ofs + ProdR5) *)
          (*   (Z.of_nat (Datatypes.length ProdR9) + 1))) = *)
          (*                OK {| dec_sectable := sectbl; *)
          (*                      dec_symbtable := symbtbl; *)
          (*                      dec_reloctable := PTree.empty reloctable; *)
          (*                      dec_shstrtbl := ProdR2 ++ shstrtab_str; *)
          (*                      dec_strtbl := ProdR6 |} /\ *)
          (*                (forall i e, In (i,e) (PTree.elements symbtbl) <-> *)
          (*                In (i,e) (sort_symbtable (PTree.elements (prog_symbtable p))))). *)
  { 
    clear e0 EQ1 Heqb e EQ2 SORT.
    clear ProdR1 ProdR3.
    clear Heqb0 ProdR9 ProdR4.
    clear e_sections_ofs e_shstrtbl_ofs e_shstrtbl e_sections.
    
    unfold create_symbtable_section in EQ0.
    rewrite C1'' in *. clear C1''.
    

    (* generalize strtbl *)
    (* assert (STRGEN: exists tl, ProdR6 = ProdR6 ++ tl). *)
    (* exists []. apply app_nil_end. *)
    (* destruct STRGEN as (tl & ProdR6H). rewrite ProdR6H. clear ProdR6H. *)
    
    
    set (l:= (sort_symbtable (PTree.elements (prog_symbtable p)))) in *.
    
    assert (LEN: exists n, length l = n).
    { clear EQ0 SORTNOREP.
      induction l. exists O. auto.
      destruct IHl.
      exists (S x). simpl. auto. }
    destruct LEN as (n & LEN).
    
    unfold str. clear str. set (str:= ProdR2 ++ shstrtab_str).
    generalize LEN EQ0 SORTNOREP.
    generalize  ProdR5 ProdL0 ProdR6.
    generalize n l.
    clear LEN EQ0 SORTNOREP.    
    clear ProdR5 ProdL0 ProdR6 ProdL1.
    clear n l.
    
    
    
    induction n;intros.
    - rewrite length_zero_iff_nil in LEN. subst.
      simpl in EQ0. inv EQ0.
      cbn [fold_left]. cbn [bind].
      simpl.
      eexists. split;eauto.
      split. intros. simpl in H. auto. intros.
      apply False_ind. auto.
      
    - exploit LocalLib.length_S_inv;eauto.
      intros (l' & a1 & A1 & B1). subst.
      clear LEN.
      rewrite fold_left_app in *.
      simpl in EQ0.
      unfold acc_symbtable_bytes in EQ0 at 1. destruct a1.
      monadInv EQ0.
      set (str':= symtab_str ++ str).
      unfold decode_symbtable_section.
      rewrite fold_left_app.
      (* use induction hypothesis *)
      rewrite map_app in SORTNOREP.
      apply list_norepet_app in SORTNOREP.
      destruct SORTNOREP as (NOREP1 & NOREP2 & DIS).
      (* acc_strtbl: ProdR6 = ProdR0 ++ xxx *)
      unfold acc_strtbl in EQ1.
      destr_in EQ1. destr_in EQ1. simpl in EQ1.
      inv EQ1. (* rewrite <- app_assoc. *)
      (* use I.H. *)
      exploit IHn;eauto.
     
      intros (symbtbl' & P1 & P2).
      (* monadInv P1. monadInv EQ1. *)
      (* rewrite EQ2. *)
      simpl.
      rewrite <- app_assoc.
      rewrite P1. clear P1 IHn.
      rewrite (app_nil_end x).

      erewrite acc_decode_symbtable_section_eq.
      3: { destr.
           eapply decode_encode_symbentry64;eauto.
           unfold match_idxmap. intros.
           eapply ident_to_index_injective.
           eapply PTree.elements_keys_norepet.
           auto.
           eapply decode_encode_symbentry32;eauto.
           unfold match_idxmap. intros.
           eapply ident_to_index_injective.
           eapply PTree.elements_keys_norepet.
           auto. }
      3: { rewrite <- app_assoc.
           simpl. eapply id_from_strtbl_result.
           eauto. eauto. }
      2: { unfold symblen.
           destr. eapply SymbtableEncode.encode_symbentry64_len;eauto.
           eapply SymbtableEncode.encode_symbentry32_len;eauto. }
           
      simpl. eexists. split;eauto.
      intros. split;intros.
      + apply in_app.
        apply PTree.elements_complete in H.
        rewrite PTree.gsspec in H.
        destr_in H.
        * inv H. right. constructor. auto.
        * left. apply P2. apply PTree.elements_correct;auto.
      + apply PTree.elements_correct.
        rewrite PTree.gsspec.
        apply in_app in H.
        destruct H.
        * unfold list_disjoint in DIS.
          assert (i0 <> i).
          apply DIS. eapply (in_map fst) in H.
          simpl in H. auto. simpl. auto.
          destr. apply PTree.elements_complete.
          apply P2. auto.
        * inv H. inv H0.
          destr. inv H0. }

  rewrite (app_nil_end ProdR6).
  generalize (C3 []). clear C3. intros (symbtbl & C3 & C3').
  rewrite C3. simpl. clear C3.
  rewrite app_nil_r.

  (* reloc sections *)
  unfold update_symbtable.
  simpl.
  (* elements symbtbl = elements p.prog_symbtable *)
  exploit (PTree.elements_extensional symbtbl (prog_symbtable p)).
  intros. destruct (symbtbl ! i) eqn:G.
  apply PTree.elements_correct in G. apply C3' in G.
  apply SORT in G. apply PTree.elements_complete in G.
  rewrite G. auto.
  destruct ((prog_symbtable p) ! i) eqn:G1;auto.
  apply PTree.elements_correct in G1. apply SORT in G1.
  apply C3' in G1. apply PTree.elements_complete in G1.
  rewrite G in G1. congruence.
  clear C3' SORT. intros C3'.

  assert (C4: exists reloctbl,
         fold_left (acc_section_header Archi.ptr64)
       (combine ProdL1 ProdR4)
       (OK
          {|
          dec_sectable := sectbl;
          dec_symbtable := symbtbl;
          dec_reloctable := PTree.empty reloctable;
          dec_shstrtbl := ProdR2 ++ shstrtab_str;
          dec_strtbl := ProdR6 |}) =
         OK
          {|
          dec_sectable := sectbl;
          dec_symbtable := symbtbl;
          dec_reloctable := reloctbl;
          dec_shstrtbl := shstrtab_str;
          dec_strtbl := ProdR6 |} /\
         (forall i e, In (i,e) (PTree.elements reloctbl) <-> In (i,e) (PTree.elements (prog_reloctables p)))). {
  clear DUMMY symblen str C1''.
  clear e0 EQ1 Heqb EQ0.
  clear Heqb0 dummy_entry.
  clear ProdL0  e_shstrtbl e_sections.
  
  unfold gen_reloc_sections_headers in EQ2.

  generalize (PTree.elements_keys_norepet (prog_reloctables p)).
  intros NOREP.

  set (l:= (PTree.elements (prog_reloctables p))) in *.
  generalize NOREP EQ2 e.
  generalize  ProdR1 ProdR2 ProdR3 ProdR4 ProdL1.
  clear NOREP EQ2 e.
  clear ProdR1 ProdR2 ProdR3 ProdR4 ProdL1.
  generalize shstrtab_str.
  assert (LEN: exists n, length l = n).
  { induction l. exists O. auto.
    destruct IHl.
    exists (S x). simpl. auto. }
  destruct LEN as (n & LEN).
  generalize n l LEN. clear n l LEN.
  induction n;intros.
  - rewrite length_zero_iff_nil in LEN. subst.
    simpl in EQ2. inv EQ2.
    simpl. eexists. split;eauto.
    simpl. intros. split;auto.
  - exploit LocalLib.length_S_inv;eauto.
    intros (l' & a1 & A1 & B1). subst.
    clear LEN.
    rewrite fold_left_app in EQ2.
    simpl in EQ2.
    unfold acc_reloc_sections_headers in EQ2 at 1.
    monadInv EQ2. destruct a1.
    destr_in EQ0. monadInv EQ0.

    (* combine append *)
    do 2 rewrite app_length in e. simpl in e.    
    rewrite combine_app;try lia.
    rewrite fold_left_app.
    
    (* norepeat *)
    rewrite map_app in NOREP.
    apply list_norepet_app in NOREP.
    destruct NOREP as (NOREP1 & NOREP2 & DIS).

    (* acc relocstrtbl *)
    unfold acc_relstrtbl in EQ0.
    destr_in EQ0.
    destr_in EQ0.
    Opaque Encode.string_to_bytes.
    simpl in EQ0. inv EQ0.
    repeat rewrite app_assoc_reverse.
    
    (* use I.H. *)
    exploit IHn;eauto. lia.
    intros (reloctbl' & P1 & P2).
    rewrite P1.
    clear IHn P1 EQ.
    
    simpl.
    Transparent Archi.ptr64. simpl. (* 32bit and 64bit is identical *)
    Transparent Encode.string_to_bytes.
    simpl. unfold update_reloctable_shstrtbl.
    simpl in *.    
    erewrite id_from_strtbl_result;eauto.
    simpl. 

    (* decoe encode reloctable correct *)
    unfold decode_reloctable_section.
    erewrite decode_encode_reloctable_correct;eauto.
    simpl. eexists. split;eauto.
    2: { unfold match_idxmap.
         intros. erewrite ident_to_index_injective;eauto.
         rewrite C3'. auto. 
         rewrite C3'. auto. }

    (* In elements *)
    intros. split;intros.
    + apply in_app.
      apply PTree.elements_complete in H.
        rewrite PTree.gsspec in H.
        destr_in H.
        * inv H. right. constructor. auto.
        * left. apply P2. apply PTree.elements_correct;auto.
      + apply PTree.elements_correct.
        rewrite PTree.gsspec.
        apply in_app in H.
        destruct H.
        * unfold list_disjoint in DIS.
          assert (i <> p0).
          apply DIS. eapply (in_map fst) in H.
          simpl in H. auto. simpl. auto.
          destr. apply PTree.elements_complete.
          apply P2. auto.
        * inv H. inv H0.
          destr. inv H0. }

  (* final *)
  destruct C4 as (reloctbl & C4 & C4').
  rewrite C4. simpl. eexists. split;eauto.
  (* program_equiv *)
  constructor;simpl;auto;intros.
  - destruct ((prog_symbtable p) ! id) eqn:G.
    apply PTree.elements_correct in G.
    rewrite <- C3' in G. apply PTree.elements_complete in G.
    auto.
    destruct (symbtbl ! id) eqn:G'.
    apply PTree.elements_correct in G'.
    rewrite ->  C3' in G'. apply PTree.elements_complete in G'.
    congruence. auto.
  - destruct ((prog_sectable p) ! id) eqn:G.
    apply PTree.elements_correct in G.
    rewrite <- C1'' in G. apply PTree.elements_complete in G.
    auto.
    destruct (sectbl ! id) eqn:G'.
    apply PTree.elements_correct in G'.
    rewrite ->  C1'' in G'. apply PTree.elements_complete in G'.
    congruence. auto.
  - destruct ((prog_reloctables p) ! id) eqn:G.
    apply PTree.elements_correct in G.
    apply C4' in G. apply PTree.elements_complete in G.
    auto.
    destruct (reloctbl ! id) eqn:G'.
    apply PTree.elements_correct in G'.
    apply C4' in G'. apply PTree.elements_complete in G'.
    congruence. auto.
Qed.

    
    
Lemma decode_prog_code_section_correct: forall p1 p2 p1',
    program_equiv p1 p2 ->
    decode_prog_code_section p1 = OK p1' ->
    exists p2', decode_prog_code_section p2 = OK p2' /\ program_equiv p1' p2'.
Proof.
  unfold decode_prog_code_section.
  intros.
  monadInv H0. 
  rewrite PTree.fold_spec in *.
  assert ((PTree.elements (prog_sectable p1)) = (PTree.elements (prog_sectable p2))).
  { exploit PTree.elements_extensional.
    intros. exploit (@pe_sectable fundef unit);eauto.
    auto. }
  unfold RelocProgramBytes.section in *.
  rewrite H0 in *. clear H0.
  set (l := (PTree.elements (prog_sectable p2))) in *.
  assert (LEN: exists n, length l = n).
  { clear EQ.
    induction l. exists O. auto.
    destruct IHl.
    exists (S x0). simpl. auto. }
  
  destruct LEN. generalize EQ H0. generalize x0 l x.
  clear l x0 H0 EQ x. 
  induction x0;intros.
  - rewrite length_zero_iff_nil in H0. subst.
    simpl in *. inv EQ.
    eexists. split. eauto. simpl.
    constructor;simpl;auto.
    eapply pe_symbtable;eauto.
    eapply pe_reloctable_map;eauto.
    eapply pe_prog_defs;eauto.
    eapply pe_prog_main;eauto.
    eapply pe_prog_senv;auto.
  - exploit LocalLib.length_S_inv;eauto.
    intros (l' & a1 & A1 & B1). subst.
    clear H0.
    rewrite fold_left_app in *.
    simpl in *.
    unfold acc_PTree_fold in EQ at 1. monadInv EQ.
    exploit IHx0;eauto.
    intros (p2' & P1 & P2).
    monadInv P1. rewrite EQ1. simpl.
    clear EQ1 EQ0 IHx0.
    assert (acc_decode_code_section (prog_reloctables p2) (fst a1) (snd a1) = OK x1).
    { unfold acc_decode_code_section in *.
      assert ((PTree.elements (prog_reloctables p1)) = (PTree.elements (prog_reloctables p2))).
      exploit PTree.elements_extensional.
      intros. exploit (@pe_reloctable_map fundef unit);eauto.
      auto. auto. }
    rewrite H0.
    simpl. eexists. split;eauto.
    constructor;simpl;auto.
    eapply pe_symbtable;eauto.
    intros. do 2 rewrite PTree.gsspec.
    destr.
    exploit (@pe_sectable fundef unit);eauto.
    eapply pe_reloctable_map;eauto.
    eapply pe_prog_defs;auto.
    eapply pe_prog_main;eauto.
    eapply pe_prog_senv;auto.
Qed.



Lemma program_equiv_symbol_address: forall D (p1 p2: RelocProg.program fundef unit instruction D),
    program_equiv p1 p2 ->
    forall id ofs, RelocProgGlobalenvs.Genv.symbol_address (RelocProgSemantics.globalenv instr_size p1) id ofs = RelocProgGlobalenvs.Genv.symbol_address (RelocProgSemantics.globalenv instr_size p2) id ofs.
Proof.
  intros.
  unfold RelocProgSemantics.globalenv. unfold RelocProgGlobalenvs.Genv.symbol_address.
  unfold RelocProgGlobalenvs.Genv.find_symbol. simpl.
  assert ((gen_symb_map (prog_symbtable p1)) ! id = (gen_symb_map (prog_symbtable p2)) ! id).
  unfold gen_symb_map.
  repeat rewrite PTree.gmap.
  erewrite pe_symbtable. eauto.
  auto.
  rewrite H0.
  auto.
Qed.

Lemma program_equiv_symbol_address1: forall D (p1 p2: RelocProg.program fundef unit instruction D),
    program_equiv p1 p2 ->
    forall id ofs, RelocProgGlobalenvs.Genv.symbol_address (RelocProgSemantics1.globalenv instr_size p1) id ofs = RelocProgGlobalenvs.Genv.symbol_address (RelocProgSemantics1.globalenv instr_size p2) id ofs.
Proof.
  intros.
  unfold RelocProgSemantics1.globalenv. unfold RelocProgGlobalenvs.Genv.symbol_address.
  unfold RelocProgGlobalenvs.Genv.find_symbol. simpl.
  assert ((gen_symb_map (prog_symbtable p1)) ! id = (gen_symb_map (prog_symbtable p2)) ! id).
  unfold gen_symb_map.
  repeat rewrite PTree.gmap.
  erewrite pe_symbtable. eauto.
  auto.
  rewrite H0.
  auto.
Qed.


Lemma program_equiv_instr_map: forall D (p1 p2: RelocProg.program fundef unit instruction D),
    program_equiv p1 p2 ->
    RelocProgGlobalenvs.Genv.genv_instrs (RelocProgSemantics1.globalenv instr_size p1) = RelocProgGlobalenvs.Genv.genv_instrs (RelocProgSemantics1.globalenv instr_size p2).
Proof.
  unfold RelocProgSemantics1.globalenv.
  simpl. unfold gen_code_map. intros.
  repeat rewrite PTree.fold_spec in *.
  f_equal. eapply PTree.elements_extensional.
  intros.
  do 2 erewrite PTree.gmap.  
  erewrite pe_sectable;eauto.
  destruct ((prog_sectable p2) ! i );auto.
  simpl. f_equal.
  unfold rev_section.
  destr. erewrite  pe_reloctable_map;eauto.
Qed.

Lemma program_equiv_ext_funs: forall D (p1 p2: RelocProg.program fundef unit instruction D),
    program_equiv p1 p2 ->
    Genv.genv_ext_funs (RelocProgSemantics.globalenv instr_size p1) = Genv.genv_ext_funs (RelocProgSemantics.globalenv instr_size p2).
Proof.
  unfold RelocProgSemantics.globalenv.
  simpl. unfold gen_extfuns. intros.
  f_equal.
  eapply pe_prog_defs. auto.
Qed.

Lemma program_equiv_ext_funs1: forall D (p1 p2: RelocProg.program fundef unit instruction D),
    program_equiv p1 p2 ->
    RelocProgGlobalenvs.Genv.genv_ext_funs (RelocProgSemantics1.globalenv instr_size p1) = RelocProgGlobalenvs.Genv.genv_ext_funs (RelocProgSemantics1.globalenv instr_size p2).
Proof.
  unfold RelocProgSemantics1.globalenv.
  simpl. unfold gen_extfuns. intros.
  f_equal.
  eapply pe_prog_defs. auto.
Qed.


Lemma store_init_data_bytes_match_ge: forall n bytes reloctbl m b p ge1 ge2 (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs),
    length bytes = n ->
    store_init_data_bytes ge1 reloctbl m b p bytes = store_init_data_bytes ge2 reloctbl m b p bytes.
Proof. 
  unfold store_init_data_bytes. intros. do 4 f_equal.
  generalize H. clear H. revert bytes.
  generalize dependent n. 
  induction n;intros.
  - rewrite length_zero_iff_nil in H. subst.
    simpl. auto.
  - exploit LocalLib.length_S_inv;eauto.
    intros (l' & a1 & A1 & B1). subst.
    clear H.
    repeat rewrite fold_left_app in *.
    exploit IHn;eauto. intros.    
    simpl. rewrite H.
    destruct fold_left. destruct p0. destruct p0.
    rewrite <- H.
    unfold acc_data.

    destruct l0;auto.
    destr. destr.
    rewrite MATCHGE.
    destr.
Qed.


Lemma program_equiv_init_mem: forall p1 p2 m,
    program_equiv p1 p2 ->
    init_mem instr_size p1 = Some m ->
    init_mem instr_size p2 = Some m.
Proof.
  unfold init_mem.
  intros. destr_in H0.
  assert (alloc_sections instr_size
      (RelocProgSemantics.globalenv instr_size p2)
      (prog_reloctables p2)
      (prog_sectable p2) Mem.empty = Some m0).
  { unfold alloc_sections in *.
    rewrite PTree.fold_spec in *.
    assert ((PTree.elements (prog_sectable p1)) = (PTree.elements (prog_sectable p2))).
    { exploit PTree.elements_extensional.
      intros. exploit (@pe_sectable fundef unit);eauto.
      auto. }
    unfold RelocProgram.section in *.
    rewrite H1 in *. clear H1.
    set (l := (PTree.elements (prog_sectable p2))) in *.
    assert (LEN: exists n, length l = n).
    { clear Heqo.
      induction l. exists O. auto.
      destruct IHl.
      exists (S x). simpl. auto. }
    clear H0.
    destruct LEN. generalize H0 Heqo. generalize x l m0.
    clear l H0 Heqo x. clear m0 m.
    induction x;intros.
    - rewrite length_zero_iff_nil in H0. subst.
      simpl in *. auto.
    - exploit LocalLib.length_S_inv;eauto.
      intros (l' & a1 & A1 & B1). subst.
      clear H0.
      rewrite fold_left_app in *.
      simpl in *.
      unfold alloc_section in Heqo at 1.
      destr_in Heqo.
      exploit IHx;eauto.
      intros. rewrite H0.
      simpl.
      exploit (@pe_reloctable_map fundef unit);eauto.
      intros. repeat rewrite H1 in *.
      (* program_equiv and globalenv  *)

      clear H1 H0.
      destr.
      + destruct (Mem.alloc_glob).
        destr.
        
        exploit store_init_data_bytes_match_ge.
        intros.
        eapply program_equiv_symbol_address;eauto.
        eauto.
        intros.
        rewrite <- H0. auto.
      + destruct (Mem.alloc_glob).
        destr.
        
        exploit store_init_data_bytes_match_ge.
        intros.
        eapply program_equiv_symbol_address;eauto.
        eauto.
        intros.
        rewrite <- H0. auto. }
  rewrite H1.
  clear H1 Heqo.
  unfold alloc_external_symbols in *.
  rewrite PTree.fold_spec in *.
  rewrite <- H0. f_equal.
  symmetry.
  eapply PTree.elements_extensional.
  eapply pe_symbtable. eauto.
Qed.


Section PRESERVATION. 
(** Transformation *)
Variable prog: program.
Variable tprog: elf_file.
Hypothesis TRANSF: match_prog prog tprog.


Let ge := RelocProgSemantics2.globalenv instr_size  prog.
Let tge := globalenv instr_size  tprog.

Lemma transf_initial_state: forall st1 rs,
    RelocProgSemantics2.initial_state instr_size  prog rs st1 ->
    exists st2, initial_state instr_size  tprog rs st2 /\ st1 = st2.
  intros st1 rs S1.
  exists st1. split;auto.
  unfold match_prog in TRANSF.
  exploit gen_reloc_elf_correct;eauto. intros (prog' & D1 & E1).  
  econstructor. eapply D1.
  inv S1.

  (* decode_prog_code_section equiv *)
  exploit decode_prog_code_section_correct;eauto.
  intros (p2' & D2 & E2). econstructor.
  eapply D2.

  (* init_mem equal *)
  exploit program_equiv_init_mem;eauto.

  (* initial_state_gen *)
  clear H H0 D2.
  inv H1. unfold rs0,ge0.
  assert ((RelocProg.prog_main prog'0) = (RelocProg.prog_main p2')).
  eapply pe_prog_main;eauto. rewrite H.
  erewrite program_equiv_symbol_address.
  econstructor;eauto. auto.
Qed.

Lemma eval_addrmode_match_ge: forall ge1 ge2 a rs (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs),
    eval_addrmode ge1 a rs = eval_addrmode ge2 a rs.
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

Lemma eval_builtin_arg_match_ge: forall rs sp m arg varg ge1 ge2 (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs),
        RelocProgSemanticsArchi.eval_builtin_arg preg ge1 rs sp m arg varg ->
        RelocProgSemanticsArchi.eval_builtin_arg preg ge2 rs sp m arg varg.
Proof.
  induction 2;try constructor;auto.
  rewrite MATCHGE in H. auto.
  rewrite MATCHGE. constructor.
Qed.

Lemma eval_builtin_args_match_ge: forall rs sp m args vargs ge1 ge2 (MATCHGE: forall i ofs, RelocProgGlobalenvs.Genv.symbol_address ge1 i ofs = RelocProgGlobalenvs.Genv.symbol_address ge2 i ofs),
        RelocProgSemanticsArchi.eval_builtin_args preg ge1 rs sp m args vargs ->
        RelocProgSemanticsArchi.eval_builtin_args preg ge2 rs sp m args vargs.
Proof.
  induction 2.
  - constructor.
  - econstructor.
    eapply eval_builtin_arg_match_ge;eauto.
    eauto.
Qed.

Lemma step_simulation: forall st1 st2 t,
    step instr_size ge st1 t st2 ->
    step instr_size tge st1 t st2.
Proof.
  intros.
  unfold ge,tge in *.
  exploit gen_reloc_elf_correct;eauto.
  unfold globalenv.
  intros (p' & D1 & E1).
  rewrite D1.
  unfold RelocProgSemantics2.globalenv in *.
  destr_in H.
  exploit decode_prog_code_section_correct;eauto.
  intros (p2' & D2 & E2). rewrite D2.

  2: {
    (* trivial cases *)
  destr.
  exploit decode_prog_code_section_correct. eapply program_equiv_sym in E1.
  eauto. eauto.
  intros (p2' & D2 & E2). congruence.

  assert ((empty_program1 prog) = (empty_program1 p')).
  unfold empty_program1.
  f_equal.
  apply pe_prog_defs;eauto.
  apply pe_prog_main;eauto.
  apply pe_prog_senv;eauto.
  rewrite <- H0. auto. }
  
  inv H.
  - eapply exec_step_internal;eauto.
    + unfold RelocProgGlobalenvs.Genv.find_ext_funct in *.
      destr. erewrite program_equiv_ext_funs1 in H1.
      eauto. eauto.
    + unfold RelocProgGlobalenvs.Genv.find_instr.
      erewrite program_equiv_instr_map.
      eauto. eapply program_equiv_sym. eauto.
    + apply program_equiv_sym in E2.
      destruct i;simpl in *;auto.
      1-27: try (erewrite program_equiv_symbol_address1;eauto).
      1-24: try (erewrite exec_load_match_ge;eauto;eapply program_equiv_symbol_address1;eauto).
      1-12: try (erewrite exec_store_match_ge;eauto;eapply program_equiv_symbol_address1;eauto).
      rewrite <- H3. do 3 f_equal.
      unfold eval_addrmode32.
      destruct a. f_equal.
      f_equal. destr.
      destruct p0. eapply program_equiv_symbol_address1;eauto.
      rewrite <- H3. do 3 f_equal.
      unfold eval_addrmode64.
      destruct a. f_equal.
      f_equal. destr.
      destruct p0. eapply program_equiv_symbol_address1;eauto.

  - eapply exec_step_builtin with (vargs:= vargs);eauto.
    + unfold RelocProgGlobalenvs.Genv.find_ext_funct in *.
      destr. erewrite program_equiv_ext_funs1 in H1.
      eauto. eauto.
    + unfold RelocProgGlobalenvs.Genv.find_instr.
      erewrite program_equiv_instr_map.
      eauto. eapply program_equiv_sym. eauto.
    + eapply eval_builtin_args_match_ge.
      eapply program_equiv_symbol_address1;eauto.
      eauto.
    + eapply external_call_symbols_preserved with (ge1:= (Genv.genv_senv (RelocProgSemantics.globalenv instr_size p))).
      simpl. erewrite pe_prog_senv.
      unfold Senv.equiv. split;eauto.
      auto. auto.
      
  - eapply exec_step_external;eauto.
    + unfold RelocProgGlobalenvs.Genv.find_ext_funct in *.
      destr. erewrite program_equiv_ext_funs1 in H1.
      eauto. eauto.
    + eapply external_call_symbols_preserved with (ge1:= (Genv.genv_senv (RelocProgSemantics.globalenv instr_size p))).
      simpl. erewrite pe_prog_senv.
      unfold Senv.equiv. split;eauto.
      auto. auto.
Qed.


Theorem transf_program_correct: forall rs,
    forward_simulation (RelocProgSemantics2.semantics instr_size  prog rs) (semantics instr_size  tprog rs).
Proof.
  intros.
  unfold match_prog in TRANSF.
  exploit gen_reloc_elf_correct;eauto.
  intros (p' & D1 & E1).
  
  eapply forward_simulation_step with (match_states:= fun (st1 st2: Asm.state) => st1 = st2).
  - simpl. unfold globalenv.
    unfold RelocProgSemantics2.globalenv.
    rewrite D1.
    destr.
    apply program_equiv_sym in E1.
    eapply decode_prog_code_section_correct in Heqr.
    destruct Heqr as (p2' & D2 & E2).
    rewrite D2.
    simpl. erewrite pe_prog_senv;eauto.
    auto.
    destr.
    eapply decode_prog_code_section_correct in Heqr0.
    destruct Heqr0 as (p2' & D2 & E2). rewrite Heqr in D2.
    congruence.
    auto. simpl. erewrite pe_prog_senv;eauto.
    apply program_equiv_sym. auto.
    
  - intros. 
    eapply transf_initial_state. auto.
  - simpl. intros. subst. auto.
  - intros. subst. exists s1'. split;auto.
    apply step_simulation. auto.
Qed.

End PRESERVATION.

End WITH_INSTR_SIZE.

Instance relocelfgen_transflink:
  TransfLink match_prog.
Admitted.
