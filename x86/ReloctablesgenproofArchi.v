Require Import Coqlib Errors Maps.
Require Import Integers Floats AST RelocProgLinking Linking.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import Reloctablesgen ReloctablesgenArchi.
Require Import RelocProg RelocProgram RelocProgSemantics RelocProgSemantics1.
Require Import RelocProgSemanticsArchi1.
Require Import LocalLib AsmInject.
Import ListNotations.
Require AsmFacts.

Section WITH_INSTR_SIZE.

Variable instr_size : instruction -> Z.
Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.
Hypothesis instr_reloc_bound : forall i ofs, instr_reloc_offset i = OK ofs -> 0 < ofs < instr_size i.
Hypothesis id_eliminate_size_unchanged:forall i, instr_size i = instr_size (id_eliminate i).

Lemma lt_add_range:forall a b c,
    0 < b < c -> a < a + b < a + c.
Proof. 
  intros. lia.
Qed.

Lemma code_id_eliminate_size_unchanged:forall c,
    code_size instr_size (transl_code' c) = code_size instr_size c.
Proof.
  intros. unfold transl_code'.
  induction c;simpl;auto.
  rewrite IHc. rewrite <- id_eliminate_size_unchanged.
  auto.
Qed.

Lemma transl_instr_range: forall symbtbl ofs i e,
    transl_instr instr_size symbtbl ofs i = OK (Some e) ->
    ofs < e.(reloc_offset) < ofs + instr_size i.
  intros symbtbl ofs i e.
  generalize (instr_size_bound i). intros A.  
  unfold transl_instr.
  destruct i;simpl;intros;inv H.

  (* only solve Pmov_rs *)  
  monadInv H1.
  unfold compute_instr_abs_relocentry in *. monadInv EQ.
  destr_match_in EQ1;inv EQ1;simpl;eapply lt_add_range; auto.
            
  1-42: try (destruct a;destruct const;try destruct p;inv H1).
  1-42: try (monadInv H0;
             destruct Archi.ptr64;
        unfold compute_instr_abs_relocentry in *;
       unfold compute_instr_disp_relocentry in *;
       unfold compute_instr_rel_relocentry in *;
       repeat (monadInv EQ));
    try (destr_match_in EQ1;inv EQ1;simpl).

  1-79: try (eapply lt_add_range; auto).

  1-42 : try(destr_match_in EQ2;inv EQ2;simpl;
             eapply lt_add_range; auto).
  
  (* Pjmp_s *)
  destruct Archi.ptr64. monadInv H1.
  unfold compute_instr_rel_relocentry in *.
  monadInv EQ.
  destr_match_in EQ2;inv EQ2;simpl;eapply lt_add_range; auto.
  inv H1. simpl. eapply lt_add_range; auto.
  (* Pjmp_m *)
  destruct base. monadInv H0.
  unfold compute_instr_abs_relocentry in *.
  monadInv EQ. 
  destr_match_in EQ1;inv EQ1;simpl;eapply lt_add_range; auto.
  destruct ofs0. monadInv H0.
  unfold compute_instr_abs_relocentry in *.
  monadInv EQ.
  destr_match_in EQ1;inv EQ1;simpl;eapply lt_add_range; auto.
  try (monadInv H0;
             destruct Archi.ptr64;
        unfold compute_instr_abs_relocentry in *;
       unfold compute_instr_disp_relocentry in *;
       unfold compute_instr_rel_relocentry in *;
       repeat (monadInv EQ));
    try (destr_match_in EQ1;inv EQ1;simpl).
  destr_match_in EQ2;inv EQ2;simpl;eapply lt_add_range; auto.
  eapply lt_add_range; auto.
  (* call_s *)
  destruct Archi.ptr64.
  monadInv H1. unfold compute_instr_rel_relocentry in *. repeat (monadInv EQ). destr_match_in EQ2. inv EQ2.
  simpl. 
  eapply lt_add_range; auto. inv EQ2.
  inv H1.   simpl. 
  eapply lt_add_range; auto.
  (* Pbuiltin *)
  destr_match_in H1.
  inv H1. inv H1.
  (* Pmovw_rm *)
  destruct ad;destruct const;try destruct p;inv H1.
  monadInv H0. destruct Archi.ptr64.
  unfold compute_instr_rel_relocentry in *.
  monadInv EQ. destr_match_in EQ2. inv EQ2. simpl.
  eapply lt_add_range; auto.
  inv EQ2.
  unfold compute_instr_abs_relocentry in *.
  monadInv EQ. destr_match_in EQ1. inv EQ1. simpl.
  eapply lt_add_range; auto. inv EQ1.
Qed.

Lemma transl_instr_consistency: forall i symbtbl ofs e,
    transl_instr instr_size symbtbl ofs i = OK (Some e) ->
    rev_id_eliminate (reloc_symb e) (id_eliminate i) = i.
Proof.
  intros i symbtbl ofs e.
  destruct i;simpl;auto;
    unfold transl_instr;simpl;intros H;repeat (monadInv H);
      unfold compute_instr_disp_relocentry in *;
      destruct Archi.ptr64;
      unfold compute_instr_abs_relocentry in *;      
    unfold compute_instr_rel_relocentry in *;
    repeat (monadInv EQ);
    try (destruct (symbtbl ! id);inv EQ1;simpl;auto); (* no addrmode finish *)
    try (destruct a;destruct const;try destruct p;try congruence);
  try (monadInv H;
       unfold compute_instr_abs_relocentry in *;
       unfold compute_instr_disp_relocentry in *;
       unfold compute_instr_rel_relocentry in *;
       repeat (monadInv EQ);
       try (destr_in EQ1;inv EQ1;simpl;auto)).

  1-45: try (destruct PTree.get;inv EQ2;simpl;auto).
  1-4 : simpl;auto.
  (* Pjmp_m *)
  destruct base. monadInv H.
  monadInv EQ. destruct PTree.get;inv EQ1;simpl;auto.
  destruct ofs0. monadInv H.
  monadInv EQ. destruct PTree.get;inv EQ1;simpl;auto.
  monadInv H. monadInv EQ.
  destruct PTree.get;inv EQ2;simpl;auto.
  destruct base. monadInv H.
  monadInv EQ. destruct PTree.get;inv EQ1;simpl;auto.
  destruct ofs0. monadInv H.
  monadInv EQ. destruct PTree.get;inv EQ1;simpl;auto.
  monadInv H. monadInv EQ.
  destruct PTree.get;inv EQ1;simpl;auto.

  (* Pmovw *)
  destruct ad;destruct const;try destruct p;try congruence.
  monadInv H. monadInv EQ. destruct PTree.get;inv EQ2;simpl;auto.
  destruct ad;destruct const;try destruct p;try congruence.
  monadInv H. monadInv EQ. destruct PTree.get;inv EQ1;simpl;auto.
  
Qed.

Lemma id_eliminate_unchanged:forall i symbtbl ofs,
    transl_instr instr_size symbtbl ofs i = OK None ->
    id_eliminate i = i.
Proof.
  intros i symbtl ofs.
  destruct i;simpl;auto;
  unfold transl_instr;simpl;intros;repeat (monadInv H);repeat (destr_in H);repeat monadInv H1.
Qed.

End WITH_INSTR_SIZE.
