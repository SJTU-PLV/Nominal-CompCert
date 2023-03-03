Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Asm RelocProg RelocProgram.
Require Import Hex compcert.encode.Bits Memdata Encode.
Require Import LocalLib.
Require Import ReloctablesgenArchi RelocProgSemanticsArchi1.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.


Lemma rev_id_eliminate_size: forall i id addend, instr_size_real i = instr_size_real (rev_id_eliminate id addend i).
Proof.
  destruct i;intros;cbn;try destr;auto.
Qed.

Lemma id_eliminate_size_unchanged:forall i, instr_size_real i = instr_size_real (id_eliminate i).
Proof.
  destruct i;simpl;auto;try destr;auto.
Qed.

Section WITH_INSTR_SIZE.

Variable instr_size : instruction -> Z.
Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.

Lemma transl_instr_range': forall ofs i e,
    transl_instr instr_size ofs i = OK (Some e) ->
    ofs <= e.(reloc_offset) < ofs + instr_size i.
Proof.
  intros ofs i e.
  generalize (instr_size_bound i). intros A.
  unfold transl_instr.
  destruct i;intros H;inv H.
  1-15: destr_match_in H11;inv H11;simpl;try lia.
  1-2: simpl;lia.
  destr_match_in H11. inv H11. simpl;lia.
  inv H11.
Qed.

End WITH_INSTR_SIZE.

Lemma transl_instr_range: forall ofs i e,
    transl_instr instr_size_real ofs i = OK (Some e) ->
    ofs <= e.(reloc_offset) < ofs + instr_size_real i.
Proof.
  eapply (transl_instr_range' instr_size_real instr_size_bound_real).
Qed.
