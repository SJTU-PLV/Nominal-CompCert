Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Globalenvs.
Require Import Asm RelocProg RelocProgram.
Require Import Hex compcert.encode.Bits Memdata Encode.
Require Import BPProperty.
Require Import TranslateInstr.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

Definition decode_instr l :=
  match l with
  | i :: l' =>
      do i' <- decode_instr' i;
      OK (i', l')
  | _ => Error (msg "impossible")
  end.

Theorem translate_instr_consistency_aux: forall i i',
    translate_instr' i = OK i' ->
    decode_instr' i' = OK i.
Proof.
Admitted.

Theorem translate_instr_consistency: forall i li l,
    translate_instr i = OK li ->
    decode_instr (li++l) = OK (i,l).
Proof.
  unfold translate_instr,decode_instr.
  intros. monadInv H. simpl.
  erewrite translate_instr_consistency_aux;eauto. simpl. auto.
Qed.
