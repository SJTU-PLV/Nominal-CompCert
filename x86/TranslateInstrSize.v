Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Asm RelocProg RelocProgram.
Require Import Hex compcert.encode.Bits Memdata Encode.
Require Import EncDecRet BPProperty.
Require Import TranslateInstr RelocBinDecode.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

(* TODO *)
Definition Instr_size_aux (i: Instruction) :=
  1.

Definition Instr_size (l : list Instruction) :=
  match l with
  | Override :: REX_WRXB w r x b :: i :: tl
  | REP :: REX_WRXB w r x b :: i :: tl
  | REPNZ :: REX_WRXB w r x b :: i :: tl =>
    2 + Instr_size_aux i
  | REX_WRXB _ _ _ _ :: i :: tl
  | Override :: i :: tl
  | REP :: i :: tl 
  | REPNZ :: i :: tl =>
    1 + Instr_size_aux i
  | i :: tl =>
    Instr_size_aux i
  | _ => 0
  end.

Lemma instr_eq_size: forall i1 i2,
    instr_eq i1 i2 -> instr_size_asm i1 = instr_size_asm i2.
Proof.
  Transparent instr_size_asm.
  intros. unfold instr_eq in H.
  destruct H. subst. auto.
  destruct Archi.ptr64 eqn:PTR.
  -
  destruct i1;try inv H;destruct i2;try inv H;cbn [instr_size_asm];auto.
  (* Pmovzl and Pmov_rr: Pmov_rr depend on Ptr64 *)
  admit.

  unfold rex_prefix_check_rr,rex_prefix_check_r.
  rewrite PTR. auto.

  -
    destruct i1;try inv H;destruct i2;try inv H;cbn [instr_size_asm];auto.
    
Admitted.


Lemma translate_instr_size: forall i e l l',
      translate_instr e i = OK l ->
      Instr_size (l ++ l') = instr_size_asm i.
Proof.
Admitted.


