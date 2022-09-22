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
  rewrite PTR. destr.
  apply andb_true_iff in Heqb. destruct Heqb.
  rewrite H. auto.
  apply andb_false_iff in Heqb. destruct Heqb.
  rewrite H. auto.
  rewrite H. auto.

  destruct H11. subst. auto.
  
  -
    destruct i1;try inv H;destruct i2;try inv H;cbn [instr_size_asm];auto.
    
Admitted.



