Require Import Coqlib.
Require Import Errors.
Require Import Values.
Require Import AST Errors.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep SmallstepLinkingSafe.
Require Import LanguageInterface Invariant.
Require Import Rusttypes.
Require Import RustIR BorrowCheckPolonius.

Section BORROWCK.

Variable p tp: program.
Variable se: Genv.symtbl.
Hypothesis BORCHK: borrow_check_program p = OK tp.
Hypothesis VALIDSE: Genv.valid_for (erase_program p) se.

Let L1 := semantics p se.
Let L2 := semantics tp se.


Lemma sound_state_safe: forall s,
    partial_safe L1 s ->
    safe L2 s.
Admitted.

End BORROWCK.


Lemma borrow_check_safe: forall p tp,
    borrow_check_program p = OK tp ->
    module_safe (semantics p) wt_c wt_c partial_safe ->
    module_safe (semantics tp) wt_c wt_c safe.
Proof.
  intros p tp BORCHK MSAFE.
  red. intros w se VALIDSE SYMBINV.
Admitted.
    
