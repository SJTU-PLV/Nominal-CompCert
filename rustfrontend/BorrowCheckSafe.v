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

Variable p: program.
Variable w: inv_world wt_c.
Variable se: Genv.symtbl.
Hypothesis VALIDSE: Genv.valid_for (erase_program p) se.
Hypothesis INV: symtbl_inv wt_c w se.
Let L := semantics p se.
Let ge := globalenv se p.

Variable sound_state: state -> Prop.

Lemma sound_state_no_mem_error: forall s,
    step_mem_error ge s -> sound_state s -> False .
Admitted.

(** Specific definition of partial safe *)
Definition partial_safe (s: state) : Prop :=
  safe L s \/ step_mem_error ge s.

Lemma borrow_check_lts_safe:
    borrow_check_program p = OK tt ->
    lts_safe se (semantics p se) wt_c wt_c (fun _ => partial_safe) w ->
    lts_safe se (semantics p se) wt_c wt_c safe w.
Proof.
  intros BORCHK PSAFE. inv PSAFE.  
  constructor.
  - simpl in *. intros s t s' STEP.
    generalize (step_safe _ _ _ STEP). intros PSAFE.
    destruct PSAFE as [|MEMERROR]. auto.
    
    
Admitted.

End BORROWCK.



(* Lemma borrow_check_safe: forall p, *)
(*     borrow_check_program p = OK tt -> *)
(*     module_safe (semantics p) wt_c wt_c partial_safe -> *)
(*     module_safe (semantics p) wt_c wt_c safe. *)
(* Proof. *)
(*   intros p BORCHK MSAFE. *)
(*   red. intros w se VALIDSE SYMBINV. *)
(* Admitted. *)
    
