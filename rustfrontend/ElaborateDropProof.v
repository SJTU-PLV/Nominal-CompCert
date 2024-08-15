Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Linking.
Require Import Rusttypes.
Require Import RustlightBase RustIR  RustOp.
Require Import Errors.
Require Import LanguageInterface cklr.CKLR cklr.Inject cklr.InjectFootprint.

Require Import ElaborateDrop. 
Require Import RustIRsem RustIRown.

Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope gensym_monad_scope.

Record match_prog (p tp: RustIR.program) : Prop := {
   match_prog_skel:
    erase_program tp = erase_program p
}.

Section MATCH_PROGRAMS.
Variable p: RustIR.program.
Variable tp: RustIR.program.
Hypothesis TRANSL: match_prog p tp.

Section INJECT.

Variable j: meminj.
Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
Hypothesis sematch: Genv.match_stbls j se tse.

Theorem is_internal_match:
  forall v tv (f tf: RustIR.fundef),
  fundef_is_internal tf = fundef_is_internal f ->
  Val.inject j v tv ->
  v <> Vundef ->
  Genv.is_internal (globalenv tse tp) tv = Genv.is_internal (globalenv se p) v.
Proof.
Admitted. 
   
  
End INJECT.
End MATCH_PROGRAMS.





Section PRESERVATION.

Variable prog: RustIR.program.
Variable tprog: RustIR.program.
(* Let build_ctx := build_clgen_env p tp. *)


Variable w: inj_world. 

Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
Variable dropflags: PTree.t (list (place * ident)).

Let ge := globalenv se prog.
Let tge := globalenv tse tprog.


Inductive match_states: state -> RustIRsem.state -> Prop :=
  | match_regular_state:
      forall f s k e own m tf ts tk te tm j
      (TRS: transl_stmt dropflags s = ts)
      (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm)))
      (MINJ: Mem.inject j m tm),
      match_states (State f s k e own m) (RustIRsem.State tf ts tk te tm). 


Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus RustIRsem.step tge S1' t S2' /\ match_states S2 S2'.
Proof. 
  induction 1; intros; inv MS. 
  - eexists. split. eapply plus_one. 
Admitted. 


End PRESERVATION.

Theorem transl_program_correct prog tprog:
   match_prog prog tprog ->
   forward_simulation (cc_c inj) (cc_c inj) (semantics prog) (RustIRsem.semantics tprog).
Proof.
    fsim eapply forward_simulation_plus; simpl in *. 
    - inv MATCH. simpl. auto. 
    - simpl. intros. destruct Hse, H. simpl. exploit is_internal_match; eauto. 
    - admit. 
    - admit. 
    - admit. 
    - eapply step_simulation; auto.   
    Admitted.   
