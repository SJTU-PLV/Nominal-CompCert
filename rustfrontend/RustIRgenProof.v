Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Linking.
Require Import Rusttypes.
Require Import Errors.
Require Import LanguageInterface CKLR Inject InjectFootprint.
Require Import RustIR Rustlight RustOp RustIRgen.
Require Import RustIRown.
Require Import Rustlightown.    


Section TRANSLATION.
(* Variable ce: composite_env. *)

Variable prog: program.
Variable tprog: RustIR.program.


Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.

Let ge := globalenv se prog.
Let tge := RustIR.globalenv tse tprog.

Record match_prog (p : Rustlight.program) (tp : RustIR.program) : Prop := {
  match_prog_main:
    tp.(prog_main) = p.(prog_main);
  match_prog_public:
    tp.(prog_public) = p.(prog_public);
  match_prog_skel:
    erase_program tp = erase_program p;
  match_prog_defs:
    list_norepet (prog_defs_names p)
}.

Inductive match_states: Rustlightown.state -> RustIRown.state -> Prop := 
  | match_regular_state: 
    forall f s k e own m tf ts tk te town tm ce params_drops oretv vars j
    (MSTMT: transl_stmt ce params_drops oretv s vars = ts)
    (MINJ: Mem.inject j m tm),
    match_states (State f s k e own m) (RustIRown.State tf ts tk te town tm). 



Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus RustIRown.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
  - simpl in *. simpl.   inv MSTMT.  . split. eapply plus_one. destruct (own_type ce (typeof_place p)) eqn:A. 
  + admit. 
    + eapply RustIRown.step_assign; eauto.  


Theorem transl_program_correct prog tprog:
   match_prog prog tprog ->
   forward_simulation (cc_rs injp) (cc_rs injp) (semantics prog) (RustIRown.semantics tprog).
Proof.
  fsim eapply forward_simulation_plus. 
  - inv MATCH. auto. 
  - intros. inv MATCH. destruct Hse, H. simpl in *. admit. 
  - admit. 
  - admit.  
  - simpl. admit. 
  - admit. 

    

