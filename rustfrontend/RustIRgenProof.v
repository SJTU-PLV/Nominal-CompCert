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

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope error_monad_scope.

(** Semantics preservation of the generation of RustIR programs from
Rustlight programs. The key parts of the proof are to 1. relate the
semantics drops expressed in the continuation to the drop statements
explicitly inserted in the program; 2. handle the discrepency between
the source (mem, env, own_env) and the target (mem, env, own_env) due
to the new generated return variable which is used to store the return
value before dropping all the in-scope variables and parameters. *)

Definition match_glob (ctx: composite_env) (gd: globdef Rustlight.fundef type) (tgd: globdef RustIR.fundef type) : Prop :=
  match gd, tgd with
  | Gvar v1, Gvar v2 =>
      match_globvar eq v1 v2
  | Gfun fd1, Gfun fd2 =>
      transl_fundef ctx fd1 = fd2
  | _, _ => False
  end.

Record match_prog (p : Rustlight.program) (tp : RustIR.program) : Prop := {
    match_prog_main:
    tp.(prog_main) = p.(prog_main);
    match_prog_public:
    tp.(prog_public) = p.(prog_public);
    match_prog_types:
    tp.(prog_types) = p.(prog_types);
    match_prog_defs:
    list_forall2 (fun '(id1, gd) '(id2, tgd) => id1 = id2 /\ match_glob p.(prog_comp_env) gd tgd) p.(prog_defs) tp.(prog_defs);
    match_dropm:
    generate_dropm p = RustIR.generate_dropm tp;
    match_prog_skel:
    erase_program tp = erase_program p;
}.


Section PRESERVATION.


Variable prog: program.
Variable tprog: RustIR.program.

Hypothesis TRANSL: match_prog prog tprog.
Variable w: inj_world.

Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
(* Variable dropflags: PTree.t (list (place * ident)). *)

Let ge := globalenv se prog.
Let tge := RustIR.globalenv tse tprog.

Inductive match_states: Rustlightown.state -> RustIRown.state -> Prop := 
| match_regular_state: 
  forall f s k e own m tf ts tk te town tm oretv vars j
    (* It is no need to relate two functions *)
    (TRSTMT: transl_stmt ge f.(fn_params) oretv s vars = ts)
    (* The in-scope variables collected in transl_stmt are the same as
    those collected in the continuation *)
    (CONTVARS: cont_vars k = vars)
    (* relation between (e, own) and (te, town) *)
    (MENV: 
    (MINJ: Mem.inject j m tm),
    match_states (State f s k e own m) (RustIRown.State tf ts tk te town tm) 
| match_dropinsert_state:
  forall f l dk k le own m tf ts tk te town tm j
    (MINJ: Mem.inject j m tm),
    (* Dropinsert f l dk k le own m *)
    match_states (Dropinsert f l dk k le own m) (RustIRown.State tf ts tk te town tm).




Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus RustIRown.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros. 
  - inv MS. simpl. destruct (own_type (prog_comp_env prog) (typeof_place p)) eqn:A. 
    + eexists. split. eapply plus_one. eapply RustIRown.step_seq. 
      econstructor. eauto. 
    + eexists. split. eapply plus_one. econstructor; eauto.       
      
  Admitted. 

(* Theorem transl_program_correct prog tprog:
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

    

