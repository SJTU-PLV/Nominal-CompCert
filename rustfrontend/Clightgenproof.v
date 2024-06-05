Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import LanguageInterface.
Require Import AST.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import Clight.
Require Import RustlightBase RustIR.
Require Import Errors.
Require Import Clightgen.

Import ListNotations.

(** Correctness proof for the generation of Clight *)


Variable match_prog: RustIR.program -> Clight.program -> Prop. (* TODO *)



(* Simulation relation *)

Variable ce: composite_env.
Variable tce: Ctypes.composite_env.
Variable dropm: PTree.t ident.
Hypothesis match_composites: composite_env -> Ctypes.composite_env -> Prop.

Inductive match_cont : RustIR.cont -> Clight.cont -> Prop :=
| match_Kstop: match_cont RustIR.Kstop Clight.Kstop
| match_Kseq: forall s ts k tk g g',
    (* To avoid generator, we need to build the spec *)
    transl_stmt ce tce dropm s g = Res ts g' ->
    match_cont k tk ->
    match_cont (RustIR.Kseq s k) (Clight.Kseq ts tk)
(** TODO  *)
.

Definition match_env (f: meminj) (e: env) (te: Clight.env) : Prop :=
  (* me_mapped in Simpllocalproof.v *)
  forall id b ty, e!id = Some (b, ty) ->
          exists tb, te!id = Some (tb, to_ctype ty) /\ f b = Some (tb, 0).
                    

Inductive match_states: RustIR.state -> Clight.state -> Prop :=
| match_states_regular: forall f tf s ts k tk m tm e te le j g1 g2,
    (* Ignore the generators here *)
    transl_function ce tce dropm f = OK tf ->
    transl_stmt ce tce dropm s g1 = Res ts g2 ->
    (* match continuation *)
    match_cont k tk ->
    (* we need to consider that tm may contains more block for its call of drop glue *)
    (* use injp_acc ? *)
    Mem.inject j m tm ->
    (* local environments are the same? *)
    match_env j e te ->
    match_states (RustIR.State f s k e m) (Clight.State tf ts tk te le tm)

.


Theorem transl_program_correct prog tprog:
  match_prog prog tprog ->
  forward_simulation cc_id cc_id (RustIR.semantics prog) (Clight.semantics1 tprog).
Admitted.
