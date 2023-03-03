(** * The semantics of relocatable program using only the symbol table *)

(** The key feature of this semantics: it uses mappings from the ids
    of global symbols to memory locations in deciding their memory
    addresses. These mappings are caculated by using the symbol table.
    *)

Require Import Coqlib Maps AST Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgram Globalenvs.
Require Import Locations Stacklayout Conventions.
Require Import Linking Errors.
Require Import LocalLib.
Require Import RelocProgGlobalenvs RelocProgSemanticsArchi.


Section WITH_INSTR_SIZE.
  Variable instr_size : instruction -> Z.
  Let exec_instr:= exec_instr instr_size.

Lemma code_size_app:
  forall c1 c2,
    code_size instr_size (c1 ++ c2) = code_size instr_size c1 + code_size instr_size c2.
Proof.
  induction c1; simpl; intros; rewrite ? IHc1; lia.
Qed.


(** Small step semantics *)


(** New defined eval_builtin_arg for Genv.t *)
Section EVAL_BUILTIN_ARG.

Variable A: Type.

Variable ge: Genv.t.
Variable e: A -> val.
Variable sp: val.
Variable m:mem. 

Inductive eval_builtin_arg: builtin_arg A -> val -> Prop :=
  | eval_BA: forall x,
      eval_builtin_arg (BA x) (e x)
  | eval_BA_int: forall n,
      eval_builtin_arg (BA_int n) (Vint n)
  | eval_BA_long: forall n,
      eval_builtin_arg (BA_long n) (Vlong n)
  | eval_BA_float: forall n,
      eval_builtin_arg (BA_float n) (Vfloat n)
  | eval_BA_single: forall n,
      eval_builtin_arg (BA_single n) (Vsingle n)
  | eval_BA_loadstack: forall chunk ofs v,
      Mem.loadv chunk m (Val.offset_ptr sp ofs) = Some v ->
      eval_builtin_arg (BA_loadstack chunk ofs) v
  | eval_BA_addrstack: forall ofs,
      eval_builtin_arg (BA_addrstack ofs) (Val.offset_ptr sp ofs)
  | eval_BA_loadglobal: forall chunk id ofs v,
      Mem.loadv chunk m  (Genv.symbol_address ge id ofs) = Some v ->
      eval_builtin_arg (BA_loadglobal chunk id ofs) v
  | eval_BA_addrglobal: forall id ofs,
      eval_builtin_arg (BA_addrglobal id ofs) (Genv.symbol_address ge id ofs)
  | eval_BA_splitlong: forall hi lo vhi vlo,
      eval_builtin_arg hi vhi -> eval_builtin_arg lo vlo ->
      eval_builtin_arg (BA_splitlong hi lo) (Val.longofwords vhi vlo)
  | eval_BA_addptr: forall a1 a2 v1 v2,
      eval_builtin_arg a1 v1 ->
      eval_builtin_arg a2 v2 ->
      eval_builtin_arg (BA_addptr a1 a2) (if Archi.ptr64 then Val.addl v1 v2 else Val.add v1 v2).

                       
Definition eval_builtin_args (al: list (builtin_arg A)) (vl: list val) : Prop :=
  list_forall2 eval_builtin_arg al vl.

Lemma eval_builtin_arg_determ:
  forall a v, eval_builtin_arg a v -> forall v', eval_builtin_arg a v' -> v' = v.
Proof.
  induction 1; intros v' EV; inv EV; try congruence.
  f_equal; eauto.
  destruct Archi.ptr64;f_equal;auto.
Qed.

Lemma eval_builtin_args_determ:
  forall al vl, eval_builtin_args al vl -> forall vl', eval_builtin_args al vl' -> vl' = vl.
Proof.
  induction 1; intros v' EV; inv EV; f_equal; eauto using eval_builtin_arg_determ.
Qed.

 
End EVAL_BUILTIN_ARG.

Hint Constructors eval_builtin_arg: barg.

(* same lemmas as the in Events *)
Section EVAL_BUILTIN_ARG_PRESERVED.

Variables A: Type.
Variable ge1: Genv.t.
Variable ge2: Genv.t.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

Lemma eval_builtin_arg_preserved:
  forall a v, eval_builtin_arg A ge1 e sp m a v -> eval_builtin_arg A ge2 e sp m a v.
Proof.
   assert (EQ: forall id ofs, Genv.symbol_address ge2 id ofs = Genv.symbol_address ge1 id ofs).
  { unfold Genv.symbol_address; simpl; intros. rewrite symbols_preserved; auto. }
  induction 1; eauto with barg. rewrite <- EQ in H; eauto with barg. rewrite <- EQ; eauto with barg.
Qed.

Lemma eval_builtin_args_preserved:
  forall al vl, eval_builtin_args A ge1 e sp m al vl -> eval_builtin_args A ge2 e sp m al vl.
Proof.
  induction 1; constructor; auto; eapply eval_builtin_arg_preserved; eauto.
Qed.

End EVAL_BUILTIN_ARG_PRESERVED.

Inductive initial_state (prog: program) (rs: regset) (s: state): Prop :=
| initial_state_intro: forall m,
    init_mem instr_size prog = Some m ->
    initial_state_gen instr_size prog rs m s ->
    initial_state prog rs s.

Definition semantics (p: program) (rs: regset) :=
  Semantics_gen (step instr_size) (initial_state p rs) final_state (globalenv instr_size p) (Genv.genv_senv (globalenv instr_size p)).

(** Determinacy of the [Asm] semantics. *)

  Ltac rewrite_hyps :=
  repeat
    match goal with
      H1 : ?a = _, H2: ?a = _ |- _ => rewrite H1 in H2; inv H2
    end.
  

Lemma semantics_determinate: forall p rs, determinate (semantics p rs).
Proof.
  intros; constructor; simpl; intros.
- eapply semantics_determinate_step;eauto.
- (* trace length *)
  red; intros; inv H; simpl.
  lia.
  eapply external_call_trace_length; eauto.
  (* eapply external_call_trace_length; eauto. *)
- (* initial states *)
  inv H; inv H0. rewrite_hyps.
  eapply initial_state_gen_determinate;eauto.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. red; intros; red; intros. inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

Theorem reloc_prog_single_events p rs:
  single_events (semantics p rs).
Proof.
  red. simpl. intros s t s' STEP.
  inv STEP; simpl. lia.
  eapply external_call_trace_length; eauto.
  (* eapply external_call_trace_length; eauto. *)
Qed.

Theorem reloc_prog_receptive p rs:
  receptive (semantics p rs).
Proof.
  split.
  - simpl. intros s t1 s1 t2 STEP MT.
    inv STEP.
    inv MT. eexists. eapply exec_step_internal; eauto.
    (* edestruct external_call_receptive as (vres2 & m2 & EC2); eauto. *)
    (* eexists. eapply exec_step_builtin; eauto. *)
    edestruct external_call_receptive as (vres2 & m2 & EC2); eauto.
    eexists. eapply exec_step_external; eauto.
  - eapply reloc_prog_single_events; eauto.
Qed.



End WITH_INSTR_SIZE.
