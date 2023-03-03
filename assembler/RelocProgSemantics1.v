(** * The semantics of relocatable program using both the symbol and the relocation tables *)

(** The key feature of this semantics: it uses the relocation tables 
for each sections to recover the id in the code section. 
The data sections are unchanged in the generation of relocation tables.
Then we use the RelocProgsemantics of the decoded program as the semantics 
of the source program *)

Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgram Globalenvs.
Require Import Locations Stacklayout Conventions.
Require Import Linking Errors.
Require Import RelocProgSemantics Reloctablesgen RelocProgSemanticsArchi RelocProgSemanticsArchi1.
Require Import RelocProgGlobalenvs LocalLib.
Import ListNotations.


Section WITH_INSTR_SIZE.
  Variable instr_size : instruction -> Z.


Definition rev_acc_code (r:code*Z*reloctable) i :=
  let '(c,ofs,reloctbl) := r in
  match reloctbl with
  | [] =>
    (c++[i], ofs + instr_size i, [])
  | e :: reloctbl' =>
    let ofs' := ofs + instr_size i in
    if Z.leb ofs e.(reloc_offset) && Z.ltb e.(reloc_offset) ofs' then
      (c++[rev_id_eliminate e.(reloc_symb) e.(reloc_addend) i], ofs', reloctbl')
    else
      (c++[i], ofs', reloctbl)
  end.


Definition rev_transl_code (reloctbl: reloctable) (c:code) :=
  fst (fst (fold_left rev_acc_code c ([],0,reloctbl))).

Definition rev_section {D:Type} (reloctbl_map: reloctable_map) (id:ident) (sec:RelocProg.section instruction D) :=
  match sec with
  | sec_text c =>
    match reloctbl_map ! id with
    | Some reloctbl =>
      sec_text (rev_transl_code reloctbl c)
    | None => sec
    end
  | _ => sec
  end.

Definition decode_program {D: Type} (p: RelocProg.program fundef unit instruction D) :=
  {| prog_defs := prog_defs p;
     prog_public := prog_public p;
     prog_main := prog_main p;
     prog_sectable := PTree.map (rev_section p.(prog_reloctables)) p.(prog_sectable);
     prog_symbtable := prog_symbtable p;
     prog_reloctables := p.(prog_reloctables);
     prog_senv := prog_senv p;
  |}.

Definition globalenv {D: Type} (p: RelocProg.program fundef unit instruction D) := globalenv instr_size (decode_program p).

Inductive initial_state (p:program) (rs:regset) (st:state) : Prop :=
| initial_state_intro: forall p',
    p' = decode_program p ->
    RelocProgSemantics.initial_state instr_size p' rs st ->
    initial_state p rs st.

Definition semantics (p:program) (rs:regset) :=
  Semantics_gen (RelocProgSemanticsArchi.step instr_size)
                (initial_state p rs)
                (final_state)
                (globalenv p)
                (Genv.genv_senv (globalenv p)).


  Ltac rewrite_hyps :=
  repeat
    match goal with
      H1 : ?a = _, H2: ?a = _ |- _ => rewrite H1 in H2; inv H2
    end.
  

Lemma semantics_determinate: forall p rs, determinate (semantics p rs).
Proof.
  intros; constructor; simpl; intros.
  - unfold globalenv in *. exploit semantics_determinate_step. eapply H. eapply H0.
    unfold decode_program. simpl. auto.
  - (* trace length *)
    red; intros; inv H; simpl.
    lia.
    eapply external_call_trace_length; eauto.
  - (* initial states *)
    inv H; inv H0. inv H2; inv H1. rewrite_hyps.
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
  red. intros.
  inv H; simpl. lia.
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
    edestruct external_call_receptive as (vres2 & m2 & EC2); eauto.
    (* eexists. eapply RelocProgSemantics.exec_step_builtin; eauto. *)
    (* edestruct external_call_receptive as (vres2 & m2 & EC2); eauto. *)
    eexists. eapply exec_step_external; eauto.
  - eapply reloc_prog_single_events; eauto.  
Qed.

End WITH_INSTR_SIZE.
