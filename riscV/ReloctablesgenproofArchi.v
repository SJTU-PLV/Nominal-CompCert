Require Import Coqlib Errors Maps.
Require Import Integers Floats AST RelocProgLinking Linking.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import Reloctablesgen ReloctablesgenArchi.
Require Import RelocProg RelocProgram RelocProgSemantics RelocProgSemantics1 RelocProgGlobalenvs.
Require Import Memory MemoryAgree.
Require Import RelocProgSemanticsArchi RelocProgSemanticsArchi1.
Require Import LocalLib AsmInject.
Import ListNotations.

Local Open Scope error_monad_scope.

Section WITH_INSTR_SIZE.

Variable instr_size : instruction -> Z.
Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.


Definition instr_eq (i1 i2: instruction) :=  i1=i2.

Lemma instr_eq_refl: forall i, instr_eq i i.
Proof.
  unfold instr_eq.
  auto.
Qed.


Lemma transl_instr_consistency: forall i ofs e,
    transl_instr instr_size ofs i = OK (Some e) ->
    instr_eq (rev_id_eliminate (reloc_symb e) (reloc_addend e) (id_eliminate i)) i.
Proof.
  intros.
  unfold instr_eq. destruct i;simpl in *;auto;inv H.
  1-15: destr_match_in H1;inv H1;simpl;try rewrite Ptrofs.repr_signed; auto.
  1-2: destruct Archi.ptr64;simpl;auto.
  destr_match_in H1;inv H1;simpl;try rewrite Ptrofs.repr_signed; auto.
Qed.

Lemma id_eliminate_unchanged:forall i ofs,
    transl_instr instr_size ofs i = OK None ->
    id_eliminate i = i.
Proof.
  intros i ofs.
  destruct i;simpl;auto;
  unfold transl_instr;simpl;intros;repeat (monadInv H);repeat (destr_in H);repeat monadInv H1.
Qed.

Lemma exec_instr_eq: forall (instr_size : instruction -> Z) (i i': instruction) (rs : regset) 
                       (m : mem) (ge tge : Genv.t),
    (forall (id : ident) (ofs : ptrofs), Genv.symbol_address ge id ofs = Genv.symbol_address tge id ofs) ->
    instr_eq i' i ->
    exec_instr instr_size ge i rs m = exec_instr instr_size tge i' rs m.
Proof.
  intros.
  unfold instr_eq in H0.
  destr_in H0;subst;try eapply exec_instr_refl;auto.
Qed.

End WITH_INSTR_SIZE.
