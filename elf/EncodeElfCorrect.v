Require Import ElfBytesSemantics.
Require Import Smallstep.
Require Import EncodeRelocElf DecodeRelocElf.
Require Import Asm EncDecRet RelocElf.
Require Import Coqlib Errors.

Require Import RelocElfgenproof.
Require Import LocalLib.


Definition match_prog : elf_file -> (list Integers.Byte.int * Asm.program * Globalenvs.Senv.t) -> Prop :=
  fun p p' => encode_elf_file p = OK p'.

Section WITH_INSTR_SIZE.

Variable instr_size : instruction -> Z.
Variable Instr_size : list Instruction -> Z.

Section PRES.

Variable prog: elf_file.
Variable tprog_bytes: list Integers.Byte.int.
Variable tprog_prog: Asm.program.
Variable tprog_senv: Globalenvs.Senv.t.

Hypothesis TRANSF: match_prog prog (tprog_bytes, tprog_prog, tprog_senv).

Lemma encode_elf_correct:
  forall rs, forward_simulation (RelocElfSemantics.semantics instr_size Instr_size prog rs)
                                (ElfBytesSemantics.semantics instr_size Instr_size tprog_bytes tprog_prog tprog_senv rs).
Proof.
  unfold match_prog in TRANSF.
  unfold ElfBytesSemantics.semantics. intros.
  erewrite decode_encode_elf_file; eauto.
  apply forward_simulation_step with (match_states := eq); intuition subst; eauto.
Qed.

End PRES.

End WITH_INSTR_SIZE.
