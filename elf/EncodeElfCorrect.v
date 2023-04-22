Require Import ElfBytesSemantics.
Require Import Smallstep.
Require Import EncodeRelocElf DecodeRelocElf.
Require Import Asm EncDecRet RelocElf.
Require Import Coqlib Errors.
Require Import Linking RelocElfLinking.
Require Import LocalLib.


Definition match_prog : elf_file -> (list Integers.Byte.int * Asm.program * Globalenvs.Senv.t) -> Prop :=
  fun p p' => encode_elf_file p = OK p'.

Definition transf_program_match :
  forall p tp, encode_elf_file p = OK tp -> match_prog p tp.
Proof.
  auto.
Qed.


Section WITH_INSTR_SIZE.

Variable instr_size : instruction -> Z.

Section PRES.

Variable prog: elf_file.
Variable tprog_bytes: list Integers.Byte.int.
Variable tprog_prog: Asm.program.
Variable tprog_senv: Globalenvs.Senv.t.

Hypothesis TRANSF: match_prog prog (tprog_bytes, tprog_prog, tprog_senv).

Lemma encode_elf_correct:
  forall rs, forward_simulation (RelocElfSemantics.semantics instr_size prog rs)
                                (ElfBytesSemantics.semantics instr_size tprog_bytes tprog_prog tprog_senv rs).
Proof.
  unfold match_prog in TRANSF.
  unfold ElfBytesSemantics.semantics. intros.
  erewrite decode_encode_elf_file; eauto.
  apply forward_simulation_step with (match_states := eq); intuition subst; eauto.
Qed.

End PRES.

End WITH_INSTR_SIZE.

Definition link (p1 p2: list Integers.Byte.int * Asm.program * Globalenvs.Senv.t) :=
  let '(b1, p1, s1) := p1 in let '(b2, p2, s2) := p2 in
  match decode_elf_file b1 p1 s1, decode_elf_file b2 p2 s2 with
  | OK e1, OK e2 =>
    match link_elf_file e1 e2 with
    | Some e =>
      match encode_elf_file e with
        OK r => Some r
      | _ => None
      end
    | None => None
    end
  | _, _ => None
  end.

Instance linker : Linker (list Integers.Byte.int * Asm.program * Globalenvs.Senv.t).
Proof.
  eapply Build_Linker with (link := link) (linkorder := fun _ _ => True).
  auto. auto. auto.
Defined.

Axiom Instance encodeelf_transflink : Linking.TransfLink match_prog.
