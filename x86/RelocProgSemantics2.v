(* *******************  *)
(* Author: Jinhua Wu    *)
(* Date:   Jul 26th     *)
(* *******************  *)

(** * The semantics of relocatable program after instruction and data encoding *)

(** The key feature of this semantics: it first decode the instructions and
    then use RelocProgsemantics1; moreover, the encoded data is used directly
    in the initialization of the data section *)
Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgram Globalenvs.
Require Import Stacklayout Conventions.
Require Import Linking Errors.
Require Import EncDecRet RelocBingen RelocBinDecode.
Require Import RelocProgSemantics RelocProgSemantics1.

Import ListNotations.
Local Open Scope error_monad_scope.

Section WITH_INSTR_SIZE.
  Variable instr_size : instruction -> Z.
  Variable Instr_size : list Instruction -> Z.
Section WITHGE.

  Variable ge:RelocProgSemantics.Genv.t.
  
(** Initialization of memory *)

Definition acc_data r b : list memval * Z * reloctable :=
  let '(lmv, ofs, reloctbl) := r in
  match reloctbl with
  | [] => (lmv ++ [Byte b], ofs + 1, []) 
  | e :: tl =>
    let n := if Archi.ptr64 then 8 else 4 in
    let q := if Archi.ptr64 then Q64 else Q32 in
    if ((reloc_offset e) <=? ofs) && (ofs <? (reloc_offset e) + n) then
      let v := Genv.symbol_address ge (reloc_symb e) (Ptrofs.repr (reloc_addend e)) in
      let m := n - 1 - (ofs - (reloc_offset e)) in
      (lmv ++ [Fragment v q (Z.to_nat m)], ofs + 1, tl)
    else
      (lmv ++ [Byte b], ofs + 1, reloctbl)
  end.


Definition store_init_data_bytes (reloctbl: reloctable) (m: mem) (b: block) (p: Z) (bytes: list byte) : option mem :=
  let memvals := fst (fst (fold_left acc_data bytes ([],0,reloctbl))) in
  Mem.storebytes m b p memvals.

Definition alloc_section (symbtbl: symbtable) (reloctbl_map: reloctable_map) (r: option mem) (id: ident) (sec: section) : option mem :=
  let reloctbl := match reloctbl_map ! id with
                  | None => []
                  | Some r => r
                  end in
  let store_init_data_bytes := store_init_data_bytes reloctbl in
  match r with
  | None => None
  | Some m =>
    (**r Assume section ident corresponds to a symbol entry *)
    match get_symbol_type symbtbl id with
    | Some ty =>
      match sec, ty with
      | sec_bytes bytes, symb_rwdata =>
        let sz := Z.of_nat (Datatypes.length bytes) in
        let '(m1, b) := Mem.alloc_glob id m 0 sz in
        match store_zeros m1 b 0 sz with
        | None => None
        | Some m2 =>
          match store_init_data_bytes m2 b 0 bytes with
          | None => None
          | Some m3 => Mem.drop_perm m3 b 0 sz Writable
          end
        end
      | sec_bytes bytes, symb_rodata =>
        let sz := Z.of_nat (Datatypes.length bytes) in
        let '(m1, b) := Mem.alloc_glob id m 0 sz in
        match store_zeros m1 b 0 sz with
        | None => None
        | Some m2 =>
          match store_init_data_bytes m2 b 0 bytes with
          | None => None
          | Some m3 => Mem.drop_perm m3 b 0 sz Readable
          end
        end
      | sec_bytes bytes , symb_func =>
        let sz := Z.of_nat (Datatypes.length bytes) in
        let (m1, b) := Mem.alloc_glob id m 0 sz in
        Mem.drop_perm m1 b 0 sz Nonempty
      | _, _ => None
      end
    | None => None
    end
  end.


Definition alloc_sections (symbtbl: symbtable) (reloctbl_map: reloctable_map) (sectbl: sectable) (m:mem) :option mem :=
  PTree.fold (alloc_section symbtbl reloctbl_map) sectbl (Some m).

End WITHGE.


Definition init_mem (p: program) :=
  let ge := RelocProgSemantics.globalenv instr_size p in
  match alloc_sections ge p.(prog_symbtable) p.(prog_reloctables) p.(prog_sectable) Mem.empty with
  | Some m1 =>
    RelocProgSemantics.alloc_external_symbols m1 p.(prog_symbtable)
  | None => None
  end.


Fixpoint decode_instrs_bytes (fuel:nat) (bytes: list byte) (acc: list Instruction) : res (list Instruction) :=
  match bytes with
  | nil => OK acc
  | _ =>
    match fuel with
    | O => Error (msg "instruction decoding failed: run out of fuel")
    | S fuel' =>
      do (i, len) <- EncDecRet.decode_Instruction bytes;
      let bytes' := skipn len bytes in
      decode_instrs_bytes fuel' bytes' (acc ++ [i])
    end
  end.

Fixpoint decode_instrs (fuel: nat) (reloctbl: reloctable) (ofs: Z) (instrs: list Instruction) (acc: list instruction) :=
  match instrs with
  | [] => OK acc
  | _ =>
    match fuel with
    | O => Error (msg "instruction decoding failed: run out of fuel")
    | S fuel' =>
      match reloctbl with
      | [] => 
        do (i, instrs') <- decode_instr None instrs;
        decode_instrs fuel' [] (ofs + instr_size i) instrs' (acc ++ [i])
      | e :: tl =>
        let sz := Instr_size instrs in
        let ofs' := ofs + sz in
        if (ofs <? e.(reloc_offset)) && (e.(reloc_offset) <? ofs') then
          do (i, instrs') <- decode_instr (Some e) instrs;
          decode_instrs fuel' tl ofs' instrs' (acc++[i])
        else
          do (i, instrs') <- decode_instr None instrs;
          decode_instrs fuel' reloctbl ofs' instrs' (acc++[i])
      end
    end
  end.
      
Definition decode_instrs' (reloctbl: reloctable) (bytes: list byte) :=
  do instrs1 <- decode_instrs_bytes (length bytes) bytes [];
  do instrs2 <- decode_instrs (length instrs1) reloctbl 0 instrs1 [];
  OK instrs2.
  
Definition decode_code_section (e: symbentry) (reloctbl: reloctable) (id: ident) (s:section) : res section :=
    match s, (symbentry_type e) with
    | sec_bytes bs, symb_func =>
      do instrs <- decode_instrs' reloctbl bs;
      OK (sec_text instrs)
    | _,_ =>
      Error (msg "Code section is not encoded into bytes")
    end.


Definition acc_decode_code_section (symbtbl: symbtable) (reloctbl_map: reloctable_map) acc id sec:=
  do acc' <- acc;
  let reloctbl := match reloctbl_map ! id with
                  | None => []
                  | Some r => r
                  end in
  match symbtbl ! id with
  | Some e =>
    do s <- decode_code_section e reloctbl id sec;
    OK (PTree.set id s acc')
  | _ => Error (msg "Decode code section: no corresponding symbol entry")
  end.


Definition decode_prog_code_section (p:program) : res program :=
  do t <- PTree.fold (acc_decode_code_section p.(prog_symbtable) p.(prog_reloctables)) (prog_sectable p) (OK (PTree.empty section));
  OK {| prog_defs      := prog_defs p;
        prog_public    := prog_public p;
        prog_main      := prog_main p;
        prog_sectable  := t;
        prog_symbtable := prog_symbtable p;
        prog_reloctables := prog_reloctables p;
        prog_senv        := prog_senv p;
     |}.
 
Inductive initial_state (prog: program) (rs: regset) (s: state): Prop :=
| initial_state_intro: forall m prog',
    decode_prog_code_section prog = OK prog' ->
    init_mem prog' = Some m ->
    RelocProgSemantics1.initial_state_gen prog' rs m s ->
    initial_state prog rs s.

Definition semantics (p: program) (rs: regset) :=
  Semantics_gen RelocProgSemantics1.step 
                (initial_state p rs) RelocProgSemantics1.final_state 
                (RelocProgSemantics1.globalenv p) 
                (RelocProgSemantics1.genv_senv (RelocProgSemantics1.globalenv p)).


(** Determinacy of the semantics. *)

Lemma semantics_determinate: forall p rs, determinate (semantics p rs).
Proof.
  intros.
  destruct (RelocProgSemantics1.semantics_determinate p rs).
  constructor; simpl; auto.
- (* initial states *)
  intros. inv H; inv H0. 
  assert (prog' = prog'0) by congruence. subst.
  assert (m = m0) by congruence. subst. inv H3; inv H5.
  assert (m1 = m5 /\ bstack = bstack0) by intuition congruence. destruct H0; subst.
  assert (m2 = m6) by congruence. subst.
  f_equal. congruence.
Qed.

Theorem reloc_prog_single_events p rs:
  single_events (semantics p rs).
Proof.
  red. simpl. intros s t s' STEP.
  inv STEP; simpl. omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
Qed.

Theorem reloc_prog_receptive p rs:
  receptive (semantics p rs).
Proof.
  destruct (RelocProgSemantics1.reloc_prog_receptive p rs).
  split; auto.
Qed.

