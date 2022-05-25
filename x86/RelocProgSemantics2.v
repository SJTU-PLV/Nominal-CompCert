(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Dec 6, 2019  *)
(* *******************  *)

(** * The semantics of relocatable program after instruction and data encoding *)

(** The key feature of this semantics: it first decode the instructions and
    then use RelocProgsemantics1; moreover, the encoded data is used directly
    in the initialization of the data section *)
Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProgram Globalenvs.
Require Import Stacklayout Conventions.
Require Import Linking Errors.
(* Require Import RelocBinDecode. *)
Require RelocProgSemantics1.

Local Open Scope error_monad_scope.


(** Initialization of memory *)
Section WITHGE.

Variable ge:RelocProgSemantics1.Genv.t.

Definition store_init_data_bytes (m: mem) (b: block) (p: Z) (bytes: list byte)
                              : option mem :=
  let memvals := List.map Byte bytes in
  Mem.storebytes m b p memvals.


Definition alloc_section (symbtbl: symbtable) (r: option mem) (id: ident) (sec: section) : option mem :=
  match r with
  | None => None
  | Some m =>
    match sec with
    | sec_bytes bs =>
      let sz := Z.of_nat (length bs) in
    (**r Assume section ident corresponds to a symbol entry *)
      match RelocProgSemantics.get_symbol_type symbtbl id with
      | None => None
      | Some ty =>
        match ty with
        | symb_rwdata =>
          let '(m1, b) := Mem.alloc_glob id m 0 sz in
          match store_zeros m1 b 0 sz with
          | None => None
          | Some m2 =>
            match store_init_data_bytes m2 b 0 bs with
            | None => None
            | Some m3 => Mem.drop_perm m3 b 0 sz Writable
            end
          end
        | symb_rodata =>
          let '(m1, b) := Mem.alloc_glob id m 0 sz in
          match store_zeros m1 b 0 sz with
          | None => None
          | Some m2 =>
            match store_init_data_bytes m2 b 0 bs with
            | None => None
            | Some m3 => Mem.drop_perm m3 b 0 sz Readable
            end
          end
        | symb_func =>
          let '(m1, b) := Mem.alloc_glob id m 0 sz in
          Mem.drop_perm m1 b 0 sz Nonempty
        | _ => None
        end            
      end
    | _ => None
    end
  end.

Definition alloc_sections (symbtbl: symbtable) (sectbl: sectable) (m:mem) :option mem :=
  PTree.fold (alloc_section symbtbl) sectbl (Some m).

End WITHGE.

Definition init_mem (p: program) :=
  let ge := RelocProgSemantics.globalenv p in
  match alloc_sections ge p.(prog_symbtable) p.(prog_sectable) Mem.empty with
  | Some m1 =>
    RelocProgSemantics.alloc_external_symbols m1 p.(prog_symbtable)
  | None => None
  end.

Section WITHMAPS.

Variable rtbl_ofs_map: reloc_ofs_map_type.

Variable symtbl : symbtable.

Fixpoint decode_instrs (fuel:nat) (ofs: Z) (bytes: list byte) (instrs: list instruction) : res (list instruction) :=
  match bytes with
  | nil => OK (rev instrs)
  | _ =>
    match fuel with
    | O => Error (msg "instruction decoding failed: run out of fuel")
    | S fuel' =>
      do r <- fmc_instr_decode rtbl_ofs_map symtbl ofs bytes;
      let '(instr, bytes') := r in
      decode_instrs fuel' (ofs + instr_size instr) bytes' (instr :: instrs)
    end
  end.

Definition decode_instrs' (bytes: list byte) :=
  do instrs <- decode_instrs (length bytes) 0 bytes nil;
  OK instrs.
  
Definition decode_code_section (s:section) : res section :=
  match s with
  | sec_bytes bs =>
    do instrs <- decode_instrs' bs;
    OK (sec_text instrs)
  | _ =>
    Error (msg "Code section is not encoded into bytes")
  end.
    
End WITHMAPS.

Definition decode_prog_code_section (p:program) : res program :=
  let t := (prog_sectable p) in
  match SecTable.get sec_code_id t with
  | None => Error (msg "Cannot find a code section in the program")
  | Some sec =>
    let rtbl :=  get_reloctable RELOC_CODE (prog_reloctables p) in
    let rofsmap := gen_reloc_ofs_map rtbl in
    let stbl := prog_symbtable p in
    do sec' <- decode_code_section rofsmap stbl sec;
      match SecTable.set sec_code_id sec' t with
      | None => Error (msg "Cannot find a code section in the program")
      | Some t' =>
        OK {| prog_defs      := prog_defs p;
              prog_public    := prog_public p;
              prog_main      := prog_main p;
              prog_sectable  := t';
              prog_symbtable := prog_symbtable p;
              prog_strtable  := prog_strtable p;
              prog_reloctables := prog_reloctables p;
              prog_senv        := prog_senv p;
           |}
      end
  end.

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

