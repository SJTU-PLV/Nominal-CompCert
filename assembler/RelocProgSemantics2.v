(** * The semantics of relocatable program after instruction and data encoding *)

(** The key feature of this semantics: it first decode the instructions and
    then use RelocProgsemantics1; moreover, the encoded data is used directly
    in the initialization of the data section *)
Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgramBytes Globalenvs.
Require Import Stacklayout Conventions.
Require Import Linking Errors.
Require Import EncDecRet RelocBingen RelocBinDecode.
Require Import RelocProgSemantics RelocProgSemantics1 RelocProgSemanticsArchi1.
Require Import RelocProgGlobalenvs RelocProgSemanticsArchi.

Import ListNotations.
Local Open Scope error_monad_scope.


(* intermediate program representation *)
Definition program1:= RelocProg.program fundef unit instruction byte.
Definition section1 := RelocProg.section instruction byte.
Definition sectable1 := RelocProg.sectable instruction byte.

Section WITH_INSTR_SIZE.
  Variable instr_size : instruction -> Z.
Section WITHGE.

  Variable ge:RelocProgGlobalenvs.Genv.t.
  
(** Initialization of memory *)

Fixpoint aux_generate_fragment_ptr n v q :=
  match n with
  | O =>
    []
  | S n' =>
    Fragment v q n' :: aux_generate_fragment_ptr n' v q
  end.


Fixpoint aux_generate_fragment_undef n :=
  match n with
  | O =>
    []
  | S n' =>
    Undef :: aux_generate_fragment_undef n'
  end.

    
  
Definition acc_data r b : list memval * Z * reloctable * list byte :=
  let '(lmv, ofs, reloctbl, ofsbytes) := r in
  match reloctbl with
  | [] => (lmv ++ [Byte b], ofs + 1, [], ofsbytes)
  | e :: tl =>
    let n := if Archi.ptr64 then 8 else 4 in
    let q := if Archi.ptr64 then Q64 else Q32 in
    if ((reloc_offset e) <=? ofs) && (ofs <? (reloc_offset e) + n) then
      let m := n - 1 - (ofs - (reloc_offset e)) in
      if m =? 0 then
        let addrofs := decode_int (ofsbytes ++ [b]) in
        let v := Genv.symbol_address ge (reloc_symb e) (Ptrofs.repr addrofs) in
        let mv := match v with
                  | Vptr _ _ => aux_generate_fragment_ptr (Z.to_nat n) v q
                  | _ => aux_generate_fragment_undef (Z.to_nat n)
                  end in
        (lmv ++ mv, ofs + 1, tl, [])
      else
        (lmv, ofs + 1, reloctbl, ofsbytes ++ [b])
    else
      (lmv ++ [Byte b], ofs + 1, reloctbl, [])
  end.


Definition store_init_data_bytes (reloctbl: reloctable) (m: mem) (b: block) (p: Z) (bytes: list byte) : option mem :=
  let memvals := fst (fst (fst (fold_left acc_data bytes ([],0,reloctbl,[])))) in
  Mem.storebytes m b p memvals.

Definition alloc_section (reloctbl_map: reloctable_map) (r: option mem) (id: ident) (sec: RelocProg.section instruction byte) : option mem :=
  let reloctbl := match reloctbl_map ! id with
                  | None => []
                  | Some r => r
                  end in
  let store_init_data_bytes := store_init_data_bytes reloctbl in
  match r with
  | None => None
  | Some m =>
    match sec with
    | sec_rwdata bytes =>
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
    | sec_rodata bytes =>
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
    | sec_text code =>
      let sz := Z.max (code_size instr_size code) 1 in
      let (m1, b) := Mem.alloc_glob id m 0 sz in
      Mem.drop_perm m1 b 0 sz Nonempty
    end                  
  end.


Definition alloc_sections (reloctbl_map: reloctable_map) (sectbl: RelocProg.sectable instruction byte) (m:mem) :option mem :=
  PTree.fold (alloc_section reloctbl_map) sectbl (Some m).

End WITHGE.


Definition init_mem (p: RelocProg.program fundef unit instruction byte) :=
  let ge := RelocProgSemantics.globalenv instr_size p in
  match alloc_sections ge p.(prog_reloctables) p.(prog_sectable) Mem.empty with
  | Some m1 =>
    RelocProgSemantics.alloc_external_symbols m1 p.(prog_symbtable)
  | None => None
  end.

(* Instructions Decoding *)

Program Fixpoint decode_instrs_bits (bits: list bool) {measure (length bits)} : res (list Instruction) :=
  match bits with
  | nil => OK []
  | _ =>
    do (i, len) <- EncDecRet.decode_Instruction bits;
    match len with
    | S _ =>
      let bits' := skipn len bits in
      do tl <- decode_instrs_bits bits';
       OK (i :: tl)
    | _ =>
      Error (msg "decode_Instruction produce len = 0")
    end
  end.
Next Obligation.
  erewrite skipn_length.
  destruct bits. congruence.
  simpl.
  lia.
Defined.

  
Lemma decode_instrs_bits_eq: forall bits,
    decode_instrs_bits bits =
    match bits with
    | nil => OK []
    | _ =>
      do (i, len) <- EncDecRet.decode_Instruction bits;
      match len with
      | S _ =>
        let bits' := skipn len bits in
        do tl <- decode_instrs_bits bits';
        OK (i :: tl)
      | _ =>
        Error (msg "decode_Instruction produce len = 0")
      end
    end.
Proof.
  intros. 
  unfold decode_instrs_bits.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext.
  cbn [projT1].  cbn [projT2].
  destr.
  destruct (decode_Instruction (b :: l)) eqn:DES.
  - destruct p.
    cbn [bind2].
    destr.
  - cbn [bind2].
    auto.
Qed.

(* For simplicity, we calculate code size every iteration*)
Program Fixpoint decode_instrs (instrs: list Instruction) {measure (length instrs)} :=
  match instrs with
  | [] => OK []
  | _ =>
    do (i, instrs') <- decode_instr instrs;
    match lt_dec (length instrs') (length instrs) with
    | left _ =>
      do tl <- decode_instrs instrs';
      OK (i :: tl)
    | _ => Error (msg "decode_instrs error")                  
    end
  end.


Lemma decode_instrs_eq :forall instrs,
    decode_instrs instrs =
    match instrs with
    | [] => OK []
    | _ =>
      do (i, instrs') <- decode_instr instrs;
      match lt_dec (length instrs') (length instrs) with
      | left _ =>
        do tl <- decode_instrs instrs';
      OK (i :: tl)
      | _ => Error (msg "decode_instrs error")                  
      end
    end.
Proof.
  intros. 
  destruct instrs. auto.

  unfold decode_instrs.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext.
  cbn [projT1].  cbn [projT2].
  destruct (decode_instr (i::instrs)) eqn: DES.
  + destruct p. cbn [bind2].
    destr.
  + cbn [bind2]. auto.
Qed.

Definition decode_instrs' (bytes: list byte) :=
  let bits := bytes_to_bits_archi bytes in
  do instrs1 <- decode_instrs_bits bits;
  do instrs2 <- decode_instrs instrs1;
  OK instrs2.
  
Definition acc_decode_code_section (reloctbl_map: reloctable_map) id (sec:section) : res (RelocProg.section instruction byte) :=
  (* do acc' <- acc; *)
  let reloctbl := match reloctbl_map ! id with
                  | None => []
                  | Some r => r
                  end in
  match sec with
  | sec_text bs =>
    do instrs <- decode_instrs' bs;
    OK (sec_text instrs)
  (* OK (PTree.set id (sec_text instrs) acc') *)
  | sec_rodata bs =>
    OK (sec_rodata bs)
  | sec_rwdata bs =>
    OK (sec_rwdata bs)       
  end.



Definition decode_prog_code_section (p:program) : res program1 :=
  do t <- PTree.fold (acc_PTree_fold (acc_decode_code_section p.(prog_reloctables))) (prog_sectable p) (OK (PTree.empty section1));
  OK {| prog_defs      := prog_defs p;
        prog_public    := prog_public p;
        prog_main      := prog_main p;
        prog_sectable  := t;
        prog_symbtable := prog_symbtable p;
        prog_reloctables := prog_reloctables p;
        prog_senv        := prog_senv p;
     |}.

Definition empty_program1 (prog: program): program1 :=
  {| prog_defs := prog.(prog_defs);
     prog_public := []; (* no use *)
     prog_main := prog.(prog_main);
     prog_sectable := PTree.empty section1;
     prog_symbtable := PTree.empty symbentry;
     prog_reloctables := PTree.empty reloctable;
     prog_senv := prog.(prog_senv) |}.
                                     
 
Definition globalenv (prog: program) :=
  match decode_prog_code_section prog with
  | OK prog' =>
    RelocProgSemantics1.globalenv instr_size prog'
  (* prove this impossible *)
  | _ => RelocProgSemantics.globalenv instr_size (empty_program1 prog)
  end.

Inductive initial_state (prog: program) (rs: regset) (s: state): Prop :=
| initial_state_intro: forall m prog',
    decode_prog_code_section prog = OK prog' ->
    init_mem prog' = Some m ->
    RelocProgSemantics.initial_state_gen instr_size prog' rs m s ->
    initial_state prog rs s.

Definition semantics (p: program) (rs: regset) :=
  Semantics_gen (RelocProgSemantics.step instr_size)
                (initial_state p rs) RelocProgSemantics.final_state 
                (globalenv p)
                (RelocProgGlobalenvs.Genv.genv_senv (globalenv p)).

(** Determinacy of the semantics. *)

Lemma semantics_determinate: forall p rs, determinate (semantics p rs).
Proof.
  Ltac Equalities :=
    match goal with
    | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
    | _ => idtac
    end.
  intros.
  constructor;simpl;intros.
  -                             (* initial state *)
    inv H;inv H0;Equalities.
    + split. constructor. auto.
    + discriminate.
    + discriminate.
    + assert (vargs0 = vargs) by (eapply RelocProgSemanticsArchi.eval_builtin_args_determ; eauto).   
      subst vargs0.      
      exploit external_call_determ. eexact H5. eexact H11. intros [A B].
      split. auto. intros. destruct B; auto. subst. auto.
    + assert (args0 = args) by (eapply Asm.extcall_arguments_determ; eauto). subst args0.
      exploit external_call_determ. eexact H3. eexact H7. intros [A B].
      split. auto. intros. destruct B; auto. subst. auto.
  - red; intros; inv H; simpl.
    lia.
    eapply external_call_trace_length; eauto.
    eapply external_call_trace_length; eauto.
  - (* initial states *)
    inv H; inv H0. inv H1;inv H2. assert (m = m0) by congruence.
    assert (prog' = prog'0) by congruence.
    subst. inv H5; inv H3.
  assert (m1 = m3 /\ stk = stk0) by intuition congruence. destruct H0; subst.
  assert (m2 = m4) by congruence. subst.
  f_equal.
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
  eapply external_call_trace_length; eauto.
Qed.

Theorem reloc_prog_receptive p rs:
  receptive (semantics p rs).
Proof.
  split.
  - simpl. intros s t1 s1 t2 STEP MT.
    inv STEP.
    inv MT. eexists.
    + eapply RelocProgSemantics.exec_step_internal; eauto.
    + 
      edestruct external_call_receptive as (vres2 & m2 & EC2); eauto.
      eexists. eapply RelocProgSemantics.exec_step_builtin; eauto.
    + edestruct external_call_receptive as (vres2 & m2 & EC2); eauto.
      eexists. eapply RelocProgSemantics.exec_step_external; eauto.
  - eapply reloc_prog_single_events; eauto.  
Qed.

End WITH_INSTR_SIZE.
