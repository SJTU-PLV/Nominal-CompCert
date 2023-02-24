Require Import Smallstep.
Require Import Machregs.
Require Import Asm.
Require Import Integers.
Require Import Floats.
Require Import List.
Require Import ZArith.
Require Import Memtype.
Require Import Memory.
Require Import Archi.
Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Values.
Require Import Conventions1.

Definition stkblock := Stack None nil 1.

(** * Operational Semantics with instr_size *)
Section INSTRSIZE.
Variable instr_size : instruction -> Z.

Section WITHGE.
  Variable ge : Genv.t Asm.fundef unit.

  Definition exec_instr f i rs (m: mem) :=
    let isz := Ptrofs.repr (instr_size i) in
    match i with
    | Pallocframe sz ofs_ra ofs_link =>
      let aligned_sz := (* align sz 8 *) sz in
      let psp := (Val.offset_ptr (rs#RSP) (Ptrofs.repr (size_chunk Mptr))) in (* parent stack pointer *)
      let sp := Val.offset_ptr (rs#RSP) (Ptrofs.neg (Ptrofs.sub (Ptrofs.repr aligned_sz) (Ptrofs.repr (size_chunk Mptr)))) in
      match Mem.storev Mptr m (Val.offset_ptr sp ofs_link) psp with
        |None => Stuck
        |Some m1 =>
      Next (nextinstr_nf isz (rs #RAX <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr))) #RSP <- sp)) m1
      end
    | Pfreeframe sz ofs_ra ofs_link =>
      let sp := Val.offset_ptr (rs RSP) (Ptrofs.sub (Ptrofs.repr (*(align sz 8)*) sz) (Ptrofs.repr (size_chunk Mptr))) in
      Next (nextinstr isz (rs#RSP <- sp)) m
    | Pcall_s i sg =>
      let sp := Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))) in
      match Mem.storev Mptr m sp (Val.offset_ptr rs#PC isz) with
        |None => Stuck
        |Some m1 =>
        Next (rs#RA <- (Val.offset_ptr rs#PC isz)
                #PC <- (Genv.symbol_address ge i Ptrofs.zero)
                #RSP <- sp) m1
      end
    |Pcall_r r sg =>
      let sp := Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))) in
      match Mem.storev Mptr m sp (Val.offset_ptr rs#PC isz) with
        |None => Stuck
        |Some m1 =>
        Next (rs#RA <- (Val.offset_ptr rs#PC isz)
                #PC <- (rs r)
                #RSP <- sp) m1
      end
    | Pret =>
      match loadvv Mptr m rs#RSP with
      | None => Stuck
      | Some ra =>
        let sp := Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr)) in
        Next (rs #RSP <- sp
                 #PC <- ra
                 #RA <- Vundef) m
      end
    | _ => exec_instr instr_size ge f i rs m
    end.

  Inductive step  : state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr instr_size (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
        exec_instr f i rs m = Next rs' m' ->
        step (State rs m) E0 (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments
        (rs # RSP <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr)))) m (ef_sig ef) args ->
        forall (SP_TYPE: Val.has_type (rs RSP) Tptr)
          ra (LOADRA: Mem.loadv Mptr m (rs RSP) = Some ra)
          (SP_NOT_VUNDEF: rs RSP <> Vundef)
          (RA_NOT_VUNDEF: ra <> Vundef),
      external_call ef ge args m t res m' ->
      rs' = (set_pair (loc_external_result (ef_sig ef))
                      res (undef_caller_save_regs rs))
              #PC <- ra
              #RA <- Vundef
              #RSP <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr)))
      ->
      step (State rs m) t (State rs' m').

End WITHGE.

Inductive initial_stack_regset (p: Asm.program) (m0: mem) : mem -> regset -> Prop :=
| initial_state_archi_archi: forall m1 m2 stk bmain,
    Mem.alloc m0 0 (max_stacksize + (align (size_chunk Mptr)8)) = (m1, stk) ->
    Mem.storev Mptr m1 (Vptr stk (Ptrofs.repr (max_stacksize + align (size_chunk Mptr) 8 - size_chunk Mptr))) Vnullptr = Some m2 ->
    let ge := Genv.globalenv p in
    Genv.find_symbol ge p.(prog_main) = Some bmain ->
    let rs0 :=
      (Pregmap.init Vundef)
        # PC <- (Vptr bmain Ptrofs.zero)
        # RA <- Vnullptr
        # RSP <- (Val.offset_ptr
                   (Vptr stkblock (Ptrofs.repr (max_stacksize + align (size_chunk Mptr) 8)))
                   (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr)))) in
    initial_stack_regset p m0 m2 rs0.

  Ltac rewrite_hyps :=
  repeat
    match goal with
      H1 : ?a = _, H2: ?a = _ |- _ => rewrite H1 in H2; inv H2
    end.

  Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  
Lemma semantics_determinate_step : forall p s s1 s2 t1 t2,
  step (Genv.globalenv p) s t1 s1 ->
  step (Genv.globalenv p) s t2 s2 -> match_traces (Genv.globalenv p) t1 t2 /\ (t1 = t2 -> s1 = s2).
Proof.
  intros.
  inv H; inv H0; Equalities.
  split. constructor.  auto.
  assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H4. eexact H9. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
Qed.

End INSTRSIZE.
