Require Import Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Locations Conventions.
Require Import Asm.

Definition stkblock := Stack None nil 1.

Section INSTRSIZE.

Variable instr_size : instruction -> Z.

Section SSASM.

Variable ge: genv.

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  | Pallocframe sz ofs_ra ofs_link =>
    let aligned_sz := align sz 8 in
    let sp := Val.offset_ptr (rs#RSP) (Ptrofs.neg (Ptrofs.repr aligned_sz)) in
    match Mem.storev Mptr m (Val.offset_ptr sp ofs_ra) (rs#RA) with
    | None => Stuck
    | Some m1 =>
      match Mem.storev Mptr m1 (Val.offset_ptr sp ofs_link) rs#RSP with
      | None => Stuck
      | Some m2 => Next (nextinstr_nf (Ptrofs.repr (instr_size i)) (rs #RAX <- (rs#RSP) #RSP <- sp)) m2
      end
    end
  | Pfreeframe sz ofs_ra ofs_link =>
    let aligned_sz := align sz 8 in
    let sp := Val.offset_ptr rs#RSP (Ptrofs.repr aligned_sz) in
    match loadvv Mptr m (Val.offset_ptr rs#RSP ofs_ra) with
    | None => Stuck
    | Some ra => Next (nextinstr  (Ptrofs.repr (instr_size i)) (rs#RSP <- sp #RA <- ra)) m
    end
  | _ => Asm.exec_instr instr_size ge f i rs m
  end.

Inductive step  : state -> trace -> state -> Prop :=
| exec_step_internal:
    forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr instr_size (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
| exec_step_builtin:
    forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr instr_size (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs RSP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextinstr_nf (Ptrofs.repr (instr_size (Pbuiltin ef args res)))
              (set_res res vres
                       (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      step (State rs m) t (State rs' m')
| exec_step_external:
    forall b ef args res rs m t rs' m' m1,
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      Mem.storev Mptr m (Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))))
                 (rs RA) = Some m1 -> (* Act as a x86 function, push RA for the callee function *)
      extcall_arguments rs m1 (ef_sig ef) args ->
      forall (SP_TYPE: Val.has_type (rs RSP) Tptr)
        (RA_TYPE: Val.has_type (rs RA) Tptr)
        (SP_NOT_VUNDEF: rs RSP <> Vundef)
        (RA_NOT_VUNDEF: rs RA <> Vundef),
      external_call ef ge args m1 t res m' ->
      ra_after_call instr_size ge (rs # RA) ->
      rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs))
              #PC <- (rs RA)
              #RA <- Vundef
      ->
      step (State rs m) t (State rs' m').

End SSASM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0 m1 stk bmain,
      Genv.init_mem p = Some m0 ->
      Mem.alloc m0 0 (max_stacksize + align(size_chunk Mptr) 8) = (m1, stk) ->
      let ge := Genv.globalenv p in
      Genv.find_symbol ge p.(prog_main) = Some bmain ->
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Vptr bmain Ptrofs.zero)
        # RA <- Vnullptr
        # RSP <- (Vptr stkblock (Ptrofs.repr (max_stacksize + (align(size_chunk Mptr) 8)))) in
      initial_state p (State rs0 m1).

(** The same final_state as defined in the Asm.v *)
Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

End INSTRSIZE.

Ltac rewrite_hyps :=
  repeat
    match goal with
      H1 : ?a = _, H2: ?a = _ |- _ => rewrite H1 in H2; inv H2
    end.

Ltac trim H :=
  match type of H with
    ?a -> ?b => let x := fresh in assert a as x; [ clear H | specialize (H x); clear x]
  end.

Lemma semantics_determinate: forall isz p, determinate (semantics isz p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities.
+ split. constructor. auto.
+ discriminate.
+ discriminate.
+ assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
+ assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H5. eexact H12. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros; inv H; simpl.
  lia.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0.
  unfold ge, ge0, rs0, rs1 in *. rewrite_hyps. auto.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. red; intros; red; intros. inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

