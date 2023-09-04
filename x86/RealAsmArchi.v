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
    (* The eliminated pseudo instructions *)
    | Pallocframe _ _ _
    | Pfreeframe  _ _ _
    (* AsmBuiltinInline.v *)
    | Pbuiltin _ _ _
    (* AsmFloatLiteral.v *)
    | Pmovsd_fi _ _
    | Pmovss_fi _ _
    | Pnegd _
    | Pnegs _
    | Pabsd _
    | Pabss _
    (* AsmLongInt.v *)
    | Pmovq_ri _ _
    | Paddq_ri _ _               
    | Psubq_ri _ _
    | Pimulq_ri _ _
    | Pandq_ri _ _
    | Porq_ri _ _
    | Pxorq_ri _ _
    | Pcmpq_ri _ _
    | Ptestq_ri _ _
    (* Some uncategorized pseudo instructions *)
    | Psetcc _ _
    | Pjcc2 _ _ _
    | Pbswap16 _
    (* instructions with `any' type *)
    | Pmovsd_mf_a _ _
    | Pmovsd_fm_a _ _
    | Pmov_mr_a _ _
    | Pmov_rm_a _ _
    | Pxorq_r _
    | Pxorl_r _
    | Pmovls_rr _
    (* zero extened move, just replace with normal move *)
    | Pmovzl_rr _ _
    (* jump to label => jump to relative address *)
    | Pjmp_l _
    | Pjcc _ _
    | Pjmptbl _ _
    | Plabel _
    | Pjmptbl_rel _ _ => Stuck
                  
    (* TODO: We need to define the semantics of new introduced instructions,
    which are undefined in Asm.v *)
    | Pret_iw _
        (* if check_ra_after_call instr_size ge (rs#RA) then *)
        (*   (* pop n bytes from the stack  *) *)
        (*   let psp := (Val.offset_ptr (rs#RSP) (Ptrofs.repr (Int.unsigned n))) in *)
        (*   Next (rs#PC <- (rs#RA) #RA <- Vundef #RSP <- psp) m *)
        (* else Stuck                *)
    | Pxorpd_fm _ _
        (* load memory values *)
        (* match Mem.loadv Mfloat64 m (eval_addrmode ge a rs) with *)
        (* | Some v => Stuck             (* there is no xor for floats *) *)
        (* | None => Stuck *)
        (* end *)
    | Pandpd_fm _ _ 
    | Pxorps_fm _ _
    | Pandps_fm _ _
    | Pjmp_m _
    | Prolw_ri _ _               
    | Paddq_rm _ _
    | Psubq_rm _ _
    | Pimulq_rm _ _
    | Pandq_rm _ _
    | Porq_rm  _ _
    | Pxorq_rm _ _
    | Pcmpq_rm _ _                         
    | Ptestq_rm _ _  => Stuck    (* TODO! *)
    (* For other instructions, we just reuse Asm.v *)
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
 
