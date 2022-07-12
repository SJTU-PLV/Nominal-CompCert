(* *******************  *)
(* Author: Jinhua Wu  *)
(* Date:   July 12, 2022  *)
(* *******************  *)

(** * The semantics of relocatable program using both the symbol and the relocation tables *)

(** The key feature of this semantics: it uses the relocation tables 
for each sections to recover the id in the code section. 
The data sections is unchanged in relocation table generation.
Then we apply the RelocProgsemantics to the decoded program *)

Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgram Globalenvs.
Require Import Locations Stacklayout Conventions.
Require Import Linking Errors.
Require RelocProgSemantics Reloctablesgen.
Require Import LocalLib.
Import ListNotations.
(** Global environments *)


Section WITH_INSTR_SIZE.
  Variable instr_size : instruction -> Z.


Definition rev_id_eliminate (symb: ident) (i:instruction) :=
   match i with
  | Pjmp_s id sg =>
     (Pjmp_s symb sg)
  | Pjmp_m (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pjmp_m (Addrmode rb ss (inr (symb,ptrofs))))
  | Pcall_s id sg =>
     (Pcall_s symb sg)
  | Pmov_rs rd id =>
     (Pmov_rs rd symb)
  | Pmovl_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovl_rm rd (Addrmode rb ss (inr (symb,ptrofs))))
  | Pmovl_mr (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
     (Pmovl_mr (Addrmode rb ss (inr (symb, ptrofs))) rs)
  | Pfldl_m (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pfldl_m (Addrmode rb ss (inr (symb, ptrofs))))
  | Pfstpl_m (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pfstpl_m (Addrmode rb ss (inr (symb, ptrofs))))
  | Pflds_m (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pflds_m (Addrmode rb ss (inr (symb, ptrofs))))
  | Pfstps_m (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pfstps_m (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovsd_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovsd_fm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovsd_mf (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
     (Pmovsd_mf (Addrmode rb ss (inr (symb, ptrofs))) rs)
  | Pmovss_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovss_fm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovss_mf (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
     (Pmovss_mf (Addrmode rb ss (inr (symb, ptrofs))) rs)
  | Pxorpd_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pxorpd_fm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pxorps_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pxorps_fm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pandpd_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pandpd_fm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pandps_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pandps_fm rd (Addrmode rb ss (inr (symb, ptrofs))))
  (** Moves with conversion *)
  | Pmovb_mr (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
     (Pmovb_mr (Addrmode rb ss (inr (symb, ptrofs))) rs)
  | Pmovb_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovb_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovw_mr (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
     (Pmovw_mr (Addrmode rb ss (inr (symb, ptrofs))) rs)
  | Pmovw_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovw_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovzb_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovzb_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovsb_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovsb_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovzw_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovzw_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovsw_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovsw_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovsq_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovsq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovsq_mr (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
     (Pmovsq_mr (Addrmode rb ss (inr (symb, ptrofs))) rs)
  (** Integer arithmetic *)
  | Pleal rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
     (Pleal rd (Addrmode rb ss (inr (symb, ptrofs))))
  (** Saving and restoring registers *)
  | Pmov_rm_a rd (Addrmode rb ss (inr disp)) =>  (**r like [Pmov_rm], using [Many64] chunk *)
    let '(id, ptrofs) := disp in
     (Pmov_rm_a rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmov_mr_a (Addrmode rb ss (inr disp)) rs =>   (**r like [Pmov_mr], using [Many64] chunk *)
    let '(id, ptrofs) := disp in
    (Pmov_mr_a (Addrmode rb ss (inr (symb, ptrofs))) rs)
  | Paddq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Paddq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Psubq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Psubq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pimulq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Pimulq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pandq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Pandq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Porq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Porq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pxorq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Pxorq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pcmpq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Pcmpq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Ptestq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Ptestq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Pmovq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovq_mr (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
    (Pmovq_mr (Addrmode rb ss (inr (symb, ptrofs))) rs)
  | Pleaq rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
     (Pleaq rd (Addrmode rb ss (inr (symb, ptrofs))))
  | _ =>
     i
    end.

Definition rev_acc_code (r:code*Z*reloctable) i :=
  let '(c,ofs,reloctbl) := r in
  match reloctbl with
  | [] =>
    (c++[i], ofs + instr_size i, [])
  | e :: reloctbl' =>
    let ofs' := ofs + instr_size i in
    if Z.ltb ofs e.(reloc_offset) && Z.ltb e.(reloc_offset) ofs' then
      (c++[rev_id_eliminate e.(reloc_symb) i], ofs', reloctbl')
    else
      (c++[i], ofs', reloctbl)
  end.


Definition rev_transl_code (reloctbl: reloctable) (c:code) :=
  fst (fst (fold_left rev_acc_code c ([],0,reloctbl))).

Definition rev_section (reloctbl_map: reloctable_map) (id:ident) (sec:section) :=
  match sec with
  | sec_text c =>
    match reloctbl_map ! id with
    | Some reloctbl =>
      sec_text (rev_transl_code reloctbl c)
    | None => sec
    end
  | _ => sec
  end.

Definition decode_program (p:program) :=
  {| prog_defs := prog_defs p;
     prog_public := prog_public p;
     prog_main := prog_main p;
     prog_sectable := PTree.map (rev_section p.(prog_reloctables)) p.(prog_sectable);
     prog_symbtable := prog_symbtable p;
     prog_reloctables := p.(prog_reloctables);
     prog_senv := prog_senv p;
  |}.

Inductive initial_state (p:program) (rs:regset) (st:state) : Prop :=
| initial_state_intro: forall p',
    p' = decode_program p ->
    RelocProgSemantics.initial_state instr_size p' rs st ->
    initial_state p rs st.

Definition semantics (p:program) (rs:regset) :=
  Semantics_gen (RelocProgSemantics.step instr_size)
                (initial_state p rs)
                (RelocProgSemantics.final_state)
                (RelocProgSemantics.globalenv instr_size p)
                (RelocProgSemantics.Genv.genv_senv (RelocProgSemantics.globalenv instr_size p)).

Lemma semantics_determinate: forall p rs, determinate (semantics p rs).
Proof.
  intros.
  destruct (RelocProgSemantics.semantics_determinate instr_size p rs).
  constructor;eauto.
  -                             (* initial state *)
    intros. inv H;inv H0.
    inv H1. inv H2.
    assert (m = m0) by congruence. subst.
    inv H0. inv H3.
    assert (m1 = m3 /\ stk = stk0) by  intuition congruence. destruct H0. subst.
    assert (m2 = m4) by congruence. subst.
    f_equal.
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
  destruct (RelocProgSemantics.reloc_prog_receptive instr_size p rs).
  split; auto.
Qed.

End WITH_INSTR_SIZE.
