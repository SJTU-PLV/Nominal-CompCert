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

(* unused 
Hypothesis id_eliminate_size_unchanged:forall i, instr_size i = instr_size (id_eliminate i).


Lemma code_id_eliminate_size_unchanged:forall c,
    code_size instr_size (transl_code' c) = code_size instr_size c.
Proof.
  intros. unfold transl_code'.
  induction c;simpl;auto.
  rewrite IHc. rewrite <- id_eliminate_size_unchanged.
  auto.
Qed. *)


(* id_eliminate just transforms Pjmp_s to Pjmp_l_rel and leaves another instruction forms unchanged *)
Definition instr_eq i1 i2 :=
  match i1,i2 with
  | Pjmp_s symb1 _, Pjmp_s symb2 _ => symb1 = symb2
  | _,_ => i1 = i2
  end.

Lemma instr_eq_refl: forall i, instr_eq i i.
Proof.
  unfold instr_eq.
  destruct i;auto.
Qed.


Lemma transl_instr_consistency: forall i ofs e,
    transl_instr instr_size ofs i = OK (Some e) ->
    instr_eq (rev_id_eliminate (reloc_symb e) (reloc_addend e) (id_eliminate i)) i.
Proof.
  intros i ofs e.
  destruct i;simpl;auto;
    unfold transl_instr;intros H;destr_match_in H;try monadInv H.

  (* Pmov_rs *)
  unfold compute_instr_abs_relocentry in EQ0.
  monadInv EQ0. simpl. auto.

  1-41: try (destruct a;destruct const;try destruct p;try monadInv H).

  
  1-41: unfold compute_instr_disp_relocentry in *;
      destruct Archi.ptr64;
      unfold compute_instr_abs_relocentry in *;
    unfold compute_instr_rel_relocentry in *;
    repeat (monadInv EQ0);
  simpl;unfold instr_eq;auto;
    try (destruct a;destruct const;try destruct p;try congruence);
  try rewrite Ptrofs.repr_signed;
  try (monadInv H;
       unfold compute_instr_abs_relocentry in *;
       unfold compute_instr_disp_relocentry in *;
       unfold compute_instr_rel_relocentry in *;
       repeat (monadInv EQ));
       try (try monadInv EQ0;simpl;auto).

  (* Pjmp_m *)
  destruct base. monadInv H.
  monadInv EQ0. simpl;auto.
  destruct ofs0. monadInv H.
  monadInv EQ0. simpl;auto.
  monadInv H. 
  simpl;auto.

  monadInv EQ0. simpl;auto.
  destruct base. monadInv H.
  monadInv EQ0. simpl;auto.
  destruct ofs0. monadInv H.
  monadInv EQ0. simpl;auto.
  monadInv H. monadInv EQ0.
  simpl;auto.

  (* Pmovw *)
  destruct ad;destruct const;try destruct p;try congruence.
  monadInv H. monadInv EQ0. simpl;rewrite Ptrofs.repr_signed;auto.
  destruct ad;destruct const;try destruct p;try congruence.
  monadInv H. monadInv EQ0. inv EQ1;simpl;rewrite Ptrofs.repr_signed;auto.  
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
  destr_in H0;subst. simpl. rewrite H. auto.
Qed.

End WITH_INSTR_SIZE.
