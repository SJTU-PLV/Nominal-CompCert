Require Import Coqlib Errors Maps.
Require Import Integers Floats AST RelocProgLinking Linking.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import Reloctablesgen ReloctablesgenArchi.
Require Import RelocProg RelocProgram RelocProgSemantics RelocProgSemantics1.
Require Import RelocProgSemanticsArchi1.
Require Import LocalLib AsmInject.
Import ListNotations.
Require AsmFacts.

Local Open Scope error_monad_scope.

Section WITH_INSTR_SIZE.

Variable instr_size : instruction -> Z.
Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.
Hypothesis instr_reloc_bound : forall i ofs, instr_reloc_offset i = OK ofs -> 0 < ofs < instr_size i.
Hypothesis id_eliminate_size_unchanged:forall i, instr_size i = instr_size (id_eliminate i).

Lemma lt_add_range:forall a b c,
    0 < b < c -> a < a + b < a + c.
Proof. 
  intros. lia.
Qed.

Lemma code_id_eliminate_size_unchanged:forall c,
    code_size instr_size (transl_code' c) = code_size instr_size c.
Proof.
  intros. unfold transl_code'.
  induction c;simpl;auto.
  rewrite IHc. rewrite <- id_eliminate_size_unchanged.
  auto.
Qed.

Lemma transl_instr_range: forall ofs i e,
    transl_instr instr_size ofs i = OK (Some e) ->
    ofs < e.(reloc_offset) < ofs + instr_size i.
  intros ofs i e.
  generalize (instr_size_bound i). intros A.  
  unfold transl_instr.

  destruct Archi.ptr64 eqn:PTR.
  -
  (* 64bit *)
  destruct i;intros H;destr_match_in H;try monadInv H. 
  
  (* only solve Pmov_rs *)  
  unfold compute_instr_abs_relocentry in *. monadInv EQ0.
  simpl;eapply lt_add_range; auto.

  1-41: try (destruct a;destruct const;try destruct p;try monadInv H).
  1-41: try (
             unfold compute_instr_disp_relocentry in *;
             try rewrite PTR in *;
             unfold compute_instr_abs_relocentry in *;             
             unfold compute_instr_rel_relocentry in *;
             repeat (monadInv EQ0));
  simpl;try eapply lt_add_range; auto.
  
  (* (* Pjmp_s *) *)
  (* monadInv H1. *)
  (* unfold compute_instr_rel_relocentry in *. *)
  (* monadInv EQ. *)
  (* destr_match_in EQ2;inv EQ2;simpl;eapply lt_add_range; auto. *)
  (* inv H1. simpl. eapply lt_add_range; auto. *)
  (* Pjmp_m *)
  destruct base. monadInv H.
  monadInv EQ0. 
  simpl;eapply lt_add_range; auto.
  destruct ofs0. monadInv H.
  monadInv EQ0.
  simpl;eapply lt_add_range; auto.
  monadInv H. monadInv EQ0.
  simpl. eapply lt_add_range; auto.
  (* call_s *)
  (* monadInv H1. unfold compute_instr_rel_relocentry in *. repeat (monadInv EQ). destr_match_in EQ2. inv EQ2. *)
  (* simpl.  *)
  (* eapply lt_add_range; auto. inv EQ2. *)
  (* (* inv H1.   simpl.  *) *)
  (* (* eapply lt_add_range; auto. *) *)
  (* (* Pbuiltin *) *)
  (* destr_match_in H1. *)
  (* inv H1. inv H1. *)
  (* Pmovw_rm *)
  destruct ad;destruct const;try destruct p;monadInv H.
  monadInv EQ0. simpl.
  eapply lt_add_range; auto.
  
  (* 32 bit *)
  -
    destruct i;intros H;destr_match_in H;try monadInv H. 

  (* only solve Pmov_rs *)  
  unfold compute_instr_abs_relocentry in *. monadInv EQ0.
  simpl;eapply lt_add_range; auto.
            
  1-41: try (destruct a;destruct const;try destruct p;try monadInv H).
  1-41:try (
             unfold compute_instr_disp_relocentry in *;
             try rewrite PTR in *;
             unfold compute_instr_abs_relocentry in *;             
             unfold compute_instr_rel_relocentry in *;
             repeat (monadInv EQ0));
    simpl;try eapply lt_add_range; auto.
  
 
  (* Pjmp_m *)
  destruct base. monadInv H.
  monadInv EQ0. 
  simpl;eapply lt_add_range; auto.
  destruct ofs0. monadInv H.
  monadInv EQ0.
  simpl;eapply lt_add_range; auto.
  monadInv H. monadInv EQ0.
  simpl;eapply lt_add_range; auto.

  (* Pmovw_rm *)
  destruct ad;destruct const;try destruct p;try monadInv H.
  monadInv EQ0. simpl.
  eapply lt_add_range; auto.
Qed.

(* id_eliminate just transforms Pjmp_s to Pjmp_l_rel and leave another instruction forms unchanged *)
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
    instr_eq (rev_id_eliminate (reloc_symb e) (id_eliminate i)) i.
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

End WITH_INSTR_SIZE.
