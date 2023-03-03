Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Asm RelocProg RelocProgram.
Require Import Hex compcert.encode.Bits Memdata Encode.
Require Import LocalLib.
Require Import ReloctablesgenArchi RelocProgSemanticsArchi1.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.


Lemma rev_id_eliminate_size: forall i id addend, instr_size_real i = instr_size_real (rev_id_eliminate id addend i).
Proof.
  destruct i;intros;cbn;auto;
    try (destruct a;destruct const;simpl;auto).
  try (destruct ad;destruct const;simpl;auto).
Qed.


Lemma id_eliminate_size_unchanged:forall i, instr_size_real i = instr_size_real (id_eliminate i).
Proof.
  Transparent addrmode_size.
  destruct i;simpl;auto;
    try (destruct a;destruct ofs;try destruct p;destruct base;destruct const;try destruct p;simpl;auto).

  try (destruct ad;destruct ofs;try destruct p;destruct base;destruct const;try destruct p;simpl;auto).
Qed.
  
Lemma rex_prefix_check_r_bound: forall r,
    0 <= rex_prefix_check_r r.
Proof.
  destruct r;unfold rex_prefix_check_r;destr;simpl;try lia.
Qed.

Lemma rex_prefix_check_fr_bound: forall r,
    0 <= rex_prefix_check_fr r.
Proof.
  destruct r;unfold rex_prefix_check_fr;destr;simpl;try lia.
Qed.

Lemma rex_prefix_check_rr_bound: forall r1 r2,
    0 <= rex_prefix_check_rr r1 r2.
Proof.
  destruct r1;destruct r2;unfold rex_prefix_check_rr;destr;simpl;try lia.
Qed.


Lemma rex_prefix_check_frr_bound: forall r1 r2,
    0 <= rex_prefix_check_frr r1 r2.
Proof.
  destruct r1;destruct r2;unfold rex_prefix_check_frr;destr;simpl;try lia.
Qed.


Lemma rex_prefix_check_a_bound: forall a,
    0 <= rex_prefix_check_a a.
Proof.
  Transparent addrmode_size.
  unfold rex_prefix_check_a.
  destruct a;destruct ofs;try destruct p;destruct base;destruct const;try destruct p;simpl;auto;
  repeat destr;lia.
Qed.

Lemma rex_prefix_check_ra_bound: forall r a,
    0 <= rex_prefix_check_ra r a.
Proof.
  Transparent addrmode_size.
  unfold rex_prefix_check_ra.
  destruct r;
  destruct a;destruct ofs;try destruct p;destruct base;destruct const;try destruct p;simpl;auto;
  repeat destr;lia.
Qed.

Lemma rex_prefix_check_fa_bound: forall r a,
    0 <= rex_prefix_check_fa r a.
Proof.
  Transparent addrmode_size.
  unfold rex_prefix_check_fa.
  destruct r;
  destruct a;destruct ofs;try destruct p;destruct base;destruct const;try destruct p;simpl;auto;
  repeat destr;lia.
Qed.

Lemma addrmode_reloc_offset_bound: forall a,
    0 < addrmode_reloc_offset a < addrmode_size a.
Proof.
  Transparent addrmode_size.
  unfold addrmode_size.
  destruct a;destruct ofs;try destruct p;destruct base;destruct const;try destruct p;simpl;lia.
Qed.

Ltac check_r :=
  match goal with
  | |- context [rex_prefix_check_r ?r] =>
    generalize (rex_prefix_check_r_bound r)
  end.

Ltac check_rr :=
  match goal with
  | |- context [rex_prefix_check_rr ?r1 ?r2] =>
    generalize (rex_prefix_check_rr_bound ?r1 ?r2)
  end.

Ltac check_f :=
  match goal with
  | |- context [rex_prefix_check_fr ?r] =>
    generalize (rex_prefix_check_fr_bound r)
  end.

Ltac check_frr :=
  match goal with
  | |- context [rex_prefix_check_frr ?r1 ?r2] =>
    generalize (rex_prefix_check_frr_bound ?r1 ?r2)
  end.


Ltac check_a :=
  match goal with
  | |- context [rex_prefix_check_a ?a] =>
    generalize (rex_prefix_check_a_bound a)
  end.

Ltac check_ra :=
  match goal with
  | |- context [rex_prefix_check_ra ?r ?a] =>
    generalize (rex_prefix_check_ra_bound r a)
  end.

Ltac check_fa :=
  match goal with
  | |- context [rex_prefix_check_fa ?r ?a] =>
    generalize (rex_prefix_check_fa_bound r a)
  end.

Ltac addrmode_reloc_offset_check:=
  match goal with
  | |- context [addrmode_reloc_offset ?a ] =>
    generalize (addrmode_reloc_offset_bound a)
  end.

Lemma instr_reloc_bound :
  forall i ofs,
    instr_reloc_offset i = OK ofs -> 0 < ofs < instr_size_real i.
Proof.
  unfold instr_size_real.
  destruct i;cbn [instr_reloc_offset];cbn [instr_size_asm];intros;destr_in H;try monadInv H;    
    try check_r;
    try check_f;
    try check_rr;
    try check_frr;
    try check_a;
    try check_ra;
    try check_fa;
    try addrmode_reloc_offset_check;
    try lia.
Qed.

Lemma lt_add_range:forall a b c,
    0 < b < c -> a < a + b < a + c.
Proof. 
  intros. lia.
Qed.

Section WITH_INSTR_SIZE.

Variable instr_size : instruction -> Z.
Hypothesis instr_reloc_bound : forall i ofs, instr_reloc_offset i = OK ofs -> 0 < ofs < instr_size i.

Lemma transl_instr_range': forall ofs i e,
    transl_instr instr_size ofs i = OK (Some e) ->
    ofs < e.(reloc_offset) < ofs + instr_size i.
  intros ofs i e.
  (* generalize (instr_size_bound i). intros A.   *)
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

End WITH_INSTR_SIZE.

Lemma transl_instr_range: forall ofs i e,
    transl_instr instr_size_real ofs i = OK (Some e) ->
    ofs < e.(reloc_offset) < ofs + instr_size_real i.
Proof.
  eapply (transl_instr_range' instr_size_real instr_reloc_bound).
Qed.
