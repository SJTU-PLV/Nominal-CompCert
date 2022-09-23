Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Asm RelocProg RelocProgram.
Require Import Hex compcert.encode.Bits Memdata Encode.
Require Import EncDecRet BPProperty.
Require Import TranslateInstr RelocBinDecode.
Require Import ReloctablesgenArchi RelocProgSemanticsArchi1 ReloctablesgenproofArchi.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.


Lemma instr_eq_size: forall i1 i2,
    RelocBinDecode.instr_eq i1 i2 -> instr_size_asm i1 = instr_size_asm i2.
Proof.
  Transparent instr_size_asm.
  intros. unfold instr_eq in H.
  destruct H. subst. auto.
  destruct Archi.ptr64 eqn:PTR.
  -
  destruct i1;try inv H;destruct i2;try inv H;cbn [instr_size_asm];auto.

  unfold rex_prefix_check_rr,rex_prefix_check_r.
  rewrite PTR. destr.
  apply andb_true_iff in Heqb. destruct Heqb.
  rewrite H. auto.
  apply andb_false_iff in Heqb. destruct Heqb.
  rewrite H. auto.
  rewrite H. auto.

  destruct H11. subst. auto.
  
  -
    destruct i1;try inv H;destruct i2;try inv H;cbn [instr_size_asm];auto.
    
    unfold rex_prefix_check_rr,rex_prefix_check_r.
    rewrite PTR. auto.
    
    destruct H11. subst. auto.

    rewrite PTR. auto.
    rewrite PTR. auto.
Qed.

Lemma rev_id_eliminate_size: forall i id, instr_size_asm i = instr_size_asm (rev_id_eliminate id i).
Proof.
  destruct i;intros;cbn;auto;
    try (destruct a;destruct const;simpl;auto).
  try (destruct ad;destruct const;simpl;auto).
Qed.

Lemma instr_eq_size_reloc: forall i1 i2, instr_eq i1 i2 -> instr_size_asm i1 = instr_size_asm i2.
Proof.
  unfold instr_eq.
  intros. destruct i1;subst;auto.
  destruct i2;try congruence;subst;auto.
Qed.  

Lemma id_eliminate_size_unchanged:forall i, instr_size_asm i = instr_size_asm (id_eliminate i).
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
    instr_reloc_offset i = OK ofs -> 0 < ofs < instr_size_asm i.
Proof.
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

