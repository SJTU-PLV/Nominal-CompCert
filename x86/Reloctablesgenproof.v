(* *******************  *)
(* Author: Jinhua Wu    *)
(* Date:   Sep 16, 2019 *)
(* Last updated: Jul 12, 2022 by Jinhua Wu *)
(* *******************  *)

Require Import Coqlib Errors Maps.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import Reloctablesgen.
Require Import RelocProg RelocProgram RelocProgSemantics.
Require Import LocalLib AsmInject.
Import ListNotations.
Require AsmFacts.


Set Implicit Arguments.

Local Open Scope error_monad_scope.
Open Scope Z_scope.

Lemma code_eliminate_app: forall c1 c2,
    transl_code' (c1++c2) = transl_code' c1 ++ transl_code' c2.
Proof.
  unfold transl_code'.
  eapply map_app.
Qed.

Lemma app_unit_eq:forall T (l1:list T) l2 a1 a2,
    l1 ++ [a1] = l2 ++ [a2] <->
    l1 = l2 /\ a1 = a2.
Proof.
  
  intros.
  split;intros.
  assert (rev (l1++[a1]) = rev (l2++[a2])).
  f_equal. auto.
  rewrite rev_unit in H0. rewrite rev_unit in H0.
  inv H0.
  assert (rev (rev l1) = rev (rev l2)).
  f_equal. auto.
  rewrite rev_involutive in H0.
  rewrite rev_involutive in H0.
  auto.
  destruct H. subst;auto.
Qed.


(** The preservation theorem of relocation table generation is established by decoding the program  *)

(** * Main Preservaiton Proofs *)
Section PRESERVATION.

Variable instr_size : instruction -> Z.
Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.
Hypothesis id_eliminate_size_unchanged:forall i, instr_size i = instr_size (id_eliminate i).

(** Transformation *)
Variable prog: program.
Variable tprog: program.

Let ge := globalenv instr_size prog.
Let tge := globalenv instr_size tprog.

Definition match_prog (p: program) (tp: program) :=
  transf_program instr_size p = OK tp.

Hypothesis TRANSF: match_prog prog tprog.



Lemma rev_transl_code_snd_size:forall n c c1 c2 r1 r2 sz,
    length c = n ->
    fold_left (rev_acc_code instr_size) c (c1,0,r1) = (c2,sz,r2) ->
    sz = code_size instr_size c.
Proof.
  induction n;intros.
  rewrite length_zero_iff_nil in H. subst.
  simpl in *.  inv H0. auto.
  exploit LocalLib.length_S_inv;eauto. intros (l' & a & A & B).
  subst. clear H.
  rewrite fold_left_app in H0. simpl in H0.
  destruct (fold_left (rev_acc_code instr_size) l' (c1, 0, r1)) eqn:FOLD.
  destruct p.
  rewrite code_size_app.
  exploit IHn. apply eq_refl. apply FOLD. intros.
  simpl in H0. destruct r.
  - inv H0. simpl. auto.
  - destruct andb in H0.
    + inv H0. simpl. auto.
    + inv H0. simpl. auto.
Qed.


Lemma rev_transl_code_fst_inv:forall n c r e c1 c2 sz1 sz2 r1 r2
    (BOUND: e.(reloc_offset) >= code_size instr_size c),
    length c = n ->
    fold_left (rev_acc_code instr_size) c ([],0,r++[e]) = (c1, sz1, r1) ->
    fold_left (rev_acc_code instr_size) c ([],0,r) = (c2, sz2, r2) ->
    c1 = c2 /\ ((r1=[]/\r2=[]) \/ r1 = r2++[e]).
Proof.
  induction n;intros.
  rewrite length_zero_iff_nil in H. subst.
  simpl in *. inv H1. inv H0. auto.
  exploit LocalLib.length_S_inv;eauto. intros (l' & a & A & B).
  subst. clear H.
  rewrite fold_left_app in H1,H0. simpl in H1,H0.
  destruct (fold_left (rev_acc_code instr_size) l' ([], 0, r)) eqn:FOLD1. destruct p.
  destruct (fold_left (rev_acc_code instr_size) l' ([], 0, r++[e])) eqn:FOLD2. destruct p.
  rewrite code_size_app in BOUND. simpl in BOUND.
  generalize (instr_size_bound a). intros SZA.
  assert (reloc_offset e >= code_size instr_size l') by lia.
  exploit IHn. apply H. apply eq_refl. apply FOLD2. apply FOLD1.
  clear H.
  intros (A & B). subst.
  
  exploit (rev_transl_code_snd_size). apply eq_refl. eapply FOLD1.
  exploit (rev_transl_code_snd_size). apply eq_refl. eapply FOLD2.
  intros C D. subst.
  destruct B.
  - destruct H;subst. 
    simpl in H1,H0.
    inv H1. inv H0. auto.
  - subst. clear FOLD1 FOLD2.
    destruct r0;simpl in *.
    + assert (DESTR: (reloc_offset e <? code_size instr_size l' + instr_size a)= false).
      { apply Z.ltb_ge. lia. }
      rewrite DESTR in H0. rewrite andb_false_r in H0.
      inv H1. inv H0. simpl. auto.
    + destruct andb in *;inv H1;inv H0;
      simpl;auto.
Qed.

Lemma transl_code_size_aux: forall n c c1 c2 sz symbtbl,
    length c = n ->
    fold_left (acc_instrs instr_size symbtbl) c (OK (0,c1)) = OK (sz,c2) ->
    code_size instr_size c = sz.
Proof.
  induction n;intros.
  - rewrite length_zero_iff_nil in H. subst.
    simpl in *. inv H0. auto.
  - exploit LocalLib.length_S_inv;eauto.
    intros (l' & a & A & B). subst. clear H.    
    rewrite fold_left_app in H0. rewrite code_size_app.
    simpl in H0. unfold acc_instrs in H0 at 1.
    monadInv H0.
    assert (code_size instr_size l' = x).
    eapply IHn;eauto.
    destruct x1;inv EQ2.
    + simpl. auto.
    + simpl. auto.
Qed.


Lemma code_id_eliminate_size_unchanged:forall c,
    code_size instr_size (transl_code' c) = code_size instr_size c.
Proof.
  intros. unfold transl_code'.
  induction c;simpl;auto.
  rewrite IHc. rewrite <- id_eliminate_size_unchanged.
  auto.
Qed.

Lemma transl_instr_range: forall symbtbl ofs i e,
    transl_instr instr_size symbtbl ofs i = OK (Some e) ->
    ofs < e.(reloc_offset) < ofs + instr_size i.
Admitted.

Lemma transl_instr_consistency: forall i symbtbl ofs e,
    transl_instr instr_size symbtbl ofs i = OK (Some e) ->
    rev_id_eliminate (reloc_symb e) (id_eliminate i) = i.
Proof.
  intros i symbtbl ofs e.
  destruct i;simpl;auto;
    unfold transl_instr;simpl;intros H;repeat (monadInv H);
    unfold compute_instr_abs_relocentry in *;
    unfold compute_instr_disp_relocentry in *;
    unfold compute_instr_rel_relocentry in *;
    repeat (monadInv EQ);
    try (destr_in EQ1;inv EQ1;simpl;auto); (* no addrmode finish *)
    try (destruct a;destruct const;try destruct p;try congruence);
  try (monadInv H;
       unfold compute_instr_abs_relocentry in *;
       unfold compute_instr_disp_relocentry in *;
       unfold compute_instr_rel_relocentry in *;
       repeat (monadInv EQ);
       try (destr_in EQ1;inv EQ1;simpl;auto)).
  (* some special *)
  1-2: destr_match_in EQ2;inv EQ2;simpl;auto.
  destr_match_in H;destr_match_in H;try destruct p. monadInv H.
  unfold compute_instr_abs_relocentry in *. repeat (monadInv H).
  monadInv EQ1. destr_in EQ0. inv EQ0.
  simpl. auto.
Qed.

Lemma id_eliminate_unchanged:forall i symbtbl ofs,
    transl_instr instr_size symbtbl ofs i = OK None ->
    id_eliminate i = i.
Proof.
  intros i symbtl ofs.
  destruct i;simpl;auto;
  unfold transl_instr;simpl;intros;repeat (monadInv H);repeat (destr_in H);repeat monadInv H1.
Qed.



Lemma transl_code_consistency_aux:forall n c r1 r2 symbtbl,
    length c = n ->
    Forall (fun e => e.(reloc_offset) > code_size instr_size c) r2 ->
    transl_code instr_size symbtbl c = OK r1 ->
    fold_left (rev_acc_code instr_size) (transl_code' c) ([], 0, r1++r2) = (c, code_size instr_size c, r2).
Proof.
  induction n;intros c r1 r2 symbtbl H FORALL H0.
  rewrite length_zero_iff_nil in H. subst.
  unfold transl_code in H0. simpl in *. inv H0.
  simpl. eauto.

  exploit LocalLib.length_S_inv;eauto.
  intros (l' & a & A & B). subst. clear H.
  rewrite code_eliminate_app.
  rewrite fold_left_app.
  destruct ((fold_left (rev_acc_code instr_size) (transl_code' l') ([], 0, r1++r2))) eqn:FOLD. destruct p.
  
  unfold transl_code in H0.
  monadInv H0. rewrite fold_left_app in EQ. simpl in EQ.
  unfold acc_instrs in EQ at 1. monadInv EQ.
  destruct x2.

  - inv EQ2.
    (* prove r = [r0] ++ r2 *)
    rewrite <- app_assoc in FOLD.
    (* x0 = code_size l' *)
    exploit transl_code_size_aux;eauto. intros CODESZ. subst.
    (* relocation entry size property *)
    exploit transl_instr_range;eauto. intros RANGE.
    assert (REQ: fold_left (rev_acc_code instr_size) (transl_code' l') ([],0, x1++[r0]++r2) = (l',code_size instr_size l', [r0]++r2)).
    { eapply IHn;eauto.
      (* Forall offset *)
      simpl. constructor. lia.
      eapply Forall_impl with (P:= (fun e : relocentry =>
              reloc_offset e > code_size instr_size (l' ++ [a]))).
      rewrite code_size_app. simpl. intros. lia. auto.
      unfold transl_code.
      rewrite EQ0. simpl. auto. }
    rewrite FOLD in REQ. inv REQ.
    simpl.
    (* id_eliminate size unchanged *)
    repeat rewrite <- id_eliminate_size_unchanged.
    assert ((code_size instr_size l' <? reloc_offset r0) &&
            (reloc_offset r0 <? code_size instr_size l' + instr_size a) = true).
    apply andb_true_iff. repeat rewrite Z.ltb_lt.
    auto.
    rewrite H.
    rewrite code_size_app. simpl. f_equal;f_equal;auto.
    exploit transl_instr_consistency;eauto.
    intros. rewrite H0. auto.
  - assert (REQ: fold_left (rev_acc_code instr_size) (transl_code' l') ([],0, r1++r2) = (l',code_size instr_size l', r2)).
    { eapply IHn;auto.
      (* Forall offset *)
      eapply Forall_impl with (P:= (fun e : relocentry =>
              reloc_offset e > code_size instr_size (l' ++ [a]))).
      rewrite code_size_app. simpl. intros.
      generalize (instr_size_bound a). intros.
      lia. auto.
      unfold transl_code.
      rewrite EQ0. inv EQ2. simpl. auto. }
    rewrite FOLD in REQ. inv REQ. inv EQ2.
    simpl.
    rewrite code_size_app.
    destruct r2.
    + rewrite <- id_eliminate_size_unchanged. f_equal;f_equal;auto.
      erewrite id_eliminate_unchanged;eauto.
    + inv FORALL.
      assert ((reloc_offset r <?
               code_size instr_size l' + instr_size (id_eliminate a)) = false).
      apply Z.ltb_ge. rewrite code_size_app in H1. simpl in H1.
      rewrite <- id_eliminate_size_unchanged.  lia.
      rewrite H. rewrite andb_false_r.
      rewrite <- id_eliminate_size_unchanged. simpl.
      f_equal;f_equal;auto.
      erewrite id_eliminate_unchanged;eauto.
Qed.

        
Lemma transl_code_consistency: forall n c symbtbl reloctbl,
    length c = n ->
    transl_code instr_size symbtbl c = OK reloctbl ->
    rev_transl_code instr_size reloctbl (transl_code' c) = c.
Proof.
  unfold rev_transl_code. intros.
  exploit transl_code_consistency_aux;eauto.
  rewrite app_nil_r.
  destruct fold_left. destruct p.
  simpl. intros. inv H1. auto.
Qed.

