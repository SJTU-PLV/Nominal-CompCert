(* *******************  *)
(* Author: Jinhua Wu    *)
(* Date:   Sep 16, 2019 *)
(* Last updated: Jul 12, 2022 by Jinhua Wu *)
(* *******************  *)

Require Import Coqlib Errors Maps.
Require Import Integers Floats AST RelocProgLinking Linking.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import Reloctablesgen.
Require Import RelocProg RelocProgram RelocProgSemantics RelocProgSemantics1.
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


Remark in_norepet_unique:
  forall T n (gl: list (ident * T)) id g,
    length gl = n ->
  In (id, g) gl -> list_norepet (map fst gl) ->
  exists gl1 gl2, gl = gl1 ++ (id, g) :: gl2 /\ ~In id (map fst gl2) /\ ~In id (map fst gl1).
Proof.
  induction n;intros.
  rewrite length_zero_iff_nil in H. subst.
  unfold transl_code in H0. simpl in *. inv H0.

  exploit LocalLib.length_S_inv;eauto.
  intros (l1 & a1 & A1 & B1).
  assert (exists l2 a2, gl = a2::l2 /\ length l2 = n).
  { destruct gl. simpl in H. congruence.
    exists gl,p. auto. }
  destruct H2 as (l2 & a2 & A2 & B2).
  subst.
  destruct l1.
  - simpl in *. inv A2.
    destruct H0;subst.
    exists [],[]. simpl. auto.
    apply False_rect;auto.      (* can not use congruence, why? *)
  - simpl in *. inv A2.
    destruct H0;subst.
    + exists [],(l1++[a1]).
      inv H1. simpl. auto.
    + inv H1.
      exploit IHn;eauto. intros (gl1 & gl2 & X & Y & Z).
      rewrite X in *. exists (a2::gl1),gl2.
      simpl. split;auto.
      split;auto. clear IHn.
      rewrite map_app in H4. simpl in H4.
      apply not_in_app in H4. destruct H4.
      unfold not.
      apply Decidable.not_or_iff. split. 
      * intros. subst. apply not_in_cons in H2. destruct H2.
        congruence.
      * auto.
Qed.

(** The preservation theorem of relocation table generation is established by decoding the program  *)

(** * Main Preservaiton Proofs *)
Section PRESERVATION.

Variable instr_size : instruction -> Z.
Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.
Hypothesis instr_reloc_bound : forall i ofs, instr_reloc_offset i = OK ofs -> 0 < ofs < instr_size i.

Hypothesis id_eliminate_size_unchanged:forall i, instr_size i = instr_size (id_eliminate i).

(** *Consistency Theorem *)

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

Lemma transl_instr_range: forall symbtbl ofs i e,
    transl_instr instr_size symbtbl ofs i = OK (Some e) ->
    ofs < e.(reloc_offset) < ofs + instr_size i.
  intros symbtbl ofs i e.
  generalize (instr_size_bound i). intros A.  
  unfold transl_instr.
  destruct i;simpl;intros;inv H.

  (* only solve Pmov_rs *)  
  monadInv H1.
  unfold compute_instr_abs_relocentry in *. monadInv EQ.
  destr_match_in EQ1;inv EQ1;simpl;eapply lt_add_range; auto.
            
  1-42: try (destruct a;destruct const;try destruct p;inv H1).
  1-42: try (monadInv H0;
             destruct Archi.ptr64;
        unfold compute_instr_abs_relocentry in *;
       unfold compute_instr_disp_relocentry in *;
       unfold compute_instr_rel_relocentry in *;
       repeat (monadInv EQ));
    try (destr_match_in EQ1;inv EQ1;simpl).

  1-79: try (eapply lt_add_range; auto).

  1-42 : try(destr_match_in EQ2;inv EQ2;simpl;
             eapply lt_add_range; auto).
  
  (* Pjmp_s *)
  destruct Archi.ptr64. monadInv H1.
  unfold compute_instr_rel_relocentry in *.
  monadInv EQ.
  destr_match_in EQ2;inv EQ2;simpl;eapply lt_add_range; auto.
  inv H1. simpl. eapply lt_add_range; auto.
  (* Pjmp_m *)
  destruct base. monadInv H0.
  unfold compute_instr_abs_relocentry in *.
  monadInv EQ. 
  destr_match_in EQ1;inv EQ1;simpl;eapply lt_add_range; auto.
  destruct ofs0. monadInv H0.
  unfold compute_instr_abs_relocentry in *.
  monadInv EQ.
  destr_match_in EQ1;inv EQ1;simpl;eapply lt_add_range; auto.
  try (monadInv H0;
             destruct Archi.ptr64;
        unfold compute_instr_abs_relocentry in *;
       unfold compute_instr_disp_relocentry in *;
       unfold compute_instr_rel_relocentry in *;
       repeat (monadInv EQ));
    try (destr_match_in EQ1;inv EQ1;simpl).
  destr_match_in EQ2;inv EQ2;simpl;eapply lt_add_range; auto.
  eapply lt_add_range; auto.
  (* call_s *)
  destruct Archi.ptr64.
  monadInv H1. unfold compute_instr_rel_relocentry in *. repeat (monadInv EQ). destr_match_in EQ2. inv EQ2.
  simpl. 
  eapply lt_add_range; auto. inv EQ2.
  inv H1.   simpl. 
  eapply lt_add_range; auto.
  (* Pbuiltin *)
  destr_match_in H1.
  inv H1. inv H1.
  (* Pmovw_rm *)
  destruct ad;destruct const;try destruct p;inv H1.
  monadInv H0. destruct Archi.ptr64.
  unfold compute_instr_rel_relocentry in *.
  monadInv EQ. destr_match_in EQ2. inv EQ2. simpl.
  eapply lt_add_range; auto.
  inv EQ2.
  unfold compute_instr_abs_relocentry in *.
  monadInv EQ. destr_match_in EQ1. inv EQ1. simpl.
  eapply lt_add_range; auto. inv EQ1.
Qed.

Lemma transl_instr_consistency: forall i symbtbl ofs e,
    transl_instr instr_size symbtbl ofs i = OK (Some e) ->
    rev_id_eliminate (reloc_symb e) (id_eliminate i) = i.
Proof.
  intros i symbtbl ofs e.
  destruct i;simpl;auto;
    unfold transl_instr;simpl;intros H;repeat (monadInv H);
      unfold compute_instr_disp_relocentry in *;
      destruct Archi.ptr64;
      unfold compute_instr_abs_relocentry in *;      
    unfold compute_instr_rel_relocentry in *;
    repeat (monadInv EQ);
    try (destruct (symbtbl ! id);inv EQ1;simpl;auto); (* no addrmode finish *)
    try (destruct a;destruct const;try destruct p;try congruence);
  try (monadInv H;
       unfold compute_instr_abs_relocentry in *;
       unfold compute_instr_disp_relocentry in *;
       unfold compute_instr_rel_relocentry in *;
       repeat (monadInv EQ);
       try (destr_in EQ1;inv EQ1;simpl;auto)).

  1-45: try (destruct PTree.get;inv EQ2;simpl;auto).
  1-4 : simpl;auto.
  (* Pjmp_m *)
  destruct base. monadInv H.
  monadInv EQ. destruct PTree.get;inv EQ1;simpl;auto.
  destruct ofs0. monadInv H.
  monadInv EQ. destruct PTree.get;inv EQ1;simpl;auto.
  monadInv H. monadInv EQ.
  destruct PTree.get;inv EQ2;simpl;auto.
  destruct base. monadInv H.
  monadInv EQ. destruct PTree.get;inv EQ1;simpl;auto.
  destruct ofs0. monadInv H.
  monadInv EQ. destruct PTree.get;inv EQ1;simpl;auto.
  monadInv H. monadInv EQ.
  destruct PTree.get;inv EQ1;simpl;auto.

  (* Pmovw *)
  destruct ad;destruct const;try destruct p;try congruence.
  monadInv H. monadInv EQ. destruct PTree.get;inv EQ2;simpl;auto.
  destruct ad;destruct const;try destruct p;try congruence.
  monadInv H. monadInv EQ. destruct PTree.get;inv EQ1;simpl;auto.
  
Qed.

Lemma id_eliminate_unchanged:forall i symbtbl ofs,
    transl_instr instr_size symbtbl ofs i = OK None ->
    id_eliminate i = i.
Proof.
  intros i symbtl ofs.
  destruct i;simpl;auto;
  unfold transl_instr;simpl;intros;repeat (monadInv H);repeat (destr_in H);repeat monadInv H1.
Qed.

Lemma code_eliminate_unchanged:forall n c symbtbl,
    length c = n ->
    transl_code instr_size symbtbl c = OK [] ->
    transl_code' c = c.
Proof.  
  induction n;intros.
  rewrite length_zero_iff_nil in H. subst.
  simpl. auto.
  
  exploit LocalLib.length_S_inv;eauto.
  intros (l' & a & A & B). subst.
  unfold transl_code' in *.
  rewrite map_app.
  unfold transl_code in H0. monadInv H0.
  rewrite fold_left_app in EQ.
  simpl in EQ. unfold acc_instrs in EQ at 1.
  monadInv EQ. destruct x2. inv EQ2.
  destruct x1;simpl in H2;inv H2. 
  inv EQ2.
  exploit IHn;eauto. unfold transl_code. erewrite EQ0.
  simpl. auto. intro. rewrite H0. simpl.
  erewrite id_eliminate_unchanged;eauto.
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

Lemma PTree_map_map_aux: forall A B C m n (f:positive -> A -> B) (g:positive -> B -> C),
    PTree.xmap g (PTree.xmap f m n) n = PTree.xmap (fun p ele => g p (f p ele)) m n.
Proof.
  intros A B C.
  induction m;intros.
  - simpl. auto.
  - simpl. destruct o.
    + rewrite <- IHm1.
      rewrite <- IHm2.
      f_equal.
    + rewrite <- IHm1.
      rewrite <- IHm2.
      f_equal.
Qed.

Theorem PTree_map_map:forall A B C m (f:positive -> A -> B) (g:positive -> B -> C),
    PTree.map g (PTree.map f m) = PTree.map (fun p ele => g p (f p ele)) m.
Proof.
  unfold PTree.map. intros.
  eapply PTree_map_map_aux.
Qed.

Lemma PTree_map_id_aux:forall A m n (f:positive -> A -> A),
    (forall id ele, m ! id = Some ele -> f (PTree.prev_append n id) ele = ele) ->
    PTree.xmap f m n = m.
Proof.
  intros A.
  induction m;intros.
  simpl;auto.
  

  destruct o. 
  + generalize (H 1%positive a). simpl.
    unfold PTree.prev. intros B.
    generalize (B  eq_refl). intros C.
    rewrite C.

    rewrite IHm1;auto. rewrite IHm2;auto.
    * intros. generalize (H (id~1)%positive ele).
      simpl. intros. apply H1. auto.
    * intros. generalize (H (id~0)%positive ele).
      simpl. intros. apply H1. auto.
    
  + simpl. rewrite IHm1;auto. rewrite IHm2;auto.
    * intros. generalize (H (id~1)%positive ele).
      simpl. intros. apply H1. auto.
    * intros. generalize (H (id~0)%positive ele).
      simpl. intros. apply H1. auto.
Qed.

Lemma PTree_map_id:forall A m (f:positive -> A -> A),
    (forall id ele, m ! id = Some ele -> f id ele = ele) ->
    PTree.map f m = m.
Proof.
  intros. unfold PTree.map.
  apply PTree_map_id_aux.
  simpl. auto.
Qed.


Lemma transl_sections_consistency:forall sectbl symbtbl reloc_map,
    transl_sectable instr_size symbtbl sectbl = OK reloc_map ->
    PTree.map (rev_section instr_size reloc_map) (transl_sectable' sectbl) = sectbl.
Proof.
  unfold transl_sectable,transl_sectable'.
  intros.
  rewrite PTree_map_map.
  rewrite PTree_map_id;auto.
  intros. unfold rev_section.
  destruct ele;simpl;auto.
  apply PTree.elements_correct in H0.
  generalize (PTree.elements_keys_norepet sectbl).
  intros NOREP.
  exploit (in_norepet_unique);eauto.
  intros (gl1 & gl2 & A & B & C).
  rewrite PTree.fold_spec in H.
  (* unable to rewrite, use set printing all to find the problem *)
  unfold section in *.
  rewrite A in H.
  rewrite fold_left_app in H. simpl in H.
  fold section in *.
  set (f:= (fun (a : res reloctable_map)
           (p : positive * section) =>
              acc_section instr_size symbtbl a (fst p) (snd p))) in *.
  (* preservaiton for Error *)
  assert (ERRPRS: forall l msg, fold_left f l (Error msg) = Error msg).
  { induction l. simpl. auto.
    simpl. auto. }
  (* prove preservaiton for geting None*)
  assert (PRS: forall l reloc_map1 reloc_map2,
               ~ In id fst ## l ->
               fold_left f l (OK reloc_map1) = OK reloc_map2 ->
               reloc_map2 ! id = reloc_map1 ! id).
  { induction l;simpl;intros.
    inv H2. auto.
    destruct transl_section in H2. simpl in H2. destruct r.
    eapply IHl;eauto.
    assert ((PTree.set (fst a) (r :: r0) reloc_map1) ! id = reloc_map1 ! id).
    rewrite PTree.gsspec. apply Decidable.not_or in H1.
    destruct H1. destruct peq;try congruence;auto.
    rewrite <- H3.
    unfold reloctable in *.
    eapply IHl;eauto.
    simpl in H2. rewrite ERRPRS in H2. inv H2. }
    
  destruct (acc_section instr_size symbtbl
           (fold_left f gl1 (OK (PTree.empty reloctable))) id
           (sec_text code)) eqn:ACC in H;
    unfold section,ident in *;rewrite ACC in H.  
  - unfold acc_section in ACC.
    monadInv ACC. destruct x0.
    + inv EQ2.
      simpl in EQ1. monadInv EQ1.
      exploit PRS.
      apply C. eauto. intros.
      exploit PRS. apply B. eauto.
      intros. rewrite PTree.gempty in H1. rewrite H2. rewrite H1.
      f_equal.
      erewrite code_eliminate_unchanged;eauto.              
    + inv EQ2.
      simpl in EQ1. monadInv EQ1.
      exploit PRS.
      apply B. eauto. intros.
      rewrite PTree.gss in H1. rewrite H1.
      f_equal. erewrite transl_code_consistency;eauto.
  - rewrite ERRPRS in H. inv H.
Qed.


(** Transformation *)
Variable prog: program.
Variable tprog: program.

Let ge := RelocProgSemantics.globalenv instr_size prog.
Let tge := globalenv instr_size tprog.

Definition match_prog (p: program) (tp: program) :=
  transf_program instr_size p = OK tp.

Hypothesis TRANSF: match_prog prog tprog.  

Lemma globalenv_eq: globalenv instr_size tprog = RelocProgSemantics.globalenv instr_size prog.
  unfold match_prog in  TRANSF. unfold transf_program in TRANSF.
  monadInv TRANSF.
  unfold globalenv,RelocProgSemantics.globalenv.
  simpl. f_equal.
  erewrite transl_sections_consistency;eauto.
Qed.

Lemma transf_initial_state:forall st1 rs1,
    RelocProgSemantics.initial_state instr_size prog rs1 st1 ->
    initial_state instr_size tprog rs1 st1.
Proof.
  intros st1 rs1 INIT. inv INIT.
  unfold match_prog in TRANSF. unfold transf_program in TRANSF.
  monadInv TRANSF. clear ge tge.
  
  econstructor;eauto. unfold decode_program. simpl.
  apply RelocProgSemantics.initial_state_intro with (m:=m).
  unfold init_mem in *. simpl in *.
  unfold globalenv in *. simpl.
  erewrite transl_sections_consistency;eauto.

  inv H0. econstructor;eauto.
Qed.

Lemma transf_program_correct:
  forall rs, Smallstep.forward_simulation (RelocProgSemantics.semantics instr_size prog rs) (semantics instr_size tprog rs).
Proof.
  intros rs.  
  eapply Smallstep.forward_simulation_step with (match_states:= fun (x y:Asm.state) => x = y).
  - unfold match_prog in TRANSF. unfold transf_program in TRANSF.
    monadInv TRANSF. simpl;auto.    
  - intros. exists s1. split;auto. apply transf_initial_state. auto.
  - intros;subst. simpl in *. auto.
  - intros. exists s1'. split;auto.
    rewrite <- H0. auto.
    unfold semantics. simpl in *.
    rewrite globalenv_eq. auto.
Qed.

End PRESERVATION.

Instance reloctablesgen_transflink (instr_size: instruction -> Z): TransfLink (match_prog instr_size).
Admitted.

