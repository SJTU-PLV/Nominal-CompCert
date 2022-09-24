Require Import Coqlib Errors Maps Memory.
Require Import Integers Floats AST RelocProgLinking Linking.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import Reloctablesgen ReloctablesgenArchi.
Require Import RelocProg RelocProgram RelocProgSemantics RelocProgSemantics1.
Require Import RelocProgSemanticsArchi RelocProgSemanticsArchi1.
Require Import ReloctablesgenproofArchi.
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

Section INSTR_MAP.
  Variable instr_size : instruction -> Z.
  Hypothesis instr_eq_size: forall i1 i2, instr_eq i1 i2 -> instr_size i1 = instr_size i2.
  
(* gen_code_map properties *)
Lemma gen_instr_map_pres_eq_aux: forall n c c',
      length c = n ->
      Forall2 instr_eq c c' ->
      fst (fold_left (acc_instr_map instr_size) c (Ptrofs.zero, fun _ : ptrofs => None)) =
      fst (fold_left (acc_instr_map instr_size) c' (Ptrofs.zero, fun _ : ptrofs => None)).
Proof.
  induction n;intros.
  rewrite length_zero_iff_nil in H. subst.
  inv H0. simpl. auto.
  
  exploit LocalLib.length_S_inv;eauto.
  intros (l1 & a1 & A1 & B1).
  subst. eapply Forall2_app_inv_l in H0.
  destruct H0 as (l1' & l2' & P1 & P2 & P3).
  inv P2. inv H4.
  repeat rewrite fold_left_app.  simpl.
  unfold acc_instr_map at 1 3.
  destruct (fold_left (acc_instr_map instr_size) l1 (Ptrofs.zero, fun _ : ptrofs => None)) eqn:FOLD.
  destruct (fold_left (acc_instr_map instr_size) l1' (Ptrofs.zero, fun _ : ptrofs => None)) eqn:FOLD1.
  simpl. erewrite instr_eq_size;eauto.
  exploit IHn;eauto. rewrite FOLD,FOLD1.
  simpl. intros. subst. auto.
Qed.

Lemma gen_instr_map_pres_eq: forall n c c' i,
    length c = n ->
    Forall2 instr_eq c c' ->
    option_rel instr_eq (gen_instr_map instr_size c i) (gen_instr_map instr_size c' i).
Proof.
  induction n;intros.
  rewrite length_zero_iff_nil in H. subst.
  inv H0. unfold gen_instr_map. simpl. constructor.
  
  exploit LocalLib.length_S_inv;eauto.
  intros (l1 & a1 & A1 & B1).
  subst. eapply Forall2_app_inv_l in H0.
  destruct H0 as (l1' & l2' & P1 & P2 & P3).
  inv P2. inv H4. unfold gen_instr_map.
  repeat rewrite fold_left_app. simpl.
  unfold acc_instr_map at 1 3.
  destruct (fold_left (acc_instr_map instr_size) l1 (Ptrofs.zero, fun _ : ptrofs => None)) eqn:FOLD.
  destruct (fold_left (acc_instr_map instr_size) l1' (Ptrofs.zero, fun _ : ptrofs => None)) eqn:FOLD1.
  destr.
  - exploit gen_instr_map_pres_eq_aux.
    2: eapply P1. eauto.
    rewrite FOLD,FOLD1. simpl. intros. subst.
    destr. constructor. auto.
  - exploit gen_instr_map_pres_eq_aux.
    2: eapply P1. eauto.
    rewrite FOLD,FOLD1. simpl. intros. subst.
    destr. exploit IHn;eauto.
    unfold gen_instr_map. rewrite FOLD,FOLD1.
    eauto.
Qed.

End INSTR_MAP.



(** The preservation theorem of relocation table generation is established by decoding the program  *)

(** * Main Preservaiton Proofs *)
Section PRESERVATION.

Variable instr_size : instruction -> Z.
Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.

Hypothesis id_eliminate_size_unchanged:forall i, instr_size i = instr_size (id_eliminate i).
Hypothesis instr_reloc_bound : forall i ofs, instr_reloc_offset i = OK ofs -> 0 < ofs < instr_size i.
Hypothesis instr_eq_size: forall i1 i2, instr_eq i1 i2 -> instr_size i1 = instr_size i2.

Definition match_prog (p: program) (tp: program) :=
  transf_program instr_size p = OK tp.

Lemma transf_program_match:
  forall p tp, transf_program instr_size p = OK tp -> match_prog p tp.
Proof.
  auto.
Qed.



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

Lemma transl_code_size_aux: forall n c c1 c2 sz,
    length c = n ->
    fold_left (acc_instrs instr_size) c (OK (0,c1)) = OK (sz,c2) ->
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


Lemma code_eliminate_unchanged:forall n c,
    length c = n ->
    transl_code instr_size c = OK [] ->
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


Lemma transl_code_consistency_aux:forall n c r1 r2,
    length c = n ->
    Forall (fun e => e.(reloc_offset) > code_size instr_size c) r2 ->
    transl_code instr_size c = OK r1 ->
    exists c', fold_left (rev_acc_code instr_size) (transl_code' c) ([], 0, r1++r2) = (c', code_size instr_size c, r2)
          /\ Forall2 instr_eq c' c.
Proof.
  induction n;intros c r1 r2 H FORALL H0.
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
    assert (REQ: exists l'', fold_left (rev_acc_code instr_size) (transl_code' l') ([],0, x1++[r0]++r2) = (l'',code_size instr_size l', [r0]++r2) /\ Forall2 instr_eq l'' l').
    { eapply IHn;eauto.
      (* Forall offset *)
      simpl. constructor. lia.
      eapply Forall_impl with (P:= (fun e : relocentry =>
              reloc_offset e > code_size instr_size (l' ++ [a]))).
      rewrite code_size_app. simpl. intros. lia. auto.
      unfold transl_code.
      rewrite EQ0. simpl. auto. }
    rewrite FOLD in REQ. destruct REQ as (l'' & A1 & A2). inv A1.
    simpl.
    (* id_eliminate size unchanged *)
    repeat rewrite <- id_eliminate_size_unchanged.
    assert ((code_size instr_size l' <? reloc_offset r0) &&
            (reloc_offset r0 <? code_size instr_size l' + instr_size a) = true).
    apply andb_true_iff. repeat rewrite Z.ltb_lt.
    auto.
    rewrite H.
    rewrite code_size_app. simpl. eexists. split. f_equal;f_equal;auto.
    eapply Forall2_app. auto.
    exploit transl_instr_consistency;eauto.
  - assert (REQ: exists l'', fold_left (rev_acc_code instr_size) (transl_code' l') ([],0, r1++r2) = (l'',code_size instr_size l', r2) /\ Forall2 instr_eq l'' l').
    { eapply IHn;auto.
      (* Forall offset *)
      eapply Forall_impl with (P:= (fun e : relocentry =>
              reloc_offset e > code_size instr_size (l' ++ [a]))).
      rewrite code_size_app. simpl. intros.
      generalize (instr_size_bound a). intros.
      lia. auto.
      unfold transl_code.
      rewrite EQ0. inv EQ2. simpl. auto. }
    rewrite FOLD in REQ. destruct REQ as (l'' & A1 & A2). inv A1. 
    simpl.
    rewrite code_size_app.
    destruct r2.
    + rewrite <- id_eliminate_size_unchanged.
      eexists. split.
      f_equal;f_equal;auto.
      erewrite id_eliminate_unchanged;eauto.
      eapply Forall2_app. auto.
      constructor;auto.
      eapply instr_eq_refl.
    + inv FORALL.
      assert ((reloc_offset r <?
               code_size instr_size l' + instr_size (id_eliminate a)) = false).
      apply Z.ltb_ge. rewrite code_size_app in H1. simpl in H1.
      rewrite <- id_eliminate_size_unchanged.  lia.
      rewrite H. rewrite andb_false_r.
      rewrite <- id_eliminate_size_unchanged. simpl.
      eexists. split.
      f_equal;f_equal;auto.
      erewrite id_eliminate_unchanged;eauto.
      eapply Forall2_app. auto.
      constructor;auto.
      eapply instr_eq_refl.
Qed.

        
Lemma transl_code_consistency: forall n c reloctbl,
    length c = n ->
    transl_code instr_size c = OK reloctbl ->
    exists c', rev_transl_code instr_size reloctbl (transl_code' c) = c' /\ Forall2 instr_eq c' c.
Proof.
  unfold rev_transl_code. intros.
  exploit transl_code_consistency_aux;eauto.
  rewrite app_nil_r.
  destruct fold_left. destruct p.
  simpl. intros. destruct H1 as (c' & A1 & A2). inv A1.
  eexists. split;eauto.
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



Definition section_eq (sec1 sec2:section) :=
  match sec1, sec2 with
  | sec_text c1, sec_text c2 =>
    Forall2 instr_eq c1 c2
  | sec_rwdata d1, sec_rwdata d2 =>
    d1 = d2
  | sec_rodata d1, sec_rodata d2 =>
    d1 = d2
  | _,_ => False
  end.

Lemma transl_sections_consistency:forall sectbl reloc_map,
    transl_sectable instr_size sectbl = OK reloc_map ->
     forall id, option_rel section_eq (PTree.map (rev_section instr_size reloc_map) (transl_sectable' sectbl))!id sectbl!id.
Proof.
  unfold transl_sectable,transl_sectable'.
  intros.
  rewrite PTree_map_map.

  rewrite PTree.gmap. unfold option_map.
  destr;unfold section in *;
  rewrite Heqo;constructor.

  unfold section_eq.
  destruct s.
  - simpl. 
    apply PTree.elements_correct in Heqo.
    generalize (PTree.elements_keys_norepet sectbl).
    intros NOREP.
    exploit (in_norepet_unique);eauto.
    intros (gl1 & gl2 & A & B & C).
    rewrite PTree.fold_spec in H.
    unfold section in *.
    rewrite A in H.
    rewrite fold_left_app in H. simpl in H.
    fold section in *.
    set (f:= (fun (a : res reloctable_map)
           (p : positive * section) =>
                acc_section instr_size a (fst p) (snd p))) in *.
    assert (ERRPRS: forall l msg, fold_left f l (Error msg) = Error msg).
  { induction l. simpl. auto.
    simpl. auto. }
  (* prove preservaiton for geting None*)
  assert (PRS: forall l reloc_map1 reloc_map2,
               ~ In id fst ## l ->
               fold_left f l (OK reloc_map1) = OK reloc_map2 ->
               reloc_map2 ! id = reloc_map1 ! id).
  { induction l;simpl;intros.
    inv H1. auto.
    destruct transl_section in H1. simpl in H1. destruct r.
    eapply IHl;eauto.
    assert ((PTree.set (fst a) (r :: r0) reloc_map1) ! id = reloc_map1 ! id).
    rewrite PTree.gsspec. apply Decidable.not_or in H0.
    destruct H0. destruct peq;try congruence;auto.
    rewrite <- H2.
    unfold reloctable in *.
    eapply IHl;eauto.
    simpl in H1. rewrite ERRPRS in H1. inv H1. }
  destruct (acc_section instr_size
                        (fold_left f gl1 (OK (PTree.empty reloctable))) id
                        (sec_text code)) eqn:ACC in H;
    unfold section,ident in *;rewrite ACC in H.
    + unfold acc_section in ACC.
      monadInv ACC. destruct x0.
      * inv EQ2.
        simpl in EQ1. monadInv EQ1.
        exploit PRS.
        apply C. eauto. intros.
        exploit PRS. apply B. eauto.
        intros. rewrite H1. rewrite H0.
        rewrite PTree.gempty.
        erewrite code_eliminate_unchanged;eauto.
        clear. induction code. constructor.
        constructor;auto. eapply instr_eq_refl. 
      * inv EQ2.
        simpl in EQ1. monadInv EQ1.
        exploit PRS.
        apply B. eauto. intros.
        rewrite PTree.gss in H0. rewrite H0.
        exploit transl_code_consistency;eauto.
        intros (c' & A1 & A2). rewrite A1. auto.
    +  rewrite ERRPRS in H. inv H.
    
  - simpl. auto.
  - simpl. auto.
Qed.

Lemma code_eq_size: forall c1 c2,
    Forall2 instr_eq c1 c2 ->
    code_size instr_size c1 = code_size instr_size c2.
Proof.
  induction c1;intros. simpl.
  inv H. auto.
  inv H. simpl. erewrite IHc1;eauto.
  erewrite instr_eq_size;eauto.
Qed.

(* init_mem equal *)
Lemma alloc_sections_eq: forall sectbl sectbl' ge1 ge2 m m',
    RelocProgGlobalenvs.Genv.genv_symb ge1 = RelocProgGlobalenvs.Genv.genv_symb ge2 ->
    (forall id, option_rel section_eq sectbl'!id sectbl!id) ->
    alloc_sections instr_size ge1 sectbl m = Some m' ->
    alloc_sections instr_size ge2 sectbl' m = Some m'.
Proof.
  unfold alloc_sections.
  intros.
  rewrite PTree.fold_spec in *.
  eapply PTree.elements_canonical_order' in H0.
  set (l1:= (PTree.elements sectbl')) in *.
  set (l2:= (PTree.elements sectbl)) in *.
  generalize (list_length_exists l1). intros (n & LEN).
  generalize n l1 LEN l2  m m' H0 H1. clear n l1 LEN l2 m m' H0 H1.
  induction n;intros.
  rewrite length_zero_iff_nil in LEN. subst.
  inv H0. 
  simpl in *. auto.
  
  exploit LocalLib.length_S_inv;eauto.
  intros (l' & a & A & B). subst.
  eapply list_forall2_app_inv_l in H0.
  destruct H0 as (l4 & l5 & P1 & P2 & P3).
  inv P3. inv H5. destruct H3.
  rewrite fold_left_app in *.
  simpl in *. unfold alloc_section at 1.
  unfold alloc_section in H1 at 1.
  rewrite H0. clear H0.
  destr_in H1.
  exploit IHn;eauto. intros Q. rewrite Q.
  unfold section_eq in H2. destr_in H2. 
  - destr_in H2. simpl in *.
    erewrite code_eq_size;eauto.
  - destr_in H1. subst.
    simpl in *.
    destruct Mem.alloc_glob. destr.
    erewrite store_init_data_list_pres.
    eauto. auto. intros.
    unfold RelocProgGlobalenvs.Genv.find_symbol. rewrite H.
    auto.
  - destr_in H1. subst.
    simpl in *.
    destruct Mem.alloc_glob. destr.
    erewrite store_init_data_list_pres.
    eauto. auto. intros.
    unfold RelocProgGlobalenvs.Genv.find_symbol. rewrite H.
    auto.
Qed.

    
(** Transformation *)
Variable prog: program.
Variable tprog: program.

Let ge := RelocProgSemantics.globalenv instr_size prog.
Let tge := globalenv instr_size tprog.

Hypothesis TRANSF: match_prog prog tprog.  

Lemma genv_symb_eq: RelocProgGlobalenvs.Genv.genv_symb ge =  RelocProgGlobalenvs.Genv.genv_symb tge.
  unfold match_prog in  TRANSF. unfold transf_program in TRANSF.
  monadInv TRANSF.
  unfold globalenv,RelocProgSemantics.globalenv.
  simpl. auto.
Qed.

Lemma genv_ext_funs_eq: RelocProgGlobalenvs.Genv.genv_ext_funs ge =  RelocProgGlobalenvs.Genv.genv_ext_funs tge.
  unfold match_prog in  TRANSF. unfold transf_program in TRANSF.
  monadInv TRANSF.
  unfold globalenv,RelocProgSemantics.globalenv.
  simpl. auto.
Qed.


                     
Lemma genv_instr_eq: forall v, option_rel instr_eq (RelocProgGlobalenvs.Genv.find_instr tge v) (RelocProgGlobalenvs.Genv.find_instr ge v).
  unfold match_prog in  TRANSF. unfold transf_program in TRANSF.
  monadInv TRANSF.
  unfold globalenv,RelocProgSemantics.globalenv in *.
  simpl in *. destruct v;simpl;try constructor.

  unfold ge,tge. simpl.
  
  unfold gen_code_map.
  repeat rewrite PTree.fold_spec.  
  exploit (@PTree.elements_canonical_order' _ _ section_eq (PTree.map (rev_section instr_size x) (transl_sectable' (prog_sectable prog))) (prog_sectable prog)).
  eapply transl_sections_consistency. auto.
  intros.

  unfold section in *.
  set (l1:= (PTree.elements (PTree.map (rev_section instr_size x) (transl_sectable' (prog_sectable prog))))) in *.
  set (l2:= (PTree.elements (prog_sectable prog))) in *.
  clear - H instr_size instr_eq_size.
  assert (LEN: exists n, length l1 = n).
  { clear.
    induction l1. exists O. auto.
    destruct IHl1.
    eexists. simpl. auto. }
  destruct LEN. generalize x0 l1 H0 l2 H.
  clear- instr_size instr_eq_size.
  induction x0;intros.
  rewrite length_zero_iff_nil in H0. subst.
  inv H. constructor.
  apply LocalLib.length_S_inv in H0.
  destruct H0 as (l' & a & A1 & A2). subst.
  eapply list_forall2_app_inv_l in H.
  destruct H as (l4 & l5 & P1 & P2 & P3).
  inv P3. inv H3. destruct H1.
  exploit IHx0;eauto. intros.
  repeat rewrite fold_left_app.
  simpl. inv H1.
  - unfold acc_code_map at 1. unfold acc_code_map at 4.
    destr.
    + simpl in H0. destr_in H0. rewrite H.
      unfold Memory.NMap.set. destr.
      * eapply gen_instr_map_pres_eq;eauto.
      * rewrite <- H3. rewrite <- H4. constructor.
    + simpl in H0. destr_in H0.
      rewrite <- H3. rewrite <- H4. constructor.
    + simpl in H0. destr_in H0.
      rewrite <- H3. rewrite <- H4. constructor.
  - unfold acc_code_map at 1. unfold acc_code_map at 4.
    destr.
    + simpl in H0. destr_in H0. rewrite H.
      unfold Memory.NMap.set. destr.
      * eapply gen_instr_map_pres_eq;eauto.
      * rewrite <- H3. rewrite <- H2. constructor. auto.
    + simpl in H0. destr_in H0.
      rewrite <- H3. rewrite <- H2. constructor. auto.
    + simpl in H0. destr_in H0.
      rewrite <- H3. rewrite <- H2. constructor. auto.      
Qed.



Lemma transf_initial_state:forall st1 rs1,
    RelocProgSemantics.initial_state instr_size prog rs1 st1 ->
    initial_state instr_size tprog rs1 st1.
Proof.
  intros st1 rs1 INIT. inv INIT. 
  unfold match_prog in TRANSF. unfold transf_program in TRANSF.
  monadInv TRANSF.
  
  econstructor;eauto. unfold decode_program. simpl.
  apply RelocProgSemantics.initial_state_intro with (m:=m).
  unfold init_mem in *. simpl in *.
  unfold RelocProgSemantics.globalenv in *. simpl.

  destr_in H. exploit (alloc_sections_eq).
  assert (RelocProgGlobalenvs.Genv.genv_symb ge =  RelocProgGlobalenvs.Genv.genv_symb tge).
  unfold ge,tge. simpl. auto.
  eapply H1.
  eapply transl_sections_consistency. eauto.
  eauto.
  intros A. unfold tge in A. unfold globalenv in A.
  unfold decode_program in A. simpl in A.
  unfold RelocProgSemantics.globalenv  in A. simpl in A.
  rewrite A.

  auto.

  inv H0. econstructor;eauto.
Qed.



Lemma symbol_address_pres: forall id ofs,
    RelocProgGlobalenvs.Genv.symbol_address ge id ofs =
    RelocProgGlobalenvs.Genv.symbol_address tge id ofs.
Proof.
  unfold match_prog in TRANSF. unfold transf_program in TRANSF.
  monadInv TRANSF. simpl;auto.
Qed.


Lemma step_simulation: forall s1 s1' t,
    step instr_size ge s1 t s1' ->
    step instr_size tge s1 t s1'.
Proof.
  intros.
  inv H.
  - 

    exploit genv_instr_eq. rewrite H2.
    intros. inv H.    
    eapply exec_step_internal with (i:=x);eauto.

    unfold RelocProgGlobalenvs.Genv.find_ext_funct in *.
    destr_in H1. 
    
    unfold match_prog in TRANSF. unfold transf_program in TRANSF.
    monadInv TRANSF. simpl;auto.

    unfold instr_eq in H6. clear H4 H1 H2 H0.
    erewrite exec_instr_refl in H3.
    2: eapply symbol_address_pres.
    destruct x;subst;auto.
    destruct i;inv H6.
    simpl in *. auto.
    
  - eapply exec_step_builtin;eauto.
    unfold RelocProgGlobalenvs.Genv.find_ext_funct in *.
    destr_in H1.
    unfold match_prog in TRANSF. unfold transf_program in TRANSF.
    monadInv TRANSF. simpl;auto.
     exploit genv_instr_eq. rewrite H2.
     intros. inv H. unfold instr_eq in H7.
     (* architecture dependent *)
     destr_in H7. subst.
     simpl. inv H7. rewrite <- H5. auto.
     eapply eval_builtin_args_preserved with (ge1:= ge).
     unfold RelocProgGlobalenvs.Genv.find_symbol. simpl.     
     
     simpl in *. unfold match_prog in TRANSF. unfold transf_program in TRANSF.
     monadInv TRANSF. simpl;eauto.
     eauto.
     
     simpl in *. unfold match_prog in TRANSF. unfold transf_program in TRANSF.
     monadInv TRANSF. simpl;eauto.

  - eapply exec_step_external;eauto.
    simpl in *. destr_in H1.
    unfold match_prog in TRANSF. unfold transf_program in TRANSF.
    monadInv TRANSF. simpl;auto.
    simpl in *. unfold match_prog in TRANSF. unfold transf_program in TRANSF.
    monadInv TRANSF. simpl;eauto.
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
  - intros. exists s1'.
    split;auto.
    rewrite <- H0. auto.
    unfold semantics. simpl in *.
    eapply step_simulation. eauto.                
Qed.

End PRESERVATION.

Instance reloctablesgen_transflink (instr_size: instruction -> Z): TransfLink (match_prog instr_size).
Admitted.
