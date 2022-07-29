(* *******************  *)
(* Author: Jinhua Wu    *)
(* Date:   Jul 26th     *)
(* *******************  *)

Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgram Globalenvs.
Require Import Stacklayout Conventions.
Require Import Linking Errors.
Require Import EncDecRet RelocBingen RelocBinDecode.
Require Import RelocProgSemantics RelocProgSemantics1.
Require Import TranslateInstr RelocProgSemantics2.

Import ListNotations.
Local Open Scope error_monad_scope.

Lemma PTree_map_elements: forall A B (f:positive -> A -> B) m,
    let R := (fun p a b => f p a = b) in
    list_forall2
      (fun (i_x : positive * A) (i_y : positive * B) =>
         fst i_x = fst i_y /\ R (fst i_x) (snd i_x) (snd i_y))
      (PTree.elements m) (PTree.elements (PTree.map f m)).
Proof.
  intros.
  apply PTree.elements_canonical_order1;intros.
  - unfold R in *.
    rewrite PTree.gmap.
    rewrite H. simpl. exists (f i x). auto.
  - unfold R in *.
    rewrite PTree.gmap in H.
    unfold option_map in *. destr_in H.
    exists a. inv H. auto.
Qed.

Lemma list_forall2_Forall2: forall A B (P: A -> B -> Prop) l1 l2,
    list_forall2 P l1 l2 <->
    Forall2 P l1 l2.
Proof.
  induction l1;intros.
  split;intros. inv H. auto.
  inv H. constructor.
  split;intros.
  inv H. constructor. auto. apply IHl1. auto.
  inv H. constructor. auto. apply IHl1. auto.
Qed.

Lemma list_forall2_app_inv_l: forall A B (P: A -> B -> Prop) l1 l2 l3,
    list_forall2 P (l1++l2) l3 ->
    exists l4 l5, l3 = l4 ++ l5 /\ list_forall2 P l1 l4 /\ list_forall2 P l2 l5.
  intros.
  apply list_forall2_Forall2 in H.
  exploit Forall2_app_inv_l;eauto. intros (l1' & l2' & ? & ? & ?).
  eexists. eexists. split;eauto.
  split;apply list_forall2_Forall2;auto.
Qed.

  
Section WITH_INSTR_SIZE.

Variable instr_size : instruction -> Z.
Variable Instr_size : list Instruction -> Z.

Hypothesis translate_instr_size: forall i e l l',
      translate_instr e i = OK l ->
      Instr_size (l ++ l') = instr_size i.

Definition match_prog (p: program) (tp: program) :=
  transf_program instr_size p = OK tp.

Lemma decode_prog_code_section_total: forall p tp,
    transf_program instr_size p = OK tp ->
    exists tp', decode_prog_code_section instr_size Instr_size tp = OK tp'.
Proof.
Admitted.

(* should be Hypothesis *)
Lemma translate_code_size: forall c1 c2 c3 r,
          transl_code instr_size r c1 = OK c2 ->
          decode_instrs' instr_size Instr_size r c2 = OK c3 ->
          code_size instr_size c1 = code_size instr_size c3.
Admitted.

Lemma rev_transl_code_size:forall r c,
    code_size instr_size c = code_size instr_size (RelocProgSemantics1.rev_transl_code instr_size r c).
Admitted.


Lemma transl_init_data_list_size: forall data l r,
    transl_init_data_list r data = OK l ->
    init_data_list_size data = Z.of_nat (length l).
Admitted.


Lemma transl_init_data_pres_mem: forall data r l b m1 m2 ge1 ge2
                                   (MATCHGE: forall i ofs, RelocProgSemantics.Genv.symbol_address ge1 i ofs = RelocProgSemantics.Genv.symbol_address ge2 i ofs),          
    transl_init_data_list r data = OK l ->
    RelocProgSemantics.store_init_data_list ge1 m1 b 0 data = Some m2 ->
    store_init_data_bytes ge2 r m1 b 0 l = Some m2.
Admitted.



Lemma alloc_section_pres_mem: forall ge1 ge2 id sec sec1 sec2 m m0 reloctbl symbtbl
    (MATCHGE: forall i ofs, RelocProgSemantics.Genv.symbol_address ge1 i ofs = RelocProgSemantics.Genv.symbol_address ge2 i ofs),
    acc_fold_section instr_size symbtbl reloctbl id sec = OK sec1 ->
    acc_decode_code_section instr_size Instr_size symbtbl reloctbl id sec1 = OK sec2 ->
    RelocProgSemantics.alloc_section instr_size ge1 symbtbl (Some m) id (RelocProgSemantics1.rev_section instr_size reloctbl id sec) = Some m0 ->
    alloc_section instr_size ge2 symbtbl reloctbl (Some m) id sec2 = Some m0.
Proof.
  intros.
  destruct sec.

  (* code section *)
  - unfold acc_fold_section in H.
    destr_in H. monadInv H.
    simpl in EQ. destr_in EQ.
    monadInv EQ.
    unfold acc_decode_code_section in H0.
    rewrite Heqo in H0. rewrite Heqs0 in H0.
    monadInv H0.
    unfold alloc_section.
    unfold RelocProgSemantics.alloc_section in H1.
    unfold  RelocProgSemantics.get_symbol_type in *.
    rewrite Heqo in *. rewrite Heqs0 in *.
    destr_in H1. simpl in H1.
    exploit translate_code_size;eauto.
    intros. simpl in Heqs1.
    destr_in Heqs1.
    + inv Heqs1.
      rewrite <- rev_transl_code_size in H1.
      rewrite H in *. auto.
    + inv Heqs1.
      rewrite H in *. auto.

  (* data section *)
  - unfold acc_fold_section in H.
    destr_in H. monadInv H.
    simpl in EQ. destr_in EQ.
    (* rwdata *)
    + monadInv EQ.
      unfold acc_decode_code_section in H0.
      rewrite Heqo in H0. rewrite Heqs0 in H0.
      monadInv H0.
      unfold alloc_section.
      unfold RelocProgSemantics.alloc_section in H1.
      unfold  RelocProgSemantics.get_symbol_type in *.
      rewrite Heqo in *. rewrite Heqs0 in *.
      destr_in H1. simpl in Heqs1.
      inv Heqs1. simpl in H1.
      exploit transl_init_data_list_size;eauto.
      intros. rewrite H in H1.
      destruct (Mem.alloc_glob id m 0 (Z.of_nat (Datatypes.length x))).
      destr_in H1.
      destr_in H1. exploit transl_init_data_pres_mem;eauto.
      intros. rewrite H0. auto.
    (* rodata *)
    + monadInv EQ.
      unfold acc_decode_code_section in H0.
      rewrite Heqo in H0. rewrite Heqs0 in H0.
      monadInv H0.
      unfold alloc_section.
      unfold RelocProgSemantics.alloc_section in H1.
      unfold  RelocProgSemantics.get_symbol_type in *.
      rewrite Heqo in *. rewrite Heqs0 in *.
      destr_in H1. simpl in Heqs1.
      inv Heqs1. simpl in H1.
      exploit transl_init_data_list_size;eauto.
      intros. rewrite H in H1.
      destruct (Mem.alloc_glob id m 0 (Z.of_nat (Datatypes.length x))).
      destr_in H1.
      destr_in H1. exploit transl_init_data_pres_mem;eauto.
      intros. rewrite H0. auto.
  - unfold acc_fold_section in H.
    simpl in H. destr_in H.
Qed.
               
Section PRESERVATION. 
(** Transformation *)
Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: match_prog prog tprog.

Let ge := RelocProgSemantics1.globalenv instr_size prog.
Let tge := globalenv instr_size Instr_size tprog.



Definition match_instr (i1 i2: instruction):=
  forall e l l', translate_instr e i1 = OK l ->
         decode_instr e (l ++ l') = OK (i2,l').


(* instruction map is mostly identical *)
Lemma find_instr_refl: forall b ofs i,
    Genv.genv_instrs ge b ofs = Some i ->
    exists i1, Genv.genv_instrs tge b ofs = Some i1
          /\ match_instr i i1.
Proof.
  unfold ge,tge. unfold globalenv.
  unfold match_prog in TRANSF.
  exploit decode_prog_code_section_total;eauto.
  intros (tp' & A). rewrite A.
  simpl.
  unfold transf_program in *. monadInv TRANSF.
  unfold transl_sectable in EQ.
  unfold decode_prog_code_section in *.
  monadInv A. simpl in *.
  clear ge tge.
Admitted.

Lemma find_ext_funct_refl: forall v,
    Genv.find_ext_funct ge v = Genv.find_ext_funct tge v.
Admitted.
  

Lemma symbol_address_pres: forall id ofs,
    RelocProgSemantics.Genv.symbol_address ge id ofs =
    RelocProgSemantics.Genv.symbol_address tge id ofs.
Proof.
  intros.
  unfold ge, tge. unfold globalenv.
  exploit decode_prog_code_section_total;eauto.
  intros (tp' & A).
  rewrite A.
  unfold RelocProgSemantics.Genv.symbol_address.
  unfold RelocProgSemantics.Genv.find_symbol.
  unfold RelocProgSemantics.globalenv. simpl.
  unfold match_prog in TRANSF.
  unfold transf_program in TRANSF. monadInv TRANSF.
  unfold decode_prog_code_section in A. simpl in *.
  monadInv A. simpl.
  auto.
Qed.

Lemma transf_initial_state:forall st1 rs,
    RelocProgSemantics1.initial_state instr_size prog rs st1 ->
    exists st2, initial_state instr_size Instr_size tprog rs st2 /\ st1 = st2.
  intros st1 rs H.
  inv H. inv H1.
  unfold match_prog in TRANSF.
  exploit decode_prog_code_section_total;eauto.
  intros (tp' & A).
  (* to prove init_mem equal *)
  assert (TOPROVE: init_mem instr_size tp' = Some m).
  { unfold RelocProgSemantics.init_mem in H.
    unfold init_mem.
    simpl in H. destr_in H.

    (* alloc sections preserve memory *)
  assert (ALLOCSECS: alloc_sections instr_size (RelocProgSemantics.globalenv instr_size tp')
                         (prog_symbtable tp') (prog_reloctables tp') 
                         (prog_sectable tp') Mem.empty = Some m0).
  { 
    set (ge1:= (RelocProgSemantics.globalenv instr_size (RelocProgSemantics1.decode_program instr_size prog))) in *.
    set (ge2:= (RelocProgSemantics.globalenv instr_size tp')).
    (* globalenv property *)
    assert (GEProp: forall id ofs,RelocProgSemantics.Genv.symbol_address ge1 id ofs = RelocProgSemantics.Genv.symbol_address ge2 id ofs).
    { intros.
      exploit (symbol_address_pres).
      unfold ge,tge,ge1,ge2.
      unfold globalenv. rewrite A.
      unfold RelocProgSemantics1.globalenv. eauto. } (* end of GEProp *)
      
    unfold decode_prog_code_section in A.
    monadInv A. simpl.
    unfold transf_program in TRANSF. monadInv TRANSF.
    unfold transl_sectable in  EQ0. simpl in *.
    exploit PTree_fold_elements. apply EQ. intros F1. clear EQ.
    exploit PTree_fold_elements. apply EQ0. intros F2. clear EQ0.
    unfold RelocProgSemantics.alloc_sections in Heqo.
    unfold alloc_sections. rewrite PTree.fold_spec.
    rewrite PTree.fold_spec in Heqo.
    unfold RelocProg.sectable in *.
    generalize (PTree_map_elements _ section (RelocProgSemantics1.rev_section instr_size (prog_reloctables prog)) (prog_sectable prog)).
    simpl. intros F3.
    (* induction on (prog_reloctables prog) *)
    set (l:= @PTree.elements section (prog_sectable prog)) in *.
    set (l1:= @PTree.elements section x0) in *.
    set (l2 := @PTree.elements section x) in *.
    unfold section in F3,Heqo.
    set (l3:= (@PTree.elements (@RelocProg.section instruction)
            (@PTree.map (@RelocProg.section instruction) (@RelocProg.section instruction)
               (RelocProgSemantics1.rev_section instr_size
                                                (prog_reloctables prog)) (prog_sectable prog)))) in *.
    
    clear ge tge H H0.
    revert F1 F2 F3 Heqo.
    generalize m0.
    generalize l l1 l2 l3. clear l l1 l2 l3.
    intros l.
    assert (LEN: exists n, length l = n).
    { induction l. exists O. auto.
      destruct IHl.
      exists (S x1). simpl. auto. }
    destruct LEN. revert H.
    generalize x1,l. clear x1 l.
    clear m m0.
    
    (* core proof *)
    
    induction x1;intros.
    - rewrite length_zero_iff_nil in H. subst.
      inv F3. inv F2. inv F1.
      simpl in Heqo. inv Heqo.
      simpl. auto.
    - exploit LocalLib.length_S_inv;eauto.
      intros (l' & a1 & A1 & B1). subst.
      clear H.
      exploit list_forall2_app_inv_l. apply F2.
      intros (? & ? & ? & ? & ?). subst.
      inv H1. inv H5.
      exploit list_forall2_app_inv_l. apply F3.
      intros (? & ? & ? & ? & ?). subst.
      inv H2. inv H7.
      exploit list_forall2_app_inv_l. apply F1.
      intros (? & ? & ? & ? & ?). subst.
      inv H4. inv H9.
      clear F1 F2 F3.
      rewrite fold_left_app in Heqo. simpl in Heqo.
      destruct (fold_left
    (fun (a : option mem) (p : positive * RelocProg.section) =>
     RelocProgSemantics.alloc_section instr_size ge1
       (prog_symbtable prog) a (fst p) (snd p)) x2 
    (Some Mem.empty)) eqn: FOLD.
      2:{ simpl in Heqo. inv Heqo. }
      exploit IHx1. eapply eq_refl.
      eapply H2. auto. eauto.
      eauto.
      clear IHx1 H2 H1 H0.
      intros FOLD1. rewrite fold_left_app.
      rewrite FOLD1. cbn [fold_left] in *.
      clear FOLD1 FOLD.
      destruct H3. destruct H5. destruct H7.
      rewrite <- H3 in *. rewrite <- H in *.
      unfold section in *.
      rewrite H1 in *. clear H H1 H3.
      rewrite <- H2 in *. clear H2.
      exploit alloc_section_pres_mem;eauto. } (* end of assert ALLOCSECS *)

  rewrite ALLOCSECS.
  unfold decode_prog_code_section in A.
  monadInv A. simpl.
  unfold transf_program in TRANSF. monadInv TRANSF.
  simpl in *. auto. }           (* end of assert TOPROVE *)
  
  inv H0.
  
  set (ge2:= (RelocProgSemantics.globalenv instr_size tp')).
  set (rs0' := rs # PC <- (RelocProgSemantics.Genv.symbol_address ge2 tp'.(prog_main) Ptrofs.zero)
           # RA <- Vnullptr
           # RSP <- (Vptr stk (Ptrofs.sub (Ptrofs.repr (max_stacksize + align (size_chunk Mptr) 8)) (Ptrofs.repr (size_chunk Mptr))))) in *.
  
  exists (State rs0' m2).
  constructor;eauto. econstructor;eauto.
  econstructor;eauto.
  f_equal.
  
  
  (* globalenv property *)
  assert (GEProp: forall id ofs,RelocProgSemantics.Genv.symbol_address ge0 id ofs = RelocProgSemantics.Genv.symbol_address ge2 id ofs).
  { intros.
    exploit (symbol_address_pres).
    unfold ge,tge,ge0,ge2.
    unfold globalenv. rewrite A.
    unfold RelocProgSemantics1.globalenv. eauto. } (* end of GEProp *)
  intros.
  unfold rs0,rs0'.
  erewrite GEProp.
  unfold decode_prog_code_section in A.
  monadInv A. cbn [prog_main].
  unfold transf_program in TRANSF. monadInv TRANSF.
  cbn [prog_main]. auto.
Qed.

Lemma step_simulation: forall st1 st2 t,
    step instr_size ge st1 t st2 ->
    exists st2', step instr_size tge st1 t st2'.
Proof.
  intros st1 st2 t STEP.
  exists st2.
  inv STEP.
  - unfold Genv.find_instr in H1.
    exploit find_instr_refl;eauto.
    intros (i1 & FIND & MATCHINSTR).
    eapply exec_step_internal;eauto.
    erewrite <- find_ext_funct_refl;eauto.
    unfold match_instr in MATCHINSTR.
    
    
  - unfold Genv.find_instr in H1.
  (* builtin instr impossible *)
    admit.
  - 
