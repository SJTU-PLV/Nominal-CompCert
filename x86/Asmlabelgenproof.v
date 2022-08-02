(* *******************  *)
(* Author: Xiangzhe Xu  *)
(* Date:   Sep 16, 2019 *)
(* *******************  *)




Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm RealAsm.
Require Import Asmlabelgen.
Import ListNotations.
Require AsmFacts.

Section WITH_INSTR_SIZE.

Variable instr_size: instruction -> Z.

  
Definition match_prog (p tp:Asm.program) :=
  match_program (fun _ f tf => transf_fundef instr_size f = OK tf) eq p tp.


Lemma transf_program_match:
  forall p tp, transf_program instr_size p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.


Section PRESERVATION.

Variable prog: Asm.program.
Variable tprog: Asm.program.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Hypothesis TRANSF: match_prog prog tprog.

Inductive match_states : Asm.state -> Asm.state -> Prop :=
|match_states_intro m rs:
   match_states (Asm.State rs m) (Asm.State rs m).

(* Variable init_stk: stack. *)

(* Lemma globalenv_eq: ge = tge. *)
(* Proof. *)
(*   unfold ge, tge. *)
(*   unfold Genv.globalenv. *)
(*   destruct TRANSF as (A & B & C). *)
(*   setoid_rewrite C. *)
(*   fold fundef. *)
(*   generalize (Genv.empty_genv fundef unit (prog_public prog)). *)
(*   revert A. *)
(*   fold fundef. *)
(*   generalize (prog_defs prog) (prog_defs tprog). *)
(*   induction 1; simpl; intros; eauto. *)
(*   inv H. destruct a1, b1; simpl in *. subst. inv H1. *)
(*   apply IHA. *)
(*   inv H. unfold transf_fundef, transf_partial_fundef in H1. *)
(*   repeat destr_in H1. unfold bind in H2. destr_in H2. inv H2. *)
(*   unfold trans_function in Heqr. repeat destr_in Heqr. *)
(*   monadInv H1. cbn *)
(*   inv H1. apply IHA. *)
(* Qed. *)


Fixpoint transl_code_spec ofs allcode code code' : Prop :=
  match code, code' with
  | nil, nil => True
  | h::t, h'::t' =>
    transl_instr instr_size h ofs allcode = OK h' /\
    transl_code_spec (ofs + instr_size h) allcode t t'
  | _, _ => False
  end.

Definition transl_code_spec_base allcode code' :=
  transl_code_spec 0 allcode allcode code'.

Lemma find_instr_inv : forall ofs code i,
    find_instr instr_size ofs code = Some i ->
    exists l1 l2, code = l1 ++ (i :: l2) /\ code_size instr_size l1 = ofs.
Admitted.

Lemma app_cons_comm: forall (A:Type) (l1:list A) a l2,
    (l1 ++ [a]) ++ l2 = l1 ++ a :: l2.
Proof.
  induction l1; intros. 
  - simpl. auto.
  - simpl. f_equal. apply IHl1.
Qed.

Lemma transl_code_spec_app : forall ofs allcode code1 rcode1 i i',
    transl_code_spec ofs allcode code1 (rev rcode1) ->
    transl_instr instr_size i (ofs + code_size instr_size code1) allcode = OK i' ->
    transl_code_spec ofs allcode (code1 ++ [i]) (rev rcode1 ++ [i']).
Admitted.

Lemma code_size_app : forall c1 c2,
    code_size instr_size (c1 ++ c2) = code_size instr_size c1 + code_size instr_size c2.
Admitted.

Lemma transl_code_err: forall allcode code e r,
    fold_left (acc_transl_instr instr_size allcode) code (Error e) <> OK r.
Admitted.

Lemma transl_code_spec_pf : forall allcode ofs0 code2 ofs1 code1 rcode1 rcode2,
    transl_code_spec ofs0 allcode code1 (rev rcode1) ->
    fold_left (acc_transl_instr instr_size allcode) code2 (OK (ofs0 + code_size instr_size code1, rcode1)) = OK (ofs1, rcode2) ->
    transl_code_spec ofs0 allcode (code1 ++ code2) (rev rcode2).
Proof.
  induction code2 as [ | i code2'].
  - intros ofs1 code1 rcode1 rcode2 TLSPEC FL.
    rewrite app_nil_r. simpl in FL. inv FL. auto.
  - intros ofs1 code1 rcode1 rcode2 TLSPEC FL.
    simpl in FL.
    unfold bind in FL.
    destruct (transl_instr instr_size i (ofs0 + code_size instr_size code1) allcode) eqn:TLEQ.
    rewrite <- app_cons_comm.
    eapply IHcode2'.
    instantiate (1:= (i0::rcode1)). simpl.
    apply transl_code_spec_app; auto.
    rewrite code_size_app. simpl.
    rewrite <- FL. f_equal. f_equal. f_equal. lia.
    apply transl_code_err in FL. contradiction.
Qed.
    

Lemma transl_code_prop_pf : forall allcode code ofs rcode',
    fold_left (acc_transl_instr instr_size allcode) code (OK (0, nil)) = OK (ofs, rcode') ->
    transl_code_spec 0 allcode code (rev rcode').
Proof.
  intros.
  replace code with ([] ++ code) by auto.
  eapply transl_code_spec_pf; eauto.
  red. simpl. auto.
Qed.


Lemma transl_code_spec_inv : forall l1 i l2 l ofs code,
    transl_code_spec ofs code (l1 ++ i :: l2) l ->
    exists l1' l2' i', l = (l1' ++ i' :: l2')
                  /\ transl_instr instr_size i (code_size instr_size l1 + ofs) code = OK i'
                  /\ find_instr instr_size (code_size instr_size l1) l = Some i'.
Proof.
  induction l1; simpl.
  - intros i l2 l ofs code SPEC.
    destruct l. contradiction.
    destruct SPEC as [TL TLSPEC].
    exists nil, l, i0. repeat split; auto.
  - intros i l2 l ofs code SPEC.
    destruct l. contradiction.
    destruct SPEC as [TL TLSPEC].
    apply IHl1 in TLSPEC.
    destruct TLSPEC as (l1' & l2' & i' & L & TI & FIND).
    subst.
    exists (i0 :: l1'), l2', i'. split.
    simpl. auto. split.
    rewrite <- TI. f_equal. lia.
    assert (instr_size i0 = instr_size a) as EQ. admit.
    rewrite <- EQ. simpl.
    destruct zeq.
    admit.
    rewrite <- FIND. f_equal. lia.
Admitted.




Lemma find_instr_in_tprog: forall code ofs code' i,
    transl_code instr_size code = OK code'
    -> find_instr instr_size ofs code = Some i
    -> exists i', transl_instr instr_size i ofs code = OK i'
            /\ find_instr instr_size ofs code' = Some i'.
Proof.
  intros code ofs code' i TL FIND.
  exploit find_instr_inv; eauto.
  destruct 1 as (l1 & l2 & CD & CSZ). subst.
  monadInv TL. destruct x. inv EQ0.
  apply transl_code_prop_pf in EQ. 
  apply transl_code_spec_inv in EQ.
  destruct EQ as (l1' & l2' & i' & RV & TLI & FIND').
  rewrite Z.add_0_r in TLI.
  eauto.
Qed.




Lemma transf_refl:
  forall f f' ofs i,
    trans_function instr_size f = OK f' ->
    find_instr instr_size ofs (fn_code f) = Some i ->
    exists i',
      find_instr instr_size ofs (fn_code f') = Some i' /\
      (((forall cond  cond1 cond2  r tbl lbl, i <> Pjmp_l lbl /\ i <> Pjcc cond lbl /\ i <> Pjcc2 cond1 cond2 lbl /\ i <> Pjmptbl r tbl ) /\ i = i')
       \/(exists l, i = Pjmp_l l /\ (exists relOfs, i' = Pjmp_l_rel relOfs))
       \/(exists condition l, i = Pjcc condition l /\ (exists relOfs cond', i' = Pjcc_rel cond' relOfs))
       \/(exists condition1 condition2 l, i = Pjcc2 condition1 condition2 l /\ (exists relOfs cond1' cond2', i' = Pjcc2_rel cond1' cond2' relOfs))
       \/(exists reg tl, i = Pjmptbl reg tl /\ (exists r' ofsLst, i' = Pjmptbl_rel r' ofsLst))). 
Proof.
  intros f f' ofs i Htrans HfindInstr.
  
  destruct i eqn:EQI;
  try  (exists i;
       split;
       unfold trans_function in Htrans;
       destruct (func_no_jmp_rel_dec f) eqn:EQF;
       [now( set (I := i) in EQI;
         monadInv Htrans;
         simpl;
         rewrite <- EQI in HfindInstr;
         generalize (find_instr_in_tprog (fn_code f) ofs x I EQ HfindInstr);
         intros HtInstr;
         destruct HtInstr as [i' [HElim HtFind]];
         rewrite HtFind;
         rewrite EQI in HElim;
         unfold transl_code in HElim;
         simpl in HElim;
         monadInv HElim;
         rewrite <- EQI;
         auto) | inversion Htrans | try (left; repeat split; try (intros HN;inversion HN); auto) | inversion Htrans]).
  +
    set (I := i) in EQI.
    unfold trans_function in Htrans.
    destruct (func_no_jmp_rel_dec f) eqn:EQF.
    monadInv  Htrans.
    rewrite <- EQI in HfindInstr.
    generalize (find_instr_in_tprog _ ofs _ I EQ HfindInstr).
    intros Hinstr.
    destruct Hinstr as (i' & HTransI' & HTfindInstr).
    rewrite EQI in HTransI'.
    simpl in HTransI'.
    destruct (label_pos instr_size l 0 (fn_code f)) eqn: EQFL.
    ++
    exists ( Pjmp_l_rel (z - (ofs + instr_size (Pjmp_l l)))).
    split.
    simpl. rewrite HTfindInstr. f_equal. inversion HTransI'. auto.
    right. left. eauto.
    ++ inversion HTransI'.
    ++ inversion Htrans.
       
  + set (I := i) in EQI.
    unfold trans_function in Htrans.
    destruct (func_no_jmp_rel_dec f) eqn:EQF.
    monadInv  Htrans.
    rewrite <- EQI in HfindInstr.
    generalize (find_instr_in_tprog _ ofs _ I EQ HfindInstr).
    intros Hinstr.
    destruct Hinstr as (i' & HTransI' & HTfindInstr).
    rewrite EQI in HTransI'.
    simpl in HTransI'.
    destruct (label_pos instr_size l 0 (fn_code f)) eqn: EQFL.
    ++ inversion HTransI'. exists i'. simpl. split. auto. right.
       right. left. exists c,l. split. auto. eauto.
    ++ inversion HTransI'.
    ++ inversion Htrans.
  + set (I := i) in EQI.
    unfold trans_function in Htrans.
    destruct (func_no_jmp_rel_dec f) eqn:EQF.
    monadInv  Htrans.
    rewrite <- EQI in HfindInstr.
    generalize (find_instr_in_tprog _ ofs _ I EQ HfindInstr).
    intros Hinstr.
    destruct Hinstr as (i' & HTransI' & HTfindInstr).
    rewrite EQI in HTransI'.
    simpl in HTransI'.
    destruct (label_pos instr_size l 0 (fn_code f)) eqn: EQFL.
    ++ inversion HTransI'. exists i'. simpl. split. auto. right.
       right. right. left. exists c1, c2, l. split. auto. eauto.
    ++ inversion HTransI'. ++ inversion Htrans.
  + set (I := i) in EQI.
    unfold trans_function in Htrans.
    destruct (func_no_jmp_rel_dec f) eqn:EQF.
    monadInv  Htrans.
    rewrite <- EQI in HfindInstr.
    generalize (find_instr_in_tprog _ ofs _ I EQ HfindInstr).
    intros Hinstr.
    destruct Hinstr as (i' & HTransI' & HTfindInstr).
    rewrite EQI in HTransI'.
    simpl in HTransI'.
    destruct (findAllLabel instr_size tbl (fn_code f)) eqn: EQFL.
    ++ inversion HTransI'. exists i'. simpl. split. auto. right. right.
       right. right. exists r, tbl. split. auto. eauto.
    ++ inversion HTransI'.
    ++ inversion Htrans.
Qed.

Lemma transf_symbol_refl: forall id,
    (Genv.symbol_address tge id Ptrofs.zero) = (Genv.symbol_address ge id Ptrofs.zero).
Proof.
  intros id.
  unfold Genv.symbol_address.
  red in TRANSF.
  unfold ge, tge.
  rewrite (Genv.find_symbol_transf_partial TRANSF id). auto.
Qed.


Lemma transf_addrmode_refl: forall a rs,
    eval_addrmode ge a rs = eval_addrmode tge a rs.
Admitted.

Lemma transf_addrmode32_refl: forall a rs,
    eval_addrmode32 ge a rs = eval_addrmode32 tge a rs.
Admitted.

Lemma transf_addrmode64_refl: forall a rs,
    eval_addrmode64 ge a rs = eval_addrmode64 tge a rs.
Admitted.

(* Lemma transf_ros_refl: forall ros rs, *)
(*     eval_ros tge ros rs = eval_ros ge ros rs. *)
(* Admitted. *)


Section WITHMATCH.
          
Context {A B V: Type} {LA: Linker A} {LV: Linker V}.
Context {transf: A -> res B} {p: AST.program A V} {tp: AST.program B V}.
Hypothesis progmatch: match_program (fun cu f tf => transf f = OK tf) eq p tp.
                
Theorem find_funct_ptr_transf_partial_inv:
  forall b ef,
  Genv.find_funct_ptr (Genv.globalenv tp) b = Some ef ->
  exists f,
  Genv.find_funct_ptr (Genv.globalenv p) b = Some f /\ transf f = OK ef.
Proof.
Admitted.

End WITHMATCH.



Lemma offsets_after_call_transf_refl: forall c x,
    transl_code instr_size c = OK x
    ->(offsets_after_call instr_size x 0) = (offsets_after_call instr_size c 0).
Proof.
  intros c x HTrans.
  induction c.
  + simpl. monadInv  HTrans. simpl in EQ. inversion EQ. rewrite <- H0 in EQ0. inversion EQ0.
    simpl. auto.
  + unfold offsets_after_call.
    unfold transl_code in HTrans.
    setoid_rewrite (fold_left_app _ [a] c) in HTrans.    
    unfold offsets_after_call.

Admitted.



Theorem step_simulation:
  forall S1 t S2, step instr_size ge S1 t S2 ->
                  forall S1' (MS: match_states S1 S1'),
                    (exists S2', step instr_size tge S1' t S2' /\ match_states S2 S2').
Proof.
  intros S1 t S2 HStep S1' MS.
  inversion MS.
  exists S2.
  split.
  + induction HStep.
  ++ (* *)
    generalize(Mem.extends_refl m).
    intros MEXT.
    generalize (Genv.find_funct_ptr_transf_partial TRANSF _ H2).
    destruct 1 as [tf [FPTR TF]].
    unfold tge. eauto.
    monadInv TF.
    unfold trans_function in EQ. destruct (func_no_jmp_rel_dec f);inversion EQ.
    monadInv H5.
    generalize (find_instr_in_tprog _ _ _ _ EQ0 H3).
    intros (i' & HInstrTransf & Hfind).
    econstructor; subst; eauto.
    inversion H.
    auto.
    assert(In i (fn_code f)) as Hin. {
      admit.
    }
      
    (* destruct i eqn:EQI. *)
    (* +++ *)
    (*   simpl in HInstrTransf. inversion HInstrTransf. simpl. simpl in H4. *)
    (*   rewrite <- H4. inversion MS. auto. *)

    destruct i eqn:EQI;
      try (
          simpl in HInstrTransf; inversion HInstrTransf; simpl; simpl in H4;
          try (rewrite <- H4; inversion MS; auto);
          (* symbol *)
          try ( generalize (transf_symbol_refl id);
                intros Hid;
                rewrite <- Hid; auto);
          try (
              (* load/store *)
              try unfold exec_load;
              try unfold exec_store;
              generalize(transf_addrmode_refl a rs);
              intros HAddrmode; rewrite HAddrmode; 
              auto);
          try (
              (* lea *)
              try generalize(transf_addrmode32_refl a rs);
              intros HAddrmode32;
              try generalize(transf_addrmode64_refl a rs);
              intros HAddrmode64;
              unfold eval_addrmode in HAddrmode32;
              unfold eval_addrmode in HAddrmode64;
              try rewrite HAddrmode32;
              try rewrite HAddrmode64;
              auto);
          try (
              (* ros *)
              rewrite transf_ros_refl;
              destruct ( Genv.find_funct ge (eval_ros ge ros rs0)) eqn:EQF; inversion H4;
              rewrite <- H8;
              rewrite EQF;
              generalize (Genv.find_funct_transf_partial TRANSF _ EQF);
              intros(tf & HfunctionFind & HfunctionTransf);
              rewrite HfunctionFind;
              auto
            );
          try (
              (* rel *)
              unfold func_no_jmp_rel in f0;
              generalize (Forall_forall instr_not_jmp_rel (fn_code f));
              intros HForall;
              destruct HForall;
              rewrite <- EQI in Hin;
              generalize (H0 f0 i Hin);
              intros HNRel; rewrite EQI in HNRel;
              simpl in HNRel; inversion HNRel
            )
        ).
    (* destruct i eqn:EQI; *)
    (*   try ( destruct HInsProperty; *)
    (*         [ now(destruct H0 as (HNE & HI'); *)
    (*               rewrite <- HI'; *)
    (*               unfold exec_instr; *)
    (*               unfold exec_instr in H4; *)
    (*               inversion H4; *)
    (*               try( *)
    (*                   (* symbol *) *)
    (*                   generalize (transf_symbol_refl id); *)
    (*                   intros Hid; *)
    (*                   rewrite <- Hid); *)
    (*               inversion H; try rewrite H6; *)
    (*               try ( *)
    (*                   (* load/store *) *)
    (*                   try unfold exec_load; *)
    (*                   try unfold exec_store; *)
    (*                   generalize(transf_addrmode_refl a rs0); *)
    (*                   intros HAddrmode; rewrite HAddrmode;  *)
    (*                   auto); *)
    (*               try ( *)
    (*                   (* lea *) *)
    (*                   try generalize(transf_addrmode32_refl a rs0); *)
    (*                   intros HAddrmode32; *)
    (*                   try generalize(transf_addrmode64_refl a rs0); *)
    (*                   intros HAddrmode64; *)
    (*                   unfold eval_addrmode in HAddrmode32; *)
    (*                   unfold eval_addrmode in HAddrmode64; *)
    (*                   try rewrite HAddrmode32; *)
    (*                   try rewrite HAddrmode64; *)
    (*                   auto) *)
    (*              ) *)
    (*         | *)
    (*         destruct H0; inversion H0; inversion H5; *)
    (*         inversion H6; inversion H7; inversion H8; inversion H9; inversion H10]). *)

   
      (* jmp_l *)
      destruct (label_pos instr_size l 0 (fn_code f)) eqn:EQLb; inversion H5.
      monadInv HInstrTransf.
      simpl.
      unfold goto_label.
      rewrite EQLb.
      rewrite H1.
      rewrite H2.
      unfold goto_ofs.
      rewrite H1.
      rewrite FPTR.
      f_equal.
      f_equal.
      f_equal.
      
      repeat rewrite Ptrofs.add_signed.      
      f_equal.
      repeat rewrite Ptrofs.signed_repr.
      
      assert (instr_size (Pjmp_l_rel (z - (Ptrofs.unsigned ofs + instr_size (Pjmp_l l)))) = instr_size (Pjmp_l l)) as Hsize. {
        admit.
      }
      rewrite Hsize.
      assert (Ptrofs.unsigned ofs = Ptrofs.signed ofs) as Hofs. {
        admit.
      }
      rewrite Hofs.      
      repeat rewrite Z.add_assoc.
      rewrite Zplus_minus.
      auto.
      (*** TBD *)
      admit.
      (*** TBD *)
      admit.
      (*** TBD *)
      admit.
      (*** TBD *)
      admit.
      (*** TBD *)
      admit.

  (*   +++ *)
  (*     (* Pjcc c l *) *)
  (*     rewrite <- H8. *)
  (*     destruct (eval_testcond  c rs0) eqn:EQC;inversion H4. *)
  (*     destruct b0. *)
  (*     ++++ *)
  (*       rewrite <- H9. *)
  (*       rewrite H4. *)
  (*       unfold goto_label in H12. *)
  (*       destruct (label_pos l 0 (fn_code f)) eqn:EQLb; inversion H12. *)
  (*       rewrite H1. *)
  (*       rewrite H2. *)
  (*       monadInv  H5. *)
  (*       simpl. *)
  (*       rewrite EQC. *)
  (*       simpl. *)
  (*       unfold goto_ofs. *)
  (*       rewrite H1. *)
  (*       rewrite FPTR. *)
  (*       simpl. *)
  (*       f_equal. *)
  (*       f_equal. *)
  (*       f_equal. *)
  (*       repeat rewrite Ptrofs.add_signed.       *)
  (*       f_equal. *)
  (*       repeat rewrite Ptrofs.signed_repr. *)
  (*       rewrite <- (Pjcc_rel_size_eq   (z - (Ptrofs.unsigned ofs + instr_size (Pjcc c l))) l). *)
  (*       assert (Ptrofs.signed ofs = Ptrofs.unsigned ofs) as Hofs by admit. *)
  (*       rewrite Hofs. *)
  (*       repeat rewrite Z.add_assoc. *)
  (*       rewrite Zplus_minus. *)
  (*       auto. *)
  (*       admit. admit. admit. admit. admit. *)
        
  (*     ++++ *)
  (*       rewrite <- H9. rewrite H4. *)
  (*       destruct (label_pos l 0 (fn_code f)) eqn:EQLb; inversion H5. *)
  (*       monadInv  H5. *)
  (*       simpl. *)
  (*       rewrite EQC. *)
  (*       inversion H12. *)
  (*       f_equal. *)
  (*   +++ *)
  (*     (* pjcc2 *) *)
  (*     rewrite <- H8. *)
  (*     rewrite <- H9. *)
  (*     rewrite H4. *)
  (*     destruct (label_pos l 0 (fn_code f)) eqn:EQLb; inversion H5. *)
  (*     simpl. *)
  (*     destruct (eval_testcond c1 rs0); inversion H4. *)
  (*     destruct b0 eqn:EQB. *)
  (*     ++++ *)
  (*       destruct (eval_testcond c2 rs0); inversion H4. *)
  (*       destruct b1 eqn:EQB1. *)
  (*       +++++ unfold goto_ofs. *)
  (*       rewrite H1. rewrite FPTR. *)
  (*       unfold goto_label. rewrite EQLb. rewrite H1. rewrite H2. *)
  (*       f_equal. f_equal. f_equal. *)
  (*       repeat rewrite Ptrofs.add_signed. *)
  (*       f_equal. *)
  (*       repeat rewrite Ptrofs.signed_repr. *)
  (*       rewrite <- (Pjcc2_rel_size_eq _ l _ _). *)
  (*       assert(Ptrofs.signed ofs = Ptrofs.unsigned ofs) as Hofs by admit. *)
  (*       rewrite Hofs. *)
  (*       repeat rewrite Z.add_assoc. *)
  (*       rewrite Zplus_minus. *)
  (*       auto. *)
  (*       admit. admit. admit. admit. admit. *)
  (*       +++++ *)
  (*         auto. *)
  (*     ++++ auto. *)
  (*   +++ *)
  (*     (* pjmptbl *) *)
  (*     rewrite <- H8. rewrite <- H9. rewrite H4. *)
  (*     monadInv H5. *)
  (*     simpl. *)
  (*     destruct (rs r);inversion H4. *)
  (*     rewrite (list_nth_z_map). *)
  (*     destruct (list_nth_z tbl (Int.unsigned i)) eqn:EQnth; inversion H4. *)
  (*     generalize(list_nth_z_range _ _ EQnth). *)
  (*     intros HIRange. *)
  (*     Lemma transf_lbl_list: forall tbl c x, *)
  (*         findAllLabel tbl c = OK x *)
  (*         -> list_length_z tbl = list_length_z x. *)
  (*     Admitted. *)

  (*     generalize (transf_lbl_list tbl (fn_code f) x EQ1). *)
  (*     intros EQLen. *)

  (*     Lemma list_get_n: forall {A:Type}  n (l:list A), *)
  (*         n < list_length_z l *)
  (*         ->exists a, list_nth_z l n = Some a. *)
  (*     Admitted. *)
  (*     assert (Int.unsigned i < list_length_z x) as HxLen. { *)
  (*       setoid_rewrite <- EQLen. *)
  (*       omega. *)
  (*     } *)

  (*     Lemma transf_lbl_prop: forall tbl c x i lbl z, *)
  (*         findAllLabel tbl c = OK x *)
  (*         -> list_nth_z tbl i = Some lbl *)
  (*         -> list_nth_z x i = Some z *)
  (*         -> (label_pos lbl 0 c) = Some z. *)
  (*     Admitted. *)
  (*     generalize (list_get_n (Int.unsigned i) x HxLen). *)
  (*     intros (a & HnthX). *)
  (*     rewrite HnthX. simpl. unfold goto_label. *)
  (*     generalize (transf_lbl_prop tbl (fn_code f) x (Int.unsigned i) l a EQ1 EQnth HnthX). *)
  (*     intros Hpos. *)
  (*     rewrite Hpos. unfold goto_label in H6. *)
  (*     rewrite Hpos in H6. *)
  (*     destruct ( (rs # RAX <- Vundef) # RDX <- Vundef PC) eqn:EQPC; inversion H6. *)
  (*     assert ( (rs # RAX <- Vundef) # RDX <- Vundef PC = rs PC) as HPC. { *)
  (*       unfold Pregmap.set. *)
  (*       destruct (PregEq.eq PC RDX). *)
  (*       inversion e. *)
  (*       destruct (PregEq.eq PC RAX). *)
  (*       inversion e. *)
  (*       auto. *)
  (*     } *)
  (*     rewrite HPC in EQPC. *)
  (*     rewrite EQPC in H1. *)
  (*     inversion H1. *)
  (*     rewrite H2. *)
  (*     unfold goto_ofs. *)
  (*     rewrite HPC. rewrite EQPC. rewrite H9. rewrite FPTR. *)
  (*     f_equal. f_equal. f_equal. *)
  (*     rewrite H11. *)
  (*     repeat rewrite Ptrofs.add_signed. *)
  (*     repeat rewrite Ptrofs.signed_repr. *)
  (*     f_equal. *)
  (*     assert(Ptrofs.signed ofs  = Ptrofs.unsigned ofs) as Hofs by admit. *)
  (*     rewrite Hofs. *)

  (*     rewrite <- (Pjmptbl_rel_size_eq r tbl  (Z.add (-(instr_size (Pjmptbl r tbl) + Ptrofs.unsigned ofs))) ## x). *)
  (*     repeat rewrite Z.add_assoc. *)
  (*     omega. *)
  (*     admit. admit. admit. admit. admit. *)
  (*   +++ admit. *)
  (*   (* +++ subst. rewrite H4. *) *)

  (*   (*   Lemma check_ra_after_call_eq : forall v a b, *) *)
  (*   (*     check_ra_after_call ge v = left a <-> check_ra_after_call tge v = left b. *) *)
  (*   (*   Admitted. *) *)

  (*   (*   destruct check_ra_after_call eqn:N; try congruence. *) *)
  (*   (*   rewrite check_ra_after_call_eq in N. unfold tge in N. *) *)
  (*   (*   rewrite N. *) *)
  (*   (*   destruct (Mem.check_top_tc m); inversion H4. *) *)
  (*   (*   auto. *) *)
                                                    
  (*   (*   (* Lemma transf_ra_refl: forall v, *) *) *)
  (*   (*   (*   ra_after_call ge v = ra_after_call tge v. *) *) *)
  (*   (*   (* Admitted. *) *) *)
      
  (*   (*   (* destruct (check_ra_after_call (Genv.globalenv tprog) (rs RA)) eqn:EQRA. *) *) *)
  (*   (*   (* destruct (check_ra_after_call ge (rs RA)) eqn:EQRA'. *) *) *)
  (*   (*   (* auto. *) *) *)
  (*   (*   (* generalize (transf_ra_refl (rs RA)). *) *) *)
  (*   (*   (* intros HRA. *) *) *)
  (*   (*   (* destruct (Mem.check_top_tc m); inversion H4. *) *) *)
          
  (* ++ *)
  (*   generalize(Genv.find_funct_ptr_transf_partial TRANSF _  H2). *)
  (*   intros (tf & FPTR & HTransf). *)
  (*   unfold tge.  monadInv HTransf. *)
  (*   subst. rewrite H. *)
  (*   eapply exec_step_builtin; eauto. *)
  (*   unfold trans_function in EQ. *)
  (*   destruct (func_no_jmp_rel_dec);inversion EQ. *)
  (*   monadInv EQ. *)
  (*   generalize (find_instr_in_tprog _ _ _ _ EQ0 H3). *)
  (*   intros (i' & HTrans & Hfind). simpl. *)
  (*   rewrite Hfind. inversion HTrans. *)
  (*   auto. *)
  (*   apply eval_builtin_args_preserved with (ge1 := ge); eauto. *)
  (*   intros id. *)
  (*   generalize (Genv.find_symbol_transf_partial TRANSF id). *)
  (*   intros Hsmybol. *)
  (*   auto. *)
  (*   apply external_call_symbols_preserved with (ge1:=ge); eauto. *)
  (*   eapply Genv.senv_transf_partial; eauto. *)
  (* ++ *)
  (*   generalize(Genv.find_funct_ptr_transf_partial TRANSF _  H2). *)
  (*   intros (tf & FPTR & HTransf). *)
  (*   unfold tge.  monadInv HTransf. *)
  (*   subst. rewrite H. *)
  (*   eapply exec_step_external; eauto. *)
  (*   apply external_call_symbols_preserved with (ge1:=ge); eauto. *)
  (*   eapply Genv.senv_transf_partial; eauto. *)
        
  (* + destruct S2. constructor. *)
Admitted.



Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
         exists st2, initial_state tprog  st2 /\ match_states st1 st2.
Proof.
Admitted.


Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros st1 st2 r MS HFinal.
  inversion HFinal.
  inversion MS. 
  econstructor.
  rewrite <- H1 in H3.
  inversion H3. auto.
  rewrite <- H1 in H3.
  inversion H3.
  auto.
Qed.


(* Lemma senv_equiv: *)
(*   Senv.equiv (Genv.genv_senv ge) (Genv.genv_senv tge). *)
(* Proof. *)
(*   unfold ge, tge, globalenv. rewrite ! add_globals_genv_senv. simpl. *)
(*   unfold match_prog in TRANSF. monadInv TRANSF. simpl. *)
(*   repeat apply conj; auto. *)
(* Qed. *)

Lemma transf_program_correct:
  forward_simulation (semantics instr_size prog) (semantics instr_size tprog).
Proof.
  eapply forward_simulation_step with match_states.
  + intros id. unfold match_prog in TRANSF.
    generalize (Genv.senv_match TRANSF). intros SENV_EQ.
    red in SENV_EQ.
    destruct SENV_EQ as (S1 & S2 & S3). auto.
  + simpl. intros s1 Hinit.
    exploit transf_initial_states; eauto.
  + simpl. intros s1 s2 r MS HFinal. eapply transf_final_states; eauto.
  + simpl. intros s1 t s1' STEP s2 MS.
    edestruct step_simulation as (STEP' & MS' ); eauto.
Qed.

Lemma trans_fun_pres_stacksize: forall f tf,
    Asmlabelgen.trans_function instr_size f = OK tf -> 
    Asm.fn_stacksize f = Asm.fn_stacksize tf.
Proof.
  intros f tf HFunc.
  unfold trans_function in HFunc.
  destruct func_no_jmp_rel_dec in HFunc; inversion HFunc.
  monadInv H0.
  simpl. auto.
Qed.


End  PRESERVATION.
End WITH_INSTR_SIZE.
