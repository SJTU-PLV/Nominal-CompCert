Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgramBytes.
Require Import Stacklayout Conventions.
Require Import Linking RelocProgLinking Errors.   
Require Import EncDecRet RelocBingen RelocBinDecode.
Require Import RelocProgSemantics RelocProgSemantics1.
Require Import TranslateInstr RelocProgSemantics2.
Require Import RelocProgSemantics RelocProgSemantics1 RelocProgSemanticsArchi1.
Require Import RelocProgSemanticsArchi RelocProgGlobalenvs.

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

(* prove encoder does not generates empty list *)

Lemma encode_Instruction_not_empty:forall i,
    encode_Instruction i = OK [] -> False.
Proof.
  destruct i;simpl;intros H;try monadInv H;try congruence.
Qed.

Lemma translate_instr_not_empty:forall i,
    translate_instr i = OK [] -> False.
Proof.
    Ltac solve_app_nil:=
    match goal with
    | H: ?a ++ [?b] = [] |- _ =>
      apply app_eq_nil in H;destruct H;congruence
    end.

    Ltac auto_monadInv:=
    match goal with
    | H: bind ?a ?f = ?c |- _ =>
      monadInv H;try auto_monadInv
    | _ => fail
    end.
  destruct i;simpl;intros H;try destr_in H;try monadInv H;try congruence;
    try auto_monadInv;try solve_app_nil.

    
  (* Pcall *)
  destr_in H. destr_in H.
Qed.

Section WITH_INSTR_SIZE.
  Variable instr_size: instruction -> Z.

(* ad-hoc *)
Section PRESERVATION. 
(** Transformation *)
  Variable prog: RelocProgram.program.
  Variable tprog: program.
  
  
  Let ge := RelocProgSemantics1.globalenv instr_size prog.
  Let tge := RelocProgSemantics2.globalenv instr_size tprog.
  
  Hypothesis symbol_address_pres: forall id ofs,
    RelocProgGlobalenvs.Genv.symbol_address ge id ofs =
    RelocProgGlobalenvs.Genv.symbol_address tge id ofs.
  Hypothesis find_instr_refl: forall b ofs i,
    Genv.genv_instrs ge b ofs = Some i ->
    Genv.genv_instrs tge b ofs = Some i.
  Hypothesis find_ext_funct_refl: forall v,
    Genv.find_ext_funct ge v = Genv.find_ext_funct tge v.

  Hypothesis rev_transl_code_in: forall i c r,
    In i (rev_transl_code instr_size r c) ->
    exists i', In i' c /\ ((exists id addend, rev_id_eliminate id addend i' = i) \/ i = i').
  Hypothesis transl_instr_in_code: forall c i id,
    prog.(prog_sectable) ! id = Some (sec_text c) ->
    In i c ->
    exists i', translate_instr i = OK i'.
  Hypothesis senv_refl:
    (Genv.genv_senv ge) = (Genv.genv_senv tge).



Lemma eval_addrmode_refl: forall a rs,
    eval_addrmode ge a rs = eval_addrmode tge a rs.
Proof.
  intros.
  erewrite eval_addrmode_match_ge. eauto.
  apply symbol_address_pres.
Qed. 

  
Lemma step_simulation: forall st1 st2 t,
    step instr_size ge st1 t st2 ->
    step instr_size tge st1 t st2.
Proof.
  intros st1 st2 t STEP.
  inv STEP.
  - unfold Genv.find_instr in H1.
    exploit find_instr_refl;eauto.
    intros.
    eapply exec_step_internal;eauto.
    erewrite <- find_ext_funct_refl;eauto.
    erewrite <- exec_instr_refl;eauto.

  (* Pbuiltin instr impossible *)
  - unfold Genv.find_instr in H1.
    simpl in H1. apply gen_code_map_inv in H1.
    destruct H1 as (id & c & P1 & P2 & P3).
    generalize (PTree_map_elements _ (RelocProg.section instruction init_data) (rev_section instr_size (prog_reloctables prog)) (prog_sectable prog)). simpl.
    intros F.
    apply PTree.elements_correct in P2.
    exploit list_forall2_in_right;eauto.
    simpl.
    intros (x1 & In1 & ? &REV1).
    subst. destruct x1. apply PTree.elements_complete in In1.
    simpl in REV1.
    destruct s.  2-3:  simpl in REV1; congruence.
    simpl in REV1. destr_in REV1.
    + inv REV1. apply rev_transl_code_in in P3.
      destruct P3 as (i' & In' & P3').
      assert (i' = Pbuiltin ef args res).
      { destruct P3'.
        destruct H1 as (id & P3').
        destruct i';simpl in P3';repeat destr_in P3';try congruence.
        subst. auto. }
      subst.
      
      eapply transl_instr_in_code in In1;eauto.
      simpl in In1. destruct In1 as (? & ?).
      inv H1.
      
    + inv REV1.
      eapply transl_instr_in_code in In1;eauto.
      destruct In1 as (? & ?).
      inv H1.
      
  - 
    rewrite find_ext_funct_refl in H0.
    eapply exec_step_external;eauto.
    rewrite <- senv_refl. auto.    
Qed.

End PRESERVATION.

End WITH_INSTR_SIZE.
