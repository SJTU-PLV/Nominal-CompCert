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


Lemma encode_Instruction_not_empty:forall i,
    encode_Instruction i = OK [] -> False.
  destruct i;simpl; try (autounfold with bitfields;simpl;congruence;fail).
  all: try (autounfold with bitfields;simpl;intros;repeat rewrite app_assoc in H;eapply app_cons_not_nil;inv H;eauto).
Qed.

Lemma translate_instr_not_empty : forall i,
    translate_instr i = OK [] -> False.
Proof.
  destruct i;unfold translate_instr;simpl;intros;monadInv H.
Qed.


Section WITH_INSTR_SIZE.
  Variable instr_size: instruction -> Z.


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


  Hypothesis senv_refl:
    (Genv.genv_senv ge) = (Genv.genv_senv tge).


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

  - 
    rewrite find_ext_funct_refl in H0.
    eapply exec_step_external;eauto.
    rewrite <- senv_refl. auto.    
Qed.

Lemma initial_state_gen_match: forall rs m st tprog' (MAIN: prog_main prog = prog_main tprog),
    decode_prog_code_section tprog = OK tprog' ->
  initial_state_gen instr_size (decode_program instr_size prog) rs m st ->
  exists st', initial_state_gen instr_size (decode_program instr_size tprog') rs m st' /\ st = st'.
Proof.
  intros.
  inv H0.

  set (ge2:= (globalenv instr_size (decode_program instr_size tprog'))).
  set (rs0':= (((Pregmap.init Vundef) # PC <-
           (Genv.symbol_address ge2 (prog_main (decode_program instr_size tprog')) Ptrofs.zero))
                 # X2 <- Vnullptr) # X1 <- Vnullptr).
  
  exists (State rs0' m).
  split.
  econstructor;eauto.
  f_equal. unfold rs0,rs0'.
  generalize  symbol_address_pres.
  unfold ge,tge. unfold RelocProgSemantics1.globalenv,RelocProgSemantics2.globalenv.
  rewrite H. intros SYMB.
  unfold ge0,ge2.
  assert ((prog_main (decode_program instr_size prog)) = (prog_main (decode_program instr_size tprog'))).
  unfold decode_program. unfold decode_prog_code_section in H.
  monadInv H. simpl.  auto.

  rewrite H0.
  erewrite SYMB. auto.
Qed.

End PRESERVATION.

End WITH_INSTR_SIZE.
