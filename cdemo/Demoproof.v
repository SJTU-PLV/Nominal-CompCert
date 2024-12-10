Require Import Coqlib Errors.
Require Import AST Linking Smallstep SmallstepClosed Invariant CallconvAlgebra.

Require Import Conventions Mach.
Require Import Locations.
Require Import LanguageInterface.

Require Import Integers.
Require Import Values Memory.

Require Import CallconvBig InjectFootprint Injp.
Require Import CAnew.
Require Import Asm Asmrel.
Require Import Asmgenproof0 Asmgenproof1.
Require Import Encrypt EncryptSpec Encryptproof.
Require Import Client Server.

Require Import SmallstepLinking VCompBig HCompBig CallConvLibs.
Require Import Composition CMulti AsmMulti ThreadLinking Compiler.


Import GS.

(** 1st step : module linking *)

Section LINKING.
  Variable client_s server_s : Asm.program.
  
  Hypothesis compile_client : transf_clight_program client = OK client_s.
  Hypothesis compile_server : transf_clight_program server = OK server_s.

  Variable c_spec c_server_spec : Smallstep.semantics li_c li_c.
  
  Hypothesis compose_c1 : compose L_E (Clight.semantics1 server) = Some c_server_spec.
  Hypothesis compose_c2 : compose (Clight.semantics1 client) c_server_spec = Some c_spec.

  Variable asm_prog asm_server_prog : Asm.program.

  Hypothesis compose_asm1 : link encrypt_s server_s = Some asm_server_prog.
  Hypothesis compose_asm2 : link client_s asm_server_prog = Some asm_prog.

  Lemma client_sim : forward_simulation cc_compcert (Clight.semantics1 client) (Asm.semantics client_s).
  Proof.
    eapply clight_semantic_preservation. eapply transf_clight_program_match.
    apply compile_client.
  Qed.

  Lemma server_sim : forward_simulation cc_compcert (Clight.semantics1 server) (Asm.semantics server_s).
  Proof.
    eapply clight_semantic_preservation. eapply transf_clight_program_match.
    apply compile_server.
  Qed.

  Lemma module_linking_correct1 :
    forward_simulation cc_compcert c_server_spec (Asm.semantics asm_server_prog).
  Proof.
    rewrite <- cctrans_id_2.
    eapply st_fsim_vcomp; eauto.
    2: eapply asm_linking; eauto.
    eapply compose_simulation.
    apply correctness_L_E. apply server_sim. eauto.
    unfold compose. cbn.
    apply link_erase_program in compose_asm1. rewrite compose_asm1. cbn. f_equal. f_equal.
    apply Axioms.functional_extensionality. intros [|]; auto.
  Qed.

  Theorem module_linking_correct :
    forward_simulation cc_compcert c_spec (Asm.semantics asm_prog).
  Proof.
    rewrite <- cctrans_id_2.
    eapply st_fsim_vcomp; eauto.
    2: eapply asm_linking; eauto.
    eapply compose_simulation.
    apply client_sim. apply module_linking_correct1. eauto.
    unfold compose. cbn.
    apply link_erase_program in compose_asm2. rewrite compose_asm2. cbn. f_equal. f_equal.
    apply Axioms.functional_extensionality. intros [|]; auto.
  Qed.

  Theorem thread_linking_correct :
    Closed.forward_simulation (Concur_sem_c c_spec) (Concur_sem_asm (Asm.semantics asm_prog)).
  Proof.
    apply Opensim_to_Globalsim; eauto. apply module_linking_correct.
  Qed.

End LINKING.
