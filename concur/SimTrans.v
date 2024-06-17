Require Import Coqlib.
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import CKLR.
Require Import LanguageInterface.
Require Import Smallstep.

Require Import CallconvNew.
Require Import CA InjectFootprint.


(** SimTrans.v : build a extended simulation from the thread_local simulation *)

(*Test : transfer a "CAinjp simulation"*)

Section SimTransfer.

  Variable prog : Clight.program.
  Variable tprog : Asm.program.

  Definition OpenC := Clight.semantics1 prog.
  Definition OpenA := Asm.semantics tprog.

  Hypothesis Big_sim : forward_simulation cc_c_asm_injp cc_c_asm_injp OpenC OpenA.


  Lemma injp_acc_acce: forall w1 w2, injp_acc w1 w2 -> injp_acce w1 w2.
  Proof.
    intros. inv H. constructor; eauto.
    - destruct H4. split. auto. eapply Mem.unchanged_on_implies; eauto.
      intros. red in H. apply H.
    - destruct H5. split. auto. eapply Mem.unchanged_on_implies; eauto.
      intros. apply H.
  Qed.
        
  Theorem New_sim : GS.forward_simulation cc_c_asm_injp_new OpenC OpenA.
  Proof.
    inv Big_sim. inv X.
    econstructor. econstructor.
    - auto.
    - instantiate (3:= fsim_index).
      instantiate (2:= fsim_order).
      Search Mem.unchanged_on.
      set (MS := fun se1 se2 gw wp i s1 s2 =>
                   fsim_match_states se1 se2 gw i s1 s2  /\
                     injp_acc (get gw) wp).
      intros until w.
      intros MSE Gvalid.
      exploit fsim_lts; eauto.
      intros FSIM. inv FSIM.
      econstructor; intros.
      + exploit fsim_match_initial_states; eauto.
        intros [i [s2 [A B]]].
        exists i, s2. split. auto.
        instantiate (1:= fun se1 se2 w wp i s1 s2 =>
                           fsim_match_states se1 se2 w i s1 s2 /\ injp_acc (get w) wp).
        simpl. split. auto. reflexivity.
      + simpl in H. destruct H. exploit fsim_match_final_states; eauto.
        intros [r2 [A B]].
        exists r2. split. auto. split. red. simpl.
        apply injp_acc_acce. auto. simpl.
        inv B. simpl. destruct gw. simpl in *. econstructor.
        Search injp_acce.
        admit.
        red in H.
        

      admit.
    - auto.
  Qed.
  
  
