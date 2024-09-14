Require Import Coqlib.
Require Import List.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import SmallstepLinking Smallstep.
Require Import Linking.
Require Import Classical.
Require Import Invariant.

(** Module safety : similar to the preservation of invariant in LTS *)

Definition safe {liA liB st} (L: lts liA liB st) (s: st) : Prop :=
  (exists r, final_state L s r)
  \/ (exists q, at_external L s q)
  \/ (exists t, exists s', Step L s t s').

Definition not_stuck {liA liB st} (L: lts liA liB st) (s: st) : Prop :=
  (exists r, final_state L s r)
  \/ (exists q, at_external L s q)
  \/ (exists t, exists s', Step L s t s').


(* Definition partial_safe {liA liB st} mem_error (L: lts liA liB st) (s: st) : Prop := *)
(*   (exists r, final_state L s r) *)
(*   \/ (exists q, at_external L s q) *)
(*   \/ (exists t, exists s', Step L s t s') *)
(*   \/ (mem_error liA liB st L s). *)

(* well-formed reachable state in module requires some restriction on
incoming query and reply *)
Inductive reachable {liA liB st} (IA: invariant liA) (IB: invariant liB) (L: lts liA liB st) (wI: inv_world IB) (s: st) : Prop :=
| initial_reach: forall q s0 t
    (WT: query_inv IB wI q)
    (INIT: initial_state L q s0)
    (STEP: Star L s0 t s),
    reachable IA IB L wI s
| external_reach: forall q r s1 s2 t w
    (* s1 also must be reachable. TODO: s1 should be in at_external? *)
(*     Otherwise we cannot prove reachable state is sound *)
    (REACH: reachable IA IB L wI s1)
    (ATEXT: at_external L s1 q)
    (WTQ: query_inv IA w q)
    (WTR: reply_inv IA w r)
    (AFEXT: after_external L s1 r s2)
    (STEP: Star L s2 t s),
    reachable IA IB L wI s.

Lemma step_reachable {liA liB st} IA IB (L: lts liA liB st) s1 t s2 w:
  Step L s1 t s2 ->
  reachable IA IB L w s1 ->
  reachable IA IB L w s2.
Proof.
  intros STEP REA.
  inv REA.
  - eapply initial_reach; eauto.
    eapply star_right; eauto.
  - eapply external_reach; eauto.
    eapply star_right; eauto.
Qed.


Record lts_safe {liA liB S} se (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB) (SI: lts liA liB S -> S -> Prop) (wI: inv_world IB) :=
  {
    reachable_safe: forall s,
      reachable IA IB L wI s ->
      SI L s;
    
    (* properties of compositionality *)
    initial_progress: forall q,
      valid_query L q = true ->
      query_inv IB wI q ->
      (exists s, initial_state L q s);
    
    external_progress: forall s q,
      reachable IA IB L wI s ->
      at_external L s q ->
      exists wA, symtbl_inv IA wA se /\ query_inv IA wA q /\
              forall r, reply_inv IA wA r ->
                   (* after external progress *)
                   (exists s', after_external L s r s');

    final_progress: forall s r,
      reachable IA IB L wI s ->
      final_state L s r ->
      reply_inv IB wI r;    
  }.

Definition module_safe_se {liA liB} (L: semantics liA liB) (IA IB: invariant _) SI se :=
  forall w,
    symtbl_inv IB w se ->
    lts_safe se (L se) IA IB SI w.

Definition module_safe {liA liB} (L: semantics liA liB) (IA IB: invariant _) SI :=
  forall se,
    Genv.valid_for (skel L) se ->
    module_safe_se L IA IB SI se.

(** Proof of lts_safe by the method of preservation and progress *)

(* silightly different from lts_preserves in Invariant.v *)
Record lts_invariant_preserves {liA liB S} (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB) (IS: inv_world IB -> S -> Prop) (w: inv_world IB) :=
  {
    preserves_step s t s':
      IS w s ->
      Step L s t s' ->
      IS w s';
    preserves_initial_state q s:
      (* valid_query L q = true -> *)
      query_inv IB w q ->
      initial_state L q s ->
      IS w s;
    (** Why? *)
    preserves_external s s' q r wA:
      IS w s ->
      at_external L s q ->
      query_inv IA wA q ->
      reply_inv IA wA r ->
      after_external L s r s' ->
      IS w s';
  }.

(* not_stuck is hard code in lts_invariant_progress *)
Record lts_invariant_progress {liA liB S} se (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB) (IS: inv_world IB -> S -> Prop) (w: inv_world IB) :=
  {
    progress_internal_state: forall s,
      IS w s ->
      not_stuck L s;

    progress_initial_state: forall q,
      valid_query L q = true ->
      query_inv IB w q ->
      (exists s, initial_state L q s);
    
    progress_external_state: forall s q,
      IS w s ->
      at_external L s q ->
      exists wA, symtbl_inv IA wA se /\ query_inv IA wA q /\
              forall r, reply_inv IA wA r ->
                   (* after external progress *)
                   (exists s', after_external L s r s');

    progress_final_state: forall s r,
      IS w s ->
      final_state L s r ->
      reply_inv IB w r;
  }.


Record module_safe_components {liA liB} (L: semantics liA liB) (IA: invariant liA) (IB: invariant liB) :=
  {
    msafe_invariant: inv_world IB -> state L -> Prop;

    msafe_preservation: forall se wB,
      symtbl_inv IB wB se ->
      Genv.valid_for (skel L) se ->
      lts_invariant_preserves (L se) IA IB msafe_invariant wB;

    msafe_progress: forall se wB,
      symtbl_inv IB wB se ->
      Genv.valid_for (skel L) se ->
      lts_invariant_progress se (L se) IA IB msafe_invariant wB;
  }.

Lemma star_preserves_invariant {liA liB S} (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB): forall w s t s' IS (PRE: lts_invariant_preserves L IA IB IS w),
    IS w s ->
    Star L s t s' ->
    IS w s'.
Proof.
  induction 3. auto.
  apply IHstar. eapply preserves_step; eauto.
Qed.

Lemma reachable_preserves_invariant {liA liB S} (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB): forall w s IS (PRE: lts_invariant_preserves L IA IB IS w),
    reachable IA IB L w s ->
    IS w s.
Proof.
  induction 2.
  - eapply star_preserves_invariant; eauto.
    eapply preserves_initial_state; eauto.
  - eapply star_preserves_invariant. 3: eapply STEP. eauto.
    eapply preserves_external; eauto.
Qed.

(* soundness of module_safe_components *)
Lemma module_safe_components_sound {liA liB} (L: semantics liA liB) (IA: invariant liA) (IB: invariant liB):
  module_safe_components L IA IB ->
  module_safe L IA IB not_stuck.
Proof.
  intros SAFE. inv SAFE.
  red. intros se VSE w WTSE.
  exploit msafe_preservation0; eauto. intros PRE.
  exploit msafe_progress0; eauto. intros PRO.
  constructor.
  (* reachable not stuck *)
  - intros s REACH.
    eapply reachable_preserves_invariant with (IS:= msafe_invariant0) in REACH; auto.
    eapply progress_internal_state; eauto.
  (* initial_progress *)
  - eapply progress_initial_state; eauto.
  (* external_progress *)
  - intros s q REACH.
    eapply progress_external_state; eauto.
    eapply reachable_preserves_invariant; eauto.
  (* final_progress *)
  - intros s r REACH.
    eapply progress_final_state; eauto.
    eapply reachable_preserves_invariant; eauto.
Qed.


(* Propeties of reachable state in composed semantics *)
Section REACH.

Context {li} (I: invariant li) (L: bool -> semantics li li). 
Context (se: Genv.symtbl).
Context (w: inv_world I).
(* A generalized wf_state specifying rechable property and invariant world in the frame *)

Inductive wf_frames : list (frame L) -> inv_world I -> Prop :=
| wf_frames_nil: wf_frames nil w
| wf_frames_cons: forall i s q w1 w2 fms
    (WF: wf_frames fms w1)
    (VSE1: symtbl_inv I w1 se)
    (FREACH: reachable I I (L i se) w1 s)
    (EXT: at_external (L i se) s q)
    (WTQ: query_inv I w2 q)
    (* (VSE2: symtbl_inv I w2 se) *)
    (* desrible progress property here *)
    (PGS: forall r, reply_inv I w2 r ->
               exists s', after_external (L i se) s r s'),
    wf_frames ((st L i s) :: fms) w2.

Inductive wf_state : list (frame L) -> Prop :=
| wf_state_cons: forall i s k w1
    (WFS: wf_frames k w1)
    (VSE: symtbl_inv I w1 se)
    (SREACH: reachable I I (L i se) w1 s),
    wf_state (st L i s :: k).


Section SAFE.

Hypothesis (VALIDSE: forall i, Genv.valid_for (skel (L i)) se).
Hypothesis (SAFE: forall i, module_safe_se (L i) I I not_stuck se).

Lemma step_wf_state sk s1 t s2:
  Step (SmallstepLinking.semantics L sk se) s1 t s2 ->
  wf_state s1 ->
  wf_state s2.
Proof.
  intros STEP WF.
  inv STEP.
  - inv WF. subst_dep.
    econstructor; eauto.
    eapply step_reachable; eauto.
  - inv WF. subst_dep.
    (* external_progress of s *)    
    exploit (@external_progress li); eauto. eapply SAFE; eauto.
    intros (wA & SYMBINV & QINV & AFTER).
    econstructor; eauto.
    econstructor; eauto.
    eapply initial_reach; eauto.
    econstructor; eauto.
  - inv WF. subst_dep.
    exploit (@final_progress li); eauto. eapply SAFE; eauto.
    intros WTR.
    inv WFS. subst_dep.
    econstructor; eauto.
    eapply external_reach; eauto.
    eapply star_refl.
Qed.

Lemma star_wf_state sk s1 t s2:
  Star (SmallstepLinking.semantics L sk se) s1 t s2 ->
  wf_state s1 ->
  wf_state s2.
Proof.
  induction 1; auto.
  intros WF. eapply IHstar.
  eapply step_wf_state; eauto.
Qed.


Lemma reachable_wf_state sk s (WTSE: symtbl_inv I w se):
  reachable I I (SmallstepLinking.semantics L sk se) w s ->
  wf_state s.
Proof.
  induction 1.
  - eapply star_wf_state; eauto.
    inv INIT.
    econstructor; eauto.
    econstructor.
    eapply initial_reach; eauto.
    eapply star_refl.
  - eapply star_wf_state; eauto.
    inv AFEXT. inv ATEXT. inv IHreachable. subst_dep.
    econstructor; eauto. 
    eapply external_reach; eauto.
    eapply star_refl.
Qed.

End SAFE.

End REACH.

(** Proof of compositionality of module safe *)

Lemma compose_safety {li} (I: invariant li) L1 L2 L:
  module_safe L1 I I not_stuck ->
  module_safe L2 I I not_stuck ->
  compose L1 L2 = Some L ->
  module_safe L I I not_stuck.
Proof.
  intros SAFE1 SAFE2 COMP. unfold compose in *. unfold option_map in *.
  destruct (link (skel L1) (skel L2)) as [sk|] eqn:Hsk; try discriminate. inv COMP.
  set (L := fun i:bool => if i then L1 else L2).
  red. intros se w VALID INV.
  assert (VALIDSE: forall i, Genv.valid_for (skel (L i)) se).
  destruct i.
  eapply Genv.valid_for_linkorder.
  eapply (link_linkorder _ _ _ Hsk). eauto.
  eapply Genv.valid_for_linkorder.
  eapply (link_linkorder _ _ _ Hsk). eauto.
  assert (SAFE: forall i, module_safe_se (L i) I I not_stuck se).
  { intros i. generalize (VALIDSE i). intros VSE.
    destruct i; simpl; auto. }
  constructor.
  (* rechable not stuck *)
  - intros s WFREACH.    
    exploit (@reachable_wf_state li); eauto.
    intros WFST.
    (* destruct the frames to case analyze the top frame *)
    destruct s. inv WFST.
    destruct f. inv WFST. subst_dep.
    (* s0 is not stuck because (L i) is safe *)
    exploit (@reachable_safe li li (state (L i))); eauto.
    eapply SAFE; eauto. intros SAFES0.
    (* case analysis of not_stuck of s0 *)
    destruct SAFES0 as [(r & FINAL)|[(q & EXT)|(t1 & s1 & STEP1)]].
    (* s0 in final state *)
    + destruct s.
      (* composed semantics in final state *)
      * red. left. exists r.
        constructor. auto.
      (* composed semantics can make a step to caller *)
      * red. right. right.
        inv WFS.
        (* final_prgress in s0 *)
        exploit (@final_progress li). eapply SAFE.
        eapply VSE. eauto. eauto. intros WTR.        
        exploit PGS; eauto. intros (s1' & AFEXT).
        (* s0 can return a well-typed reply to s1 which is in at_external to make a step *)
        do 2 eexists.
        eapply step_pop; eauto.
    (* s0 in at_external state *)
    + exploit (@external_progress li); eauto.
      eapply SAFE; eauto.
      intros (wA & SYMBINV & QINV & AFTER). clear AFTER.
      destruct (orb (valid_query (L true se) q) (valid_query (L false se) q)) eqn: VQ.
      (* step_push *)
      * eapply orb_true_iff in VQ.
        red. right. right.
        destruct VQ as [VQ1|VQ2].
        -- exploit (@initial_progress li); eauto. eapply SAFE; eauto.
           intros (s1 & INIT1).
           do 2 eexists.        
           eapply step_push; eauto. 
        -- exploit (@initial_progress li); eauto. eapply SAFE; eauto.
           intros (s1 & INIT1).
           do 2 eexists.        
           eapply step_push; eauto.
      (* composed module in at_external *)
      * red. right. left.
        exists q. econstructor. eauto.
        eapply orb_false_iff in VQ. destruct VQ.
        intros. destruct j; auto.
    (* s0 can make a step *)
    + red. right. right.
      do 2 eexists. eapply step_internal. eauto.
  (* initial_progress *)
  - intros q VQ SQ. simpl in *.
    unfold SmallstepLinking.valid_query in VQ.
    eapply orb_true_iff in VQ. destruct VQ as [VQ1| VQ2].
    + exploit (@initial_progress li); eauto.
      eapply SAFE; eauto.
      intros (s0 & INIT).
      eexists. econstructor; eauto.
    + exploit (@initial_progress li); eauto.
      eapply SAFE; eauto.
      intros (s0 & INIT).
      eexists. econstructor; eauto.
  (* external_progress *)
  - intros s q REACH EXT. inv EXT.
    eapply reachable_wf_state in REACH; eauto.
    inv REACH. subst_dep.
    exploit (@external_progress li); eauto. eapply SAFE; eauto.
    intros (wA & SYMBINV & QINV & AFTER).
    exists wA. split; auto. split; auto.
    intros r WTR.
    exploit AFTER; eauto. intros (s1 & AFEXT).
    exists (st L i s1 :: k).
    constructor. auto.
  (* final_progress *)
  - intros s r REACH FINAL.
    inv FINAL.
    eapply reachable_wf_state in REACH; eauto. inv REACH. subst_dep.
    inv WFS.
    exploit (@final_progress li); eauto. eapply SAFE; eauto.
Qed.


(* similar to ccref *)
Record bsim_invariant {li1 li2} (cc: callconv li1 li2) (I1: invariant li1) (I2: invariant li2) : Type :=
  {
    (* incoming_query2 and outgoing_query2 are used to establish
    match_states between rechable states *)
    incoming_query2: forall w2 se1 se2 ccw q2,
      symtbl_inv I2 w2 se2 ->
      match_senv cc ccw se1 se2 ->
      query_inv I2 w2 q2 ->
      exists w1 q1, symtbl_inv I1 w1 se1 /\
                 query_inv I1 w1 q1 /\
                 match_query cc ccw q1 q2 /\
                 (* outgoing_reply1 is embedded here because it is
                 stated in w2. It is used to establish progress
                 properties *)
                 forall r1 r2, reply_inv I1 w1 r1 ->
                          match_reply cc ccw r1 r2 ->
                          reply_inv I2 w2 r2;

    outgoing_query2: forall w2 ccw q1 q2,
      query_inv I2 w2 q2 ->
      match_query cc ccw q1 q2 ->
      exists w1, query_inv I1 w1 q1 /\
              (* incoming_reply2 is embedded here *)
              forall r2, reply_inv I2 w2 r2 ->
                    exists r1, reply_inv I1 w1 r1 /\
                            match_reply cc ccw r1 r2;
    
    (* outgoing_query1 and outgoing_reply1 are used to establish
    progress properties *)
    outgoing_query1: forall w1 ccw q1 q2,
      query_inv I1 w1 q1 ->
      match_query cc ccw q1 q2 ->
      exists w2, query_inv I2 w2 q2 /\
              (* incoming_reply1 is embedded here *)
              forall r1, reply_inv I1 w1 r1 ->
                    exists r2, reply_inv I2 w2 r2 /\
                            match_reply cc ccw r1 r2;    
  }.



(** Safety Preservation Under Backward Simulation *)

Section SAFETY_PRESERVATION.

Context {li1 li2} (cc: callconv li1 li2).
Context (L1: semantics li1 li1) (L2: semantics li2 li2).
Context (I1: invariant li1) (I2: invariant li2).
Context (se1 se2: Genv.symtbl) (ccw: ccworld cc).

Hypothesis BSIM_INV: bsim_invariant cc I1 I2.

Lemma module_safety_preservation:
  match_senv cc ccw se1 se2 ->
  module_safe_se L1 I1 I1 safe se1 ->
  backward_simulation cc cc L1 L2 ->
  module_safe_se L2 I2 I2 safe se2.
Proof.
  (* (** Test2  *) *)
  (* intros MSENV SAFE [BSIM]. *)
  (* destruct BSIM as [index order match_states SKEL PROP WF]. *)
  (* red. intros w2 VSE2 SINV2. *)
  (* (* set (safe' (l: lts li2 li2 (state L2)) s := *) *)
  (* (*        exists w1: inv_world I1, *) *)
  (* (*          safe l s /\ *) *)
  (* (*          symtbl_inv I1 w1 se1 /\ *) *)
  (* (*          forall r1, *) *)
  (* (*            reply_inv I1 w1 r1 -> *) *)
  (* (*            exists r2, reply_inv I2 w2 r2). *) *)

  (* (* cut (lts_safe se2 (L2 se2) I2 I2 safe' w2). *) *)
  (* split. *)
  (* - admit. *)
  (* (* initial_safe *) *)
  (* - intros q2 VQ2 QINV2. *)
  (*   destruct (inv_initial _ _ _ BSIM_INV w2 se1 se2 ccw q2 SINV2 MSENV QINV2) as (w1 & q1 & SINV1 & QINV1 & MQ). *)
  (*   assert (VSE1: Genv.valid_for (skel L1) se1). *)
  (*   (** TODO: we need the invert of match_senv_valid_for  *) *)
  (*   admit. *)
  (*   assert (VQ1: valid_query (L1 se1) q1 = true). *)
  (*   { erewrite <- bsim_match_valid_query. eauto. *)
  (*     eapply PROP. eauto. *)
  (*     auto. auto. } *)
  (*   edestruct (initial_safe _ _ _ _ _ _ (SAFE w1 VSE1 SINV1) q1 VQ1 QINV1) as ((s1 & INIT1) & INIT1').  *)
  (*   edestruct @bsim_match_initial_states as [EXIST MATCH]; eauto. *)
  (*   split. *)
  (*   + eapply EXIST. eauto. *)
  (*   + intros s2 INIT2. *)
  (*     (** use bsim_progress *) *)
  (*     exploit MATCH; eauto. *)
  (*     intros (s1' & INIT1'' & (idx & MST)). *)
  (*     (* show s1' is safe *) *)
  (*     exploit INIT1'. eapply INIT1''. intros SAFES1'. *)
  (*     (** TODO: use safe s1' and step_safe to prove smallstep.safe s1' *) *)
  (*     eapply bsim_progress; eauto. *)
  (*     admit. *)
  (* - intros s2 q2 REACH2 EXTERN2. *)
  (*   (** TODO: how to prove there is a reachable state s1 and s1 simulates s2*) *)
  (*   assert (A: exists s1 idx, reachable (L1 se1) s1 /\ match_states se1 se2 ccw idx s1 s2). *)
  (*   admit. *)
  (*   destruct A as (s1 & idx & REACH1 & MST). *)
    
    
  (** Test1  *)
  (* intros MSENV SAFE BSIM. *)
  (* inv BSIM. rename X into BSIM. *)
  (* red. intros w2 VSE2 INV2. *)
  (* generalize (inv_match_symtbl cc I1 I2 BSIM_INV w2 se1 se2 ccw INV2 MSENV). *)
  (* intros (w1 & INV1). *)
  (* assert (VSE1: Genv.valid_for (skel L1) se1). *)
  (* (** TODO: use match_senv to prove it but match_senv does not guarantee the *)
  (* backward valid_for? *)   *)
  (* admit.  *)
  (* exploit SAFE; eauto. *)
  (* intros LTSSAFE1. *)
  (* (* use bsim_lts *) *)
  (* inv BSIM. generalize (bsim_lts se1 se2 ccw MSENV VSE1). *)
  (* intros bsim_prop. inv bsim_prop. *)
Admitted.

End SAFETY_PRESERVATION.
