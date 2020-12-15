
Require Import LanguageInterface CallconvAlgebra Invariant.
Require Import CKLR Inject InjectFootprint Extends.
Require Import Mach Locations Conventions Asm.
Require Import ValueAnalysis.
Require Import Allocproof Asmgenproof0.


(** * Commutation properties *)

(** ** [cc_c_locset] *)

(** The commutation of [cc_c_locset] basically follows the way the
  original LTL semantics evaluates calls to external functions: we
  read out the arguments from the location set, then write back the
  result and mark the appropriate registers undefined. *)

Lemma locmap_getpair_inject f ls1 ls2 p:
  forall_rpair (fun l => Val.inject f (ls1 l) (ls2 l)) p ->
  Val.inject f (Locmap.getpair p ls1) (Locmap.getpair p ls2).
Proof.
  destruct p; cbn; intuition auto.
  apply Val.longofwords_inject; auto.
Qed.

Lemma commut_c_locset R:
  ccref (cc_c_locset @ cc_locset R) (cc_c R @ cc_c_locset).
Proof.
  intros [[_ w] [sg wR]] se1 se2 q1 q2 [[ ] Hse2] (qi & Hq1i & Hqi2).
  cbn in * |- . destruct Hqi2. inv Hq1i.
  exists (se2, wR, sg). repeat apply conj.
  - cbn; auto.
  - set (args1 := (fun p => Locmap.getpair p ls1) ## (loc_arguments sg)).
    set (args2 := (fun p => Locmap.getpair p ls2) ## (loc_arguments sg)).
    exists (cq vf2 sg args2 m2). split.
    + constructor; auto. clear - H0. subst args1 args2.
      unfold loc_external_rel in H0.
      pose proof (loc_arguments_external sg).
      induction loc_arguments; cbn in *; auto.
      constructor; auto.
      apply locmap_getpair_inject.
      assert (forall_rpair (loc_external sg) a) by eauto.
      destruct a; cbn in *; intuition auto.
    + constructor; auto.
  - intros r1 r2 (ri & (wR' & HwR' & Hr1i) & Hri2).
    destruct Hr1i. inv Hri2. rename rs' into ls2'.
    set (ls1' := Locmap.setpair (loc_result sg) vres1 (LTL.undef_caller_save_regs ls1)).
    exists (lr ls1' m1'). split.
    + constructor.
      * subst ls1'. clear.
        destruct loc_result.
        -- cbn. rewrite Locmap.gss. reflexivity.
        -- cbn. admit. (* register pairs, would need typing *)
    + eexists; split; eauto.
      constructor; auto. subst ls1'. red.
      destruct (loc_result sg) eqn:RES; cbn in *.
      * intuition subst. rewrite Locmap.gss. auto.
      * admit. (* loc pairs *)
Admitted.

(** ** [cc_locset_mach] *)

(** For queries, we need to synthesizing the target-level locset by
  extracting and removing arguments from the memory. *)

Lemma match_agree_args R w sg m1 m2 sp1 sp2 ls1 rs2:
  agree_args sg m1 sp1 ls1 ->
  match_mem R w m1 m2 ->
  mi R w sp1 = Some (sp2, 0) ->
  (forall r, Val.inject (mi R w) (ls1 (Locations.R r)) (rs2 r)) ->
  exists ls2,
    agree_args sg m2 sp2 ls2 /\
    (forall r, ls2 (Locations.R r) = rs2 r) /\
    loc_external_rel sg (Val.inject (mi R w)) ls1 ls2.
Proof.
  intros Hargs1 Hm Hsp Hrs.
  exists (make_locset rs2 m2 (Vptr sp2 Ptrofs.zero)).
  repeat apply conj.
  - intros ofs ty l Hl. subst l. specialize (Hargs1 ofs ty Hl). clear - Hargs1 Hm Hsp.
    unfold load_stack in Hargs1. eapply transport in Hargs1.
    2: { clear - Hm Hsp. repeat rstep. constructor; eauto. }
    destruct Hargs1 as (v2 & Hv2 & Hv).
    rewrite Ptrofs.add_zero_l in Hv2.
    cbn [make_locset]. setoid_rewrite Hv2. reflexivity.
  - auto.
  - intros l Hl. destruct Hl.
    + cbn. auto.
    + specialize (Hargs1 ofs ty H). clear - Hargs1 Hm Hsp.
      unfold load_stack in Hargs1. eapply transport in Hargs1.
      2: { clear - Hm Hsp. repeat rstep. constructor; eauto. }
      destruct Hargs1 as (v2 & Hv2 & Hv).
      rewrite Ptrofs.add_zero_l in Hv2.
      cbn [make_locset]. setoid_rewrite Hv2. cbn. auto.
Qed.

Instance cklr_free_args R:
  Monotonic free_args
    (|= - ==> match_mem R ++> block_inject_sameofs @@ [mi R] ++> k1 option_le (<> match_mem R)).
Proof.
  unfold free_args. repeat rstep. clear - H0.
  induction regs_of_rpairs as [ | [ | [ ]]]; cbn [loc_footprints]; rauto.
Qed.

Instance bis f b1 b2:
  RExists (f b1 = Some (b2, 0)) (block_inject_sameofs f) b1 b2.
Proof.
  firstorder.
Qed.

Instance loc_external_subrel:
  Monotonic loc_external_rel (- ==> subrel ++> subrel).
Proof.
  unfold loc_external_rel. repeat rstep.
  red. intros. auto.
Qed.

Lemma commut_locset_mach R:
  ccref (cc_locset_mach @ cc_mach R) (cc_locset R @ cc_locset_mach).
Proof.
  intros [[_ [sg ls1]] wR] se1 se2 q1 q2 [[ ] Hse2] (qi & Hq1i & Hqi2).
  cbn in * |- . destruct Hqi2. inv Hq1i. rename m' into m1_. rename ls into ls1.

  (** Synthesizing the query *)
  transport H12. rename x into m2_.
  edestruct match_agree_args as (ls2 & Hargs2 & Hrs2 & Hls); eauto.
  { intro r. rewrite H13. eauto. }
  set (ls2wt l := Val.ensure_type (ls2 l) (Loc.type l)).

  exists (se2, (sg, wR'), (sg, rs2)). repeat apply conj.
  - cbn. split; rauto.
  - exists (lq vf2 sg ls2 m2_). split.
    + econstructor; try rauto.
      * admit. (* vf1 <> Vundef -- add in upper conventions or move back to [fb] *)
    + constructor; eauto.
      * revert H10. rstep. rstep. rstep. econstructor; eauto.
      * admit. (* type of RA -- need to constrain in cc_mach? *)
  - intros r1 r2 (ri & (wR'' & HwR'' & Hr1i) & Hri2). 
    destruct Hr1i. inv Hri2. rename rs' into rs2'.
    set (rs1' r := result_regs sg ls1 ls1' (Locations.R r)).
    exists (mr rs1' m1'). split.
    + constructor; auto.
      * intros r Hr. unfold rs1'. rewrite <- result_regs_agree_callee_save; auto.
      * intros r Hr. unfold rs1'. cbn. destruct in_dec; tauto.
    + exists wR''. split; [rauto | ]. constructor; auto.
      intro r. unfold rs1', result_regs.
      destruct in_dec. { rewrite H16; auto. }
      destruct is_callee_save eqn:Hr; auto.
      rewrite H12 by auto. rewrite H13. generalize (H2 r).
      repeat rstep. change (wR ~> wR''). rauto.
Admitted.
