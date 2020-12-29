
Require Import LanguageInterface CallconvAlgebra Invariant.
Require Import CKLR Inject InjectFootprint Extends VAInject VAExtends.
Require Import Mach Locations Conventions Asm.
Require Import ValueAnalysis.
Require Import Allocproof Lineartyping Asmgenproof0.
Unset Program Cases.

Coercion cc_c : cklr >-> callconv.


(** * Calling convention *)

(** Ultimately we will want to reformulate (part of) the overall
  simulation convention as a monolithic thing. For now we just use the
  composite definition of cc_compcert found later in this file. *)

(*
Definition get_pair (p: rpair preg) (rs: regset) :=
  match p with
    | One r => rs r
    | Twolong r1 r2 => Val.longofwords (rs r1) (rs r2)
  end.

Inductive cc_compcert_mq: _ -> c_query -> query li_asm -> Prop :=
  cc_compcert_mq_intro se f vf sg vargs mc rs vargs' ma ma_ :

    (* Function *)
    Val.inject f vf rs#PC ->

    (* Arguments *)
    Asm.extcall_arguments rs ma sg vargs' ->
    Val.inject_list f vargs vargs' ->
    Val.has_type_list vargs (sig_args sg) ->

    (* Memory *)
    free_args sg ma rs#SP = Some ma_ ->
    Mem.inject f mc ma_ ->
    romatch_all se (bc_of_symtbl se) mc ->

    (* Queries *)
    cc_compcert_mq
      (se, sg, injw f (Mem.nextblock mc) (Mem.nextblock ma))
      (cq vf sg vargs mc)
      (rs, ma).

Inductive cc_compcert_mr: _ -> c_reply -> reply li_asm -> Prop :=
  cc_compcert_mr_intro se sg f nbc nba f' vres mc' rs' ma' :

    (* New injection *)
    inject_incr f f' ->
    (forall b1 b2 delta,
        f b1 = None -> f' b1 = Some (b2, delta) ->
        (nbc <= b1 /\ nba <= b2)%positive) ->
    Pos.le nbc (Mem.nextblock mc') ->
    Pos.le nba (Mem.nextblock ma') ->

    (* Result *)
    Val.inject f' vres (get_pair (loc_external_result sg) rs') ->
    Val.has_type vres (proj_sig_res sg) ->

    (* Memory *)
    Mem.inject f' mc' ma' ->
    romatch_all se (bc_of_symtbl se) mc' ->

    (* Replies *)
    cc_compcert_mr
      (se, sg, injw f' (Mem.nextblock mc') (Mem.nextblock ma'))
      (cr vres mc')
      (rs', ma').

Program Definition cc_compcert: callconv li_c li_asm :=
  {|
    match_senv '(se, _, w) se1 se2 := se1 = se /\ inj_stbls w se1 se2;
    match_query := cc_compcert_mq;
    match_reply := cc_compcert_mr;
  |}.
Next Obligation. Admitted.
Next Obligation. Admitted.
*)

(** To match the memory transformations used in the passes of
  CompCert, we use the following strategy. For incoming calls, we will
  expand the target-level injection to generate the appropriate [inj]
  and [ext] components, which we can then commute over the
  intermediate calling conventions. For outgoing calls, we keep
  commuting them towards the front component of [cc_compcert],
  provided by the properties of [Clight], where they can absorbed. *)

(** ** Expansion *)

(** To match the passes of CompCert, we first expand the convention as follows. *)

(*
Lemma cc_c_asm_expand:
  cceqv cc_compcert (et_c @ cc_c_locset @ et_loc @ cc_locset_mach @ cc_mach_asm @ cc_asm vainj).
Proof.
  intros sg se _ q1 q2 [ ] Hq. destruct Hq.
  set (mrs := fun r => rs (preg_of r)).
  set (ls := make_locset mrs m rs#SP).
  exists (se, (se, sg), (se, sg, (se, (se, sg), (se, (sg, mrs), (rs, Mem.nextblock m))))).
  split; [ | split].
  - (* Symbol tables *)
    cbn. auto using rel_inv_intro.
  - (* Queries *)
    exists (cq rs#PC sg args m_). split.
    {
      constructor. cbn. auto.
    }
    exists (lq rs#PC sg ls m_). split.
    {
      constructor. admit. (* args read from ls *)
    }
    exists (lq rs#PC sg ls m_). split.
    {
      constructor. cbn. constructor.
      intros l Hl. destruct l as [ | [ ]]; cbn; auto.
      + apply H2.
      + admit. (* typing of argument -- need to weaken wt_locset in
        wt_loc to actual arguments and add typing constraint in cc_c_asm *)
    }
    exists (mq rs#PC rs#SP rs#RA (fun r => rs (preg_of r)) m). split.
    {
      constructor; auto.
      + admit. (* typing of RA -- add constraint in cc_c_asm *)
      + unfold agree_args. unfold extcall_arguments in H0.
        clear - H0. induction H0; cbn [In regs_of_rpairs]; try contradiction.
        intros ofs ty. rewrite in_app. intros [? | ?]; auto.
        admit. (* reading arguments -- use extcall_arguments *)
    }
    idtac.
    {
      constructor; auto.
      + admit. (* sp valid; can do if we use free_args + combine with inj *)
      + admit. (* ra defined *)
    }
  - (* Replies *)
    intros r1 r2 (xr1 & Hxr1 & ri & Hr1i & xri & Hxri & rj & Hrij & Hrj2).
    destruct Hxr1 as [Hr1wt], Hxri as [Hriwt]. cbn in *.

Admitted.
*)


(** * Triangular conventions *)

(** With our new approach the following should be unnecessary and we
  should be able to safely remove it. *)

Inductive make_corefl {A} (R : relation A) (x:A) : A -> Prop :=
  make_corefl_intro: R x x -> make_corefl R x x.

Program Definition cc_tr {li} (cc : callconv li li) :=
  {|
    match_senv w := make_corefl (match_senv cc w);
    match_query w := make_corefl (match_query cc w);
    match_reply := match_reply cc;
  |}.
Solve All Obligations with intros; destruct H, cc; auto.

Global Instance cc_tr_ccref:
  Monotonic (@cc_tr) (forallr -, ccref ++> ccref).
Proof.
  intros li cc1 cc2 Hcc w se _ q _ [Hse] [Hq].
  edestruct Hcc as (w' & Hse' & Hq' & Hr); eauto.
  cbn. eauto 10 using make_corefl_intro.
Qed.

Global Instance cc_tr_prop {li} (cc: callconv li li) (I: invariant li):
  PropagatesQueryInvariant (cc_tr cc) I.
Proof.
  constructor. cbn. intros w wI se _ q _ [Hse] HseI [Hq] HqI. eauto.
Qed.

Lemma cc_untr {li} (cc: callconv li li):
  ccref (cc_tr cc) cc.
Proof.
  intros w se1 se2 q1 q2 [Hse] [Hq]. cbn. eauto.
Qed.

Lemma cc_inj_inj_tr:
  ccref (cc_c inj) (cc_tr (cc_c inj) @ cc_c inj).
Admitted.

Lemma cc_ext_inj_tr:
  ccref (cc_c inj) (cc_tr (cc_c ext) @ cc_c inj).
Admitted.

Lemma cc_tr_compose {li} (cc1 cc2: callconv li li):
  cceqv (cc_tr (cc_tr cc1 @ cc2)) (cc_tr cc1 @ cc_tr cc2).
Proof.
  split.
  - intros [[_ w1] w2] se _ q _ [[[Hse1] Hse2]] [(_ & [Hq1] & Hq2)].
    exists (se, w1, w2). cbn in *. intuition (eauto using make_corefl_intro).
  - intros [[_ w1] w2] se _ q _ [[Hse1] [Hse2]] (_ & [Hq1] & [Hq2]).
    exists (se, w1, w2). cbn in *. intuition (eauto using make_corefl_intro).
Qed.


(** * Commutable typing constraints *)

(** The typing invariants [wt_c] and [wt_loc] do not commute with
  CKLRs, however the following alternative formulations of the typing
  constraints do. The idea is that source values are forced to
  [Vundef] when the target values are ill-typed. The gap can then be
  absorbed into a CKLR to recover the original invariant. *)

(** ** C-level typing constraints *)

Inductive et_c_mq sg: c_query -> c_query -> Prop :=
  et_c_mq_intro vf args_ args m:
    Val.ensure_type_list args_ args (sig_args sg) ->
    et_c_mq sg (cq vf sg args_ m) (cq vf sg args m).

Inductive et_c_mr sg: c_reply -> c_reply -> Prop :=
  et_c_mr_intro res m:
    et_c_mr sg (cr (Val.ensure_type res (proj_sig_res sg)) m) (cr res m).

Program Definition et_c : callconv li_c li_c :=
  {|
    match_senv _ := eq;
    match_query := et_c_mq;
    match_reply := et_c_mr;
  |}.

Lemma et_wt_c R:
  cceqv (et_c @ cc_c R) (wt_c @ cc_c R).
Proof.
  split.
  - intros [[_ sg] wR] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2). cbn in * |-.
    destruct Hqi2. inv Hq1i.
    exists (se1, (se1, sg0), wR). cbn. repeat apply conj; auto.
    + constructor; auto.
    + eexists; split; constructor; cbn; intuition auto.
      * clear - H5. induction H5; cbn; eauto using Val.ensure_has_type.
      * clear - H5 H0. revert args_ H5. generalize (sig_args sg0). clear - H0.
        induction H0; inversion 1; subst; constructor; eauto.
        eapply Val.inject_ensure_type_l; eauto.
    + intros r1 r2 (ri & Hr1i & Hri2). destruct Hr1i.
      exists r1; split; auto. destruct r1 as [res1 m1'].
      erewrite <- (Val.has_type_ensure res1) at 1 by eauto. constructor.
  - intros [[_ [? sg]] wR] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2). cbn in * |-.
    destruct Hq1i. destruct H0. subst.
    eexists (se1, cq_sg q1, wR). cbn. repeat apply conj; auto.
    + destruct q1 as [vf1 sg vargs1 m1]. cbn in *.
      eexists. split; eauto. econstructor.
      revert H1. generalize (sig_args sg). clear.
      induction vargs1, l; inversion 1; try constructor.
      rewrite <- (Val.has_type_ensure a) at 1; eauto. constructor. auto.
    + intros r1 r2 (ri & Hr1i & wR' & HwR' & Hri2).
      destruct Hr1i. inv Hri2. eexists (cr _ _). split.
      * constructor. cbn. apply Val.ensure_has_type.
      * exists wR'. split; auto. constructor; auto.
        eapply Val.inject_ensure_type_l; eauto.
Qed.

Lemma et_et_c:
  cceqv (et_c @ et_c) et_c.
Proof.
Admitted.

(** ** Locset-level typing constraints *)

Inductive et_loc_mq sg: locset_query -> locset_query -> Prop :=
  et_loc_mq_intro vf ls1 ls2 m:
    (forall l, loc_external sg l -> ls1 l = Val.ensure_type (ls2 l) (Loc.type l)) ->
    et_loc_mq sg (lq vf sg ls1 m) (lq vf sg ls2 m).

Inductive et_loc_mr sg: locset_reply -> locset_reply -> Prop :=
  et_loc_mr_intro ls1' ls2' m:
    (forall r, In r (regs_of_rpair (loc_result sg)) ->
               ls1' (R r) = Val.ensure_type (ls2' (R r)) (mreg_type r)) ->
    et_loc_mr sg (lr ls1' m) (lr ls2' m).

Program Definition et_loc :=
  {|
    ccworld := signature;
    match_senv _ := eq;
    match_query := et_loc_mq;
    match_reply := et_loc_mr;
  |}.

Lemma et_wt_loc R:
  cceqv (et_loc @ cc_locset R) (wt_loc @ cc_locset R).
Proof.
  split.
  - intros [[_ xsg] [sg wR]] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
    destruct Hqi2. inv Hq1i.
    exists (se1, (se1, sg), (sg, wR)). cbn. repeat apply conj; auto.
    + constructor; auto.
    + exists (lq vf1 sg ls0 m1). split; constructor; auto.
      * constructor. intros l Hl. rewrite H5 by auto. apply Val.ensure_has_type.
      * intros l Hl. rewrite H5 by auto. apply Val.inject_ensure_type_l. auto.
    + intros r1 r2 (ri & Hr1i & Hri2). destruct Hr1i.
      exists r1; split; auto.
      destruct H3. constructor. intros.
      rewrite Val.has_type_ensure by eauto. reflexivity.
  - intros [[_ [xse xsg]] [sg wR]] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
    destruct Hqi2. inv Hq1i. cbn in H4. inv H4.
    exists (se1, sg, (sg, wR)). cbn. repeat apply conj; auto.
    + exists (lq vf1 sg ls1 m1). split; constructor; auto.
      intros. rewrite Val.has_type_ensure; auto.
    + intros r1 r2 (ri & Hr1i & Hri2). destruct Hr1i.
      eexists; split; auto.
      * constructor. constructor. intros. rewrite H4 by auto. apply Val.ensure_has_type.
      * destruct Hri2 as (wR' & HwR' & Hri2). inv Hri2.
        exists wR'. split; auto. constructor; auto.
        intros l Hl. rewrite H4 by auto.
        apply Val.inject_ensure_type_l. auto.
Qed.

Lemma et_wt_et_loc:
  cceqv et_loc (wt_loc @ et_loc).
Proof.
Admitted.


(** * Commutation properties *)

(** ** Basic setup *)

Class Commutes {liA liB} (cc: callconv liA liB) R1 R2 :=
  commute : ccref (cc @ R2) (R1 @ cc).

Lemma commute_around `{Commutes} {liC} (x : callconv liB liC):
  ccref (cc @ R2 @ x) (R1 @ cc @ x).
Proof.
  rewrite <- !cc_compose_assoc.
  repeat (rstep; auto).
Qed.

Arguments commute_around {liA liB} cc {R1 R2 H liC x}.

Instance commut_join {liA liB} cc R1 R2 S1 S2 :
  @Commutes liA liB cc R1 R2 ->
  @Commutes liA liB cc S1 S2 ->
  Commutes cc (R1 + S1) (R2 + S2).
Proof.
  intros. red.
  rewrite cc_join_distr_l, cc_join_distr_r, !commute.
  reflexivity.
Qed.

Instance commut_star `(Commutes):
  Commutes cc (R1^{*}) (R2^{*}).
Proof.
  red.
  rewrite <- (cc_compose_id_left cc), (cc_id_star R1) at 1.
  apply cc_star_ind_r.
  rewrite cc_compose_assoc, commute, <- cc_compose_assoc.
  rewrite (cc_one_star R1) at 2. rewrite cc_star_idemp.
  reflexivity.
Qed.

Instance commut_compose {liA liB liC} cc1 cc2 RA RB RC:
  @Commutes liA liB cc1 RA RB ->
  @Commutes liB liC cc2 RB RC ->
  Commutes (cc1 @ cc2) RA RC.
Proof.
  intros HAB HBC. red.
  rewrite cc_compose_assoc, commute, <- cc_compose_assoc, commute, cc_compose_assoc.
  reflexivity.
Qed.

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

Instance commut_c_locset R:
  Commutes cc_c_locset (cc_c R) (cc_locset R).
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
  extracting arguments from the memory and then removing them. *)

Lemma match_agree_args R w sg m1 m2 sp1 sp2 ls1 rs2:
  agree_args sg m1 sp1 ls1 ->
  match_mem R w m1 m2 ->
  Val.inject (mi R w) sp1 sp2 ->
  (forall r, Val.inject (mi R w) (ls1 (Locations.R r)) (rs2 r)) ->
  exists ls2,
    agree_args sg m2 sp2 ls2 /\
    (forall r, ls2 (Locations.R r) = rs2 r) /\
    loc_external_rel sg (Val.inject (mi R w)) ls1 ls2.
Proof.
  intros Hargs1 Hm Hsp Hrs.
  exists (make_locset rs2 m2 sp2).
  repeat apply conj.
  - intros ofs ty l Hl. subst l. specialize (Hargs1 ofs ty Hl). clear - Hargs1 Hm Hsp.
    unfold load_stack in Hargs1. transport Hargs1.
    cbn [make_locset]. setoid_rewrite H. reflexivity.
  - auto.
  - intros l Hl. destruct Hl.
    + cbn. auto.
    + specialize (Hargs1 ofs ty H). clear - Hargs1 Hm Hsp.
      unfold load_stack in Hargs1. transport Hargs1.
      cbn [make_locset]. setoid_rewrite H. cbn. auto.
Qed.

Instance cklr_free_args R:
  Monotonic free_args
    (|= - ==> match_mem R ++> Val.inject @@ [mi R] ++> k1 option_le (<> match_mem R)).
Proof.
  intros w sg m1 m2 Hm sp1 sp2 Hsp.
Admitted. (* need to update *)
(*
  destruct (free_args sg m1 sp1) as [m1_ | ] eqn:H1; [ | constructor].
  unfold free_args in H1. destruct sp1 as [ | | | | | sb1 sofs1]; try discriminate.
  cut (exists w' m2_, w ~> w' /\ free_args sg m2 sp2 = Some m2_ /\ match_mem R w' m1_ m2_).
  - intros (? & ? & ? & ? & ?). rewrite H0. rauto.
  - revert m1 m2 Hm m1_ H1. inv Hsp. cbn [free_args].
    induction regs_of_rpairs.
    + cbn. intros. inv H0. exists w, m2. split; auto. reflexivity.
    + destruct a as [
Qed.
*)

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

Instance commut_locset_mach R:
  Commutes cc_locset_mach (cc_locset R) (cc_mach R).
Proof.
  intros [[_ [sg ls1]] wR] se1 se2 q1 q2 [[ ] Hse2] (qi & Hq1i & Hqi2).
  cbn in * |- . destruct Hqi2. inv Hq1i. rename m' into m1_. rename ls into ls1.

  (** Synthesizing the query *)
  transport H11. rename x into m2_.
  edestruct match_agree_args as (ls2 & Hargs2 & Hrs2 & Hls); eauto.
  { intro r. rewrite H12. eauto. }
  set (ls2wt l := Val.ensure_type (ls2 l) (Loc.type l)).

  exists (se2, (sg, wR'), (sg, rs2)). repeat apply conj.
  - cbn. split; rauto.
  - exists (lq vf2 sg ls2 m2_). split.
    + econstructor; try rauto.
      * admit. (* vf1 <> Vundef -- add in upper conventions or move back to [fb] *)
    + constructor; eauto.
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
      destruct in_dec. { rewrite H15; auto. }
      destruct is_callee_save eqn:Hr; auto.
      rewrite H11 by auto. rewrite H12. generalize (H2 r).
      repeat rstep. change (wR ~> wR''). rauto.
Admitted.

(** ** [cc_mach_asm] *)

Instance commut_mach_asm R:
  Commutes cc_mach_asm (cc_mach R) (cc_asm R).
Proof.
  intros [[_ [rs1 nb1]] wR] se1 se2 q1 q2 [[ ] Hse2] (qi & Hq1i & Hqi2).
  cbn in * |- . destruct Hq1i. destruct q2 as [rs2 m2], Hqi2 as [Hrs Hm]. rename m into m1.
  exists (se2, wR, (rs2, Mem.nextblock m2)). cbn. repeat apply conj; auto.
  - exists (mq rs2#PC rs2#SP rs2#RA (fun r => rs2 (preg_of r)) m2). split.
    + constructor; auto.
    + constructor.
      * specialize (Hrs SP). destruct Hrs; inv H. constructor.
        revert H4.
        change (b1 < _)%positive with (Mem.valid_block m1 b1).
        change (b2 < _)%positive with (Mem.valid_block m2 b2).
        rstep. rstep. rstep. rstep. red. eauto.
      * specialize (Hrs RA). destruct Hrs; congruence.
  - intros r1 r2 (ri & (wR' & HwR' & Hr1i) & Hri2).
    admit. (* need to synthesize return val -- just a question of preg vs. mreg *)
Admitted.

(** ** [et_c] *)

Instance commut_et_c (R : cklr):
  Commutes et_c R R.
Proof.
  intros [[_ w] wR] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
  destruct Hqi2. inv Hq1i.
  exists (se2, wR, sg). repeat apply conj.
  + constructor; cbn; auto.
  + edestruct Val.ensure_type_list_inject as (vargs2_ & Hvargs_ & Hvargs2_); eauto.
    exists (cq vf2 sg vargs2_ m2); split; constructor; auto.
  + intros r1 r2 (ri & (wR' & HwR' & Hr1i) & Hri2).
    destruct Hr1i. inv Hri2.
    exists (cr vres1 m1'). split.
    * rewrite <- (Val.has_type_ensure vres1) at 1; [ constructor | ].
      eapply val_has_type_inject; eauto.
      apply Val.ensure_has_type.
    * exists wR'. split; auto. constructor; auto.
      eapply Val.inject_ensure_type_r; eauto.
Qed.

(** Other option *)

Lemma star_inv_prop {li} (R : callconv li li) (I : invariant li) :
  PropagatesReplyInvariant 1 I ->
  PropagatesQueryInvariant R I ->
  PropagatesReplyInvariant R I ->
  cceqv ((R + I)^{*} @ I) (R^{*} @ I).
Proof.
  split.
  - rewrite (proj2 (cc_compose_id_left I)) at 2.
    rewrite (cc_id_star R).
    apply cc_star_ind_l.
    rewrite cc_join_distr_l.
    apply cc_join_lub.
    + rewrite (cc_one_star R) at 1.
      rewrite <- cc_compose_assoc, cc_star_idemp.
      reflexivity.
    + apply (inv_drop _ _).
  - repeat rstep. apply cc_join_ub_l.
Qed.

(** ** [loc_et] *)

Instance commut_et_loc R:
  Commutes et_loc (cc_locset R) (cc_locset R).
Proof.
  red.
  intros [[_ xsg] [sg wR]] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
  destruct Hqi2. inv Hq1i.
  exists (se2, (sg, wR), sg). repeat apply conj; cbn; eauto.
  - set (ls2_ l := Val.ensure_type (ls2 l) (Loc.type l)).
    exists (lq vf2 sg ls2_ m2). split; constructor; auto.
    intros l Hl. rewrite H5; auto. apply Val.ensure_type_inject; auto.
  - intros r1 r2 (ri & (wR' & HwR' & Hr1i) & Hri2).
    destruct Hr1i. inv Hri2.
    exists (lr ls1' m1'). split.
    + constructor; auto. intros r Hr.
      rewrite Val.has_type_ensure; auto.
      eapply val_has_type_inject. red. eauto.
      rewrite H9 by auto.
      apply Val.ensure_has_type.
    + exists wR'. split; auto.
      constructor; auto.
      intros r Hr. eapply Val.inject_ensure_type_r. rewrite <- H9; eauto.
Qed.
