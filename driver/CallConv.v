(** This file defines the overall calling convention for CompCertO
  and provides the simulation convention algebra used in the
  [driver.Compiler] library to compose passes into the corresponding
  correctness theorem.

  The main principle before our approach is to separate the structural
  aspect of calling conventions on one hand, which establish
  connections between the successive language interfaces, and the
  CKLRs used by various passes on the other hand, which can be
  promoted to endogenous simulation conventions for each language
  interface. Although composing the various pass correctness theorems
  directly yields a mixture of stuctural conventions and CKLRs, we use
  commutation properties to separate these two components.

  More precisely, for a structural component [CC], we make sure that
  the following holds for all CKLRs [R]:

                    ccref (CC @ R) (R @ CC)

  In the context of external calls, this allows us to propagate CKLRs
  towards the source level, where they can be satisfied by the
  relational parametricity property of Clight. For incoming calls,
  this allows a target-level injection to be duplicated and propagated
  in order to satisfy the incoming simulation convention of the
  various compiler passes. Ultimately, we can formulate a simulation
  convention for the whole compiler of the form:

         (R1 + ... + Rn)^{*} @ (CC1 @ ... @ CCk) @ vainj

  The first component expresses source-level compatibility with the
  various CKLRs [R1], ..., [Rn] (and hence, thanks to commutation
  properties, overall compatibility with CKLRs for incoming calls).
  The second component encodes the structural aspects of the
  relationship between source- and target-level calls. The last
  component represents a minimal CKLR: a memory injection is necessary
  since the target program will allocate stack frames instead of
  individual memory blocks for local variable, and queries must
  contain memory states which conform to the invariants used by the
  ValueAnalysis passes. *)

Require Import LanguageInterface CallconvAlgebra Invariant.
Require Import CKLR Inject InjectFootprint Extends VAInject VAExtends.
Require Import Mach Locations Conventions Asm.
Require Import ValueAnalysis.
Require Import Allocproof Lineartyping Asmgenproof0.
Require Import Maps Stacklayout.
Unset Program Cases.

Coercion cc_c : cklr >-> callconv.


(** * Commutation properties *)

(** First, we define a general form for the commutation properties we
  need, and prove the straightforward ones. *)

(** ** Basic setup *)

(** The following class captures a general commutation property.
  In general, [cc] will be a structural simulation convention;
  [R1] and [R2] will be corresponding source- and target-level CKLR
  simulation conventions. *)

Class Commutes {liA liB} (cc: callconv liA liB) R1 R2 :=
  commute : ccref (cc @ R2) (R1 @ cc).

(** The following lemma provides a convenient way to use [commute] for
  rewriting within more complex sequences of simulation conventions. *)

Lemma commute_around `{Commutes} {liC} (x : callconv liB liC):
  ccref (cc @ R2 @ x) (R1 @ cc @ x).
Proof.
  rewrite <- !cc_compose_assoc.
  repeat (rstep; auto).
Qed.

Arguments commute_around {liA liB} cc {R1 R2 H liC x}.

(** Finally, we provide some composite instances for [Commutes]. *)

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
  original LTL semantics evaluates calls to external functions:
  for queries, we read out the arguments from the location set;
  once we get a C reply, we write back the
  result and mark the appropriate registers undefined. *)

Lemma locmap_getpair_inject f ls1 ls2 p:
  forall_rpair (fun l => Val.inject f (ls1 l) (ls2 l)) p ->
  Val.inject f (Locmap.getpair p ls1) (Locmap.getpair p ls2).
Proof.
  destruct p; cbn; intuition auto.
  apply Val.longofwords_inject; auto.
Qed.

(** For now we restrict ourselves to 64-bit x86, where no register
  pairs are involved. Eventually we'll want to fold register typing
  into the property below (or maybe the calling conventions
  themselves) to ensure that split integers are the right sizes. *)

Lemma loc_arguments_always_one sg p:
  In p (loc_arguments sg) ->
  exists l, p = One l.
Proof.
  cut (forall x y z, In p (loc_arguments_64 (sig_args sg) x y z) -> exists l, p = One l).
  - intros. apply (H 0 0 0). apply H0.
  - induction sig_args; cbn -[list_nth_z].
    + tauto.
    + intros x y z.
      destruct a, list_nth_z; cbn; intros [? | ?]; eauto.
Qed.

Lemma loc_result_always_one sg:
  exists r, loc_result sg = One r.
Proof.
  change loc_result with loc_result_64. unfold loc_result_64.
  destruct sig_res as [[ ] | ]; eauto.
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
        destruct (loc_result_always_one sg) as [r ->].
        cbn. rewrite Locmap.gss. reflexivity.
    + eexists; split; eauto.
      constructor; auto. subst ls1'. red.
      destruct (loc_result_always_one sg) as [r Hr]. rewrite Hr in *. cbn in *.
      intuition subst. rewrite Locmap.gss. auto.
Qed.

(** ** [cc_mach_asm] *)

(** The commutation property for [cc_mach_asm] is straightforward. *)

Instance commut_mach_asm R:
  Commutes cc_mach_asm (cc_mach R) (cc_asm R).
Proof.
  intros [[_ [rs1 nb1]] wR] se1 se2 q1 q2 [[ ] Hse2] (qi & Hq1i & Hqi2).
  cbn in * |- . destruct Hq1i. destruct q2 as [rs2 m2], Hqi2 as (Hrs & Hpc & Hm).
  rename m into m1.
  exists (se2, wR, (rs2, Mem.nextblock m2)). cbn. repeat apply conj; auto.
  - exists (mq rs2#PC rs2#SP rs2#RA (fun r => rs2 (preg_of r)) m2). split.
    + constructor; auto.
      * destruct H0; congruence.
      * setoid_rewrite H2. eauto.
    + constructor; auto.
      * destruct (Hrs PC); cbn in *; congruence.
      * specialize (Hrs SP). destruct Hrs; inv H0. constructor.
        revert H6.
        change (b1 < _)%positive with (Mem.valid_block m1 b1).
        change (b2 < _)%positive with (Mem.valid_block m2 b2).
        rstep. rstep. rstep. rstep. red. eauto.
      * specialize (Hrs RA). destruct Hrs; congruence.
  - intros r1 r2 (ri & (wR' & HwR' & Hr1i) & Hri2).
    admit. (* need to synthesize return val -- just a question of preg vs. mreg *)
Admitted.


(** * Typing invariants *)

(** On their own, the typing invariants [wt_c] and [wt_loc] do not
  commute with CKLRs. This is because a source value may be [Vundef],
  hence well-typed, even when the target value is defined but ill-typed.
  However, we can recover a sufficient commutation property by
  introducing some slack as [wt @ lessdef], where [lessdef] is a
  simulation convention allowing values to be refined. Then we can use
  [Val.ensure_type] to make sure that the intermediate values are
  well-typed. *)

(** ** Helper lemmas *)

Lemma val_lessdef_inject_list_compose f vs_ vs1 vs2:
  Val.lessdef_list vs_ vs1 ->
  Val.inject_list f vs1 vs2 ->
  Val.inject_list f vs_ vs2.
Proof.
  intros Hvs_ Hvs. revert vs2 Hvs.
  induction Hvs_.
  - inversion 1; constructor.
  - inversion 1; subst; constructor; eauto.
    eapply Mem.val_lessdef_inject_compose; eauto.
Qed.

Lemma has_type_inject f v1 v2 t:
  Val.has_type v1 t ->
  Val.inject f v1 v2 ->
  Val.inject f v1 (Val.ensure_type v2 t).
Proof.
  intros.
  rewrite <- (Val.has_type_ensure v1 t) by auto.
  apply Val.ensure_type_inject; auto.
Qed.

Lemma has_type_inject_list f vl1 vl2 tl:
  Val.has_type_list vl1 tl ->
  Val.inject_list f vl1 vl2 ->
  exists vl2',
    Val.has_type_list vl2' tl /\
    Val.inject_list f vl1 vl2' /\
    Val.lessdef_list vl2' vl2.
Proof.
  intros Htl Hv. revert tl Htl.
  induction Hv; cbn in *.
  - destruct tl; try contradiction. intros _.
    exists nil. repeat constructor.
  - destruct tl as [ | t tl]; try contradiction. intros [Ht Htl].
    edestruct IHHv as (vl2' & Hvl2' & Hvl & Hvl2); eauto.
    exists (Val.ensure_type v' t :: vl2'). repeat (constructor; auto).
    + apply Val.ensure_has_type.
    + apply has_type_inject; auto.
    + destruct v', t; auto.
Qed.

(** ** C-level typing constraints *)

Inductive lessdef_c_mq: c_query -> c_query -> Prop :=
  lessdef_c_mq_intro vf sg args_ args m:
    Val.lessdef_list args_ args ->
    lessdef_c_mq (cq vf sg args_ m) (cq vf sg args m).

Inductive lessdef_c_mr: c_reply -> c_reply -> Prop :=
  lessdef_c_mr_intro res_ res m:
    Val.lessdef res_ res ->
    lessdef_c_mr (cr res_ m) (cr res m).

Program Definition lessdef_c : callconv li_c li_c :=
  {|
    ccworld := unit;
    match_senv _ := eq;
    match_query _ := lessdef_c_mq;
    match_reply _ := lessdef_c_mr;
  |}.

Lemma lessdef_c_cklr R:
  cceqv (lessdef_c @ cc_c R) (cc_c R).
Proof.
  split.
  - intros [[_ [ ]] wR] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2). cbn in * |-.
    destruct Hqi2. inv Hq1i.
    eexists wR. cbn. repeat apply conj; auto.
    + constructor; auto. clear - H0 H5.
      eapply val_lessdef_inject_list_compose; eauto.
    + intros r1 r2 Hr. exists r1; split; auto.
      destruct r1; constructor; auto.
  - intros wR se1 se2 q1 q2 Hse Hq.
    exists (se1, tt, wR). repeat apply conj; cbn; eauto.
    + exists q1. split; auto. destruct q1. constructor; auto.
      clear. induction cq_args; constructor; auto.
    + intros r1 r2 (ri & Hr1i & wR' & HwR' & Hri2).
      exists wR'. split; auto. destruct Hri2; inv Hr1i; constructor; auto.
      eapply Mem.val_lessdef_inject_compose; eauto.
Qed.

Instance commut_wt_c (R : cklr):
  Commutes (wt_c @ lessdef_c) R R.
Proof.
  red. rewrite cc_compose_assoc. rewrite lessdef_c_cklr.
  intros [[_ [ ]] wR] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
  destruct Hqi2. inv Hq1i. inv H4. cbn [cq_sg cq_args] in *.
  eexists (se2, wR, (se2, (se2, sg), tt)). repeat apply conj; cbn.
  + repeat constructor; cbn; auto.
  + edestruct has_type_inject_list as (vl2 & Hvl2 & Hvl & Hvl'); eauto.
    exists (cq vf2 sg vl2 m2). split.
    * constructor; eauto.
    * eexists. split; constructor; cbn; eauto.
  + intros r1 r2 (ri & (wR' & HwR' & Hr1i) & rj & Hrij & Hrj2).
    destruct Hr1i. inv Hrij. inv Hrj2. cbn in *.
    eexists; split.
    * constructor. cbn. eapply val_has_type_inject; eauto.
    * exists wR'. split; auto. constructor; eauto.
      eapply Mem.val_inject_lessdef_compose; eauto.
Qed.

(** ** Locset-level typing constraints *)

Inductive lessdef_loc_mq sg: locset_query -> locset_query -> Prop :=
  lessdef_loc_mq_intro vf ls1 ls2 m:
    loc_external_rel sg Val.lessdef ls1 ls2 ->
    lessdef_loc_mq sg (lq vf sg ls1 m) (lq vf sg ls2 m).

Inductive lessdef_loc_mr sg: locset_reply -> locset_reply -> Prop :=
  lessdef_loc_mr_intro ls1' ls2' m:
    loc_result_rel sg Val.lessdef ls1' ls2' ->
    lessdef_loc_mr sg (lr ls1' m) (lr ls2' m).

Program Definition lessdef_loc :=
  {|
    match_senv _ := eq;
    match_query := lessdef_loc_mq;
    match_reply := lessdef_loc_mr;
  |}.

Lemma lessdef_loc_cklr R:
  cceqv (lessdef_loc @ cc_locset R) (cc_locset R).
Proof.
  split.
  - intros [[_ xsg] [sg wR]] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
    destruct Hqi2. inv Hq1i.
    exists (sg, wR). cbn. repeat apply conj; auto.
    + constructor; auto. intros l Hl.
      eapply Mem.val_lessdef_inject_compose; auto.
    + intros r1 r2 Hr. exists r1. split; auto.
      destruct r1. constructor. intros l Hl. auto.
  - intros [sg wR] se1 se2 q1 q2 Hse Hq. inv Hq.
    exists (se1, sg, (sg, wR)). repeat apply conj; cbn; auto.
    + eexists. split; constructor; eauto. intros l Hl. auto.
    + intros r1 r2 (ri & Hr1i & wR' & HwR' & Hri2). exists wR'. split; auto.
      destruct Hri2. inv Hr1i. constructor; auto.
      intros l Hl. eapply Mem.val_lessdef_inject_compose; auto.
Qed.

Instance commut_wt_loc R:
  Commutes (wt_loc @ lessdef_loc) (cc_locset R) (cc_locset R).
Proof.
  red. rewrite cc_compose_assoc, lessdef_loc_cklr.
  intros [[_ [xse xsg]] [sg wR]] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
  destruct Hqi2. inv Hq1i. inv H. inv H4.
  exists (se2, (sg, wR), (se2, (se2, sg), sg)). cbn. repeat apply conj; eauto.
  - constructor; auto.
  - set (ls2_ l := Val.ensure_type (ls2 l) (Loc.type l)).
    exists (lq vf2 sg ls2_ m2). split.
    + constructor; auto. intros l Hl. apply has_type_inject; auto.
    + eexists. split; constructor.
      * constructor. intros. apply Val.ensure_has_type.
      * intros l Hl. subst ls2_; cbn. destruct (ls2 l), Loc.type; cbn; auto.
  - intros r1 r2 (ri & (wR' & HwR' & Hr1i) & rj & Hrij & Hrj2).
    destruct Hr1i. inv Hrij. inv Hrj2. inv H6.
    exists (lr ls1' m1'). split.
    + constructor. constructor. intros r Hr.
      eapply val_has_type_inject; eauto. red. eauto.
    + exists wR'. split; auto. constructor; auto.
      intros r Hr. eapply Mem.val_inject_lessdef_compose; auto.
Qed.

(** ** Another option for [wt_c] *)

(** An alternative approach for [wt_c] would be to formulate a typing
  constraint on the target queries and replies, which can be
  propagated towards the source as [ccref (cc @ wt) (wt @ cc @
  wt)]. Then we can use the following property to make it part of the
  source-level compatibility relations to satisfy the typing
  requirements of other components' external calls. *)

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


(** * Stacking *)

(** The simulation conventions for most passes are simple enough that
  we can express them directly as [R @ CC], where [R] is a CKLR
  matching the memory relation used in the simulation proof, and
  [CC] expresses the structural correspondance between source- and
  target-level queries and replies. However, the Stacking pass
  involves fairly complex invariants and it is simpler to formulate
  the corresponding simulation convention as a monolithic one, closely
  coupled with the corresponding simulation proof.

  In the following we show that this simulation convention can then be
  decoupled into a CKLR and a structural convention. This form is then
  used as the outside interface for the pass and integrated to the
  strategy outlined above. *)

Require Import Classical.

(** ** Structural convention *)

(** The first step is to define the structural convention we will be
  using between [li_locset] and [li_mach]. *)

(** *** Dealing with the arguments region *)

(** One key aspect of this convention is the encoding of arguments: at
  the source level, arguments for the call are stored in abstract
  locations, which become either registers or in-memory stack slots at
  the target level. Crucially, these stack slots must not be
  accessible as memory locations in the source program, otherwise the
  invariant relating abstract and concrete stack locations may be
  broken through aliasing. Hence, in the structural convention the
  source memory cannot be *equal* to the target memory, but instead
  must be a version of the target memory where permissions on the
  arguments region of the stack have been removed.

  For queries, this can be expressed using [Mem.free]. We also deal
  separately with the case where no arguments are stored in the stack.
  This is both to ensure the compatibility of [args_removed] with
  injection, and to allow [Vnullptr] as a possible stack pointer for
  the initial call to [main()]. *)

Inductive args_removed sg: val -> mem -> mem -> Prop :=
  | args_removed_tailcall_possible sp m:
      tailcall_possible sg ->
      args_removed sg sp m m
  | args_removed_free sb sofs m m_:
      Mem.free m sb (offset_sarg sofs 0) (offset_sarg sofs (size_arguments sg)) = Some m_ ->
      (forall ofs, 0 <= ofs < size_arguments sg -> offset_fits sofs ofs) ->
      size_arguments sg > 0 ->
      (forall ofs ty,
        In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
        exists v, load_stack m (Vptr sb sofs) ty (Ptrofs.repr (fe_ofs_arg + 4 * ofs)) = Some v) ->
      args_removed sg (Vptr sb sofs) m m_.

(** This takes care of how the LTL memory state is obtained from the
  Mach-level one. In addition, the following construction reconstructs
  the LTL-level [locset] from the Mach-level [regset] by reading the
  additional stack locations from the Mach memory. *)

Definition make_locset (rs: Mach.regset) (m: mem) (sp: val) (l: loc) : val :=
  match l with
    | R r => rs r
    | S Outgoing ofs ty =>
      let v := load_stack m sp ty (Ptrofs.repr (fe_ofs_arg + 4 * ofs)) in
      Val.maketotal v
    | _ => Vundef
  end.

(** For replies, in some simulation convention refinement properties
  we want to establish, the source memory state is often given to us
  and we have to establish the relationship. This means we can't use
  [Mem.free] in the same way; fortunately, it is enough to give a more
  extensional characterization in terms of [Mem.unchanged] involving
  the following address predicate. *)

Definition not_init_args (sz: Z) (sp: val) :=
  fun b ofs => ~ loc_init_args sz sp b ofs.

(** *** Definition *)

(** We can now define the structural convention
  from [li_locset] to [li_mach]. *)

Record cc_lm_world :=
  lmw {
    lmw_sg : signature;
    lmw_rs : Mach.regset;
    lmw_m : mem;
    lmw_sp : val;
  }.

Inductive cc_locset_mach_mq: cc_lm_world -> locset_query -> mach_query -> Prop :=
  cc_locset_mach_mq_intro sg vf m_ rs sp ra m:
    args_removed sg sp m m_ ->
    Val.has_type ra Tptr ->
    cc_locset_mach_mq
      (lmw sg rs m sp)
      (lq vf sg (make_locset rs m sp) m_)
      (mq vf sp ra rs m).

Inductive cc_locset_mach_mr: cc_lm_world -> locset_reply -> mach_reply -> Prop :=
  cc_locset_mach_mr_intro sg rs ls' m'_ sp m rs' m':
    (forall r, In r (regs_of_rpair (loc_result sg)) -> rs' r = ls' (R r)) ->
    (forall r, is_callee_save r = true -> rs' r = rs r) ->
    Mem.unchanged_on (not_init_args (size_arguments sg) sp) m'_ m' ->
    Mem.unchanged_on (loc_init_args (size_arguments sg) sp) m m' ->
    cc_locset_mach_mr (lmw sg rs m sp) (lr ls' m'_) (mr rs' m').

Program Definition cc_locset_mach: callconv li_locset li_mach :=
  {|
    match_senv _ := eq;
    match_query := cc_locset_mach_mq;
    match_reply := cc_locset_mach_mr;
  |}.

(** ** Commutation property *)

(** For queries, we need to synthesizing the target-level locset by
  extracting arguments from the memory and then removing them. *)

Lemma offset_sarg_inject R w m1 m2 sb1 sofs1 sb2 sofs2 ofs:
  match_mem R w m1 m2 ->
  Mem.perm m1 sb1 (offset_sarg sofs1 0) Cur Freeable ->
  ptrbits_inject (mi R w) (sb1, sofs1) (sb2, sofs2) ->
  ptr_inject (mi R w) (sb1, offset_sarg sofs1 ofs) (sb2, offset_sarg sofs2 ofs).
Proof.
  intros Hm Hp Hsp. inv Hsp.
  unfold offset_sarg in *. rewrite Z.add_0_r in Hp.
  apply ptr_inject_shift.
  eapply ptrbits_ptr_inject; eauto.
  rewrite Ptrofs.add_assoc, (Ptrofs.add_commut (Ptrofs.repr _)), <- Ptrofs.add_assoc.
  constructor; auto.
Qed.

Lemma offset_sarg_expand ofs sofs:
  offset_sarg sofs ofs = offset_sarg sofs 0 + 4 * ofs.
Proof.
  unfold offset_sarg. xomega.
Qed.

Lemma offset_sarg_ptrrange_inject R w m1 m2 sb1 sofs1 sb2 sofs2 ofs:
  match_mem R w m1 m2 ->
  Mem.perm m1 sb1 (offset_sarg sofs1 0) Cur Freeable ->
  ptrbits_inject (mi R w) (sb1, sofs1) (sb2, sofs2) ->
  ptrrange_inject (mi R w)
    (sb1, offset_sarg sofs1 0, offset_sarg sofs1 ofs)
    (sb2, offset_sarg sofs2 0, offset_sarg sofs2 ofs).
Proof.
  intros. rewrite !(offset_sarg_expand ofs).
  rstep. eapply offset_sarg_inject; eauto.
Qed.

Lemma offset_fits_inject R w m1 m2 sb1 sb2 delta sofs1 sofs2 ofs sz:
  match_mem R w m1 m2 ->
  Mem.range_perm m1 sb1 (offset_sarg sofs1 0) (offset_sarg sofs1 sz) Cur Freeable ->
  0 <= ofs < sz ->
  mi R w sb1 = Some (sb2, delta) ->
  sofs2 = Ptrofs.add sofs1 (Ptrofs.repr delta) ->
  offset_fits sofs1 ofs ->
  offset_fits sofs2 ofs.
Proof.
  intros Hm PERM Hofs Hsb Hsofs2 FITS.
  unfold offset_fits, offset_sarg in *. subst sofs2.
  rewrite !(Ptrofs.add_commut sofs1).
  rewrite !(Ptrofs.add_assoc (Ptrofs.repr delta)).
  rewrite !(Ptrofs.add_commut (Ptrofs.repr delta)).
  erewrite cklr_address_inject; eauto.
  rewrite <- (Z.add_assoc _ delta), (Z.add_comm delta), Z.add_assoc.
  setoid_rewrite FITS.
  erewrite <- cklr_address_inject; eauto.
  * eapply PERM. xomega.
  * eapply PERM. xomega.
Qed.

Instance load_stack_inject R:
  Monotonic load_stack
    (|= match_mem R ++> Val.inject @@ [mi R] ++> - ==> - ==>
        k1 option_le (Val.inject @@ [mi R])).
Proof.
  unfold load_stack. rauto.
Qed.

Instance args_removed_cklr R:
  Monotonic args_removed
    (|= - ==> Val.inject @@ [mi R] ++> match_mem R ++> k1 set_le (<> match_mem R)).
Proof.
  intros w sg sp1 sp2 Hsp m1 m2 Hm m1_ Hm1_.
  destruct Hm1_ as [sp m1 | sb1 sofs1 m1 m1_ FREE FITS].
  - exists m2. split; [ | rauto].
    constructor; auto.
  - inversion Hsp. subst.
    set (sofs2 := Ptrofs.add _ _).
    assert (forall ofs,
      ptr_inject (mi R w) (sb1, offset_sarg sofs1 ofs) (b2, offset_sarg sofs2 ofs)).
    {
      intro. eapply offset_sarg_inject; eauto.
      + eapply Mem.free_range_perm; eauto. unfold offset_sarg. xomega.
      + constructor; auto.
    }
    assert
        (ptrrange_inject (mi R w)
                        (sb1, offset_sarg sofs1 0, offset_sarg sofs1 (size_arguments sg))
                        (b2, offset_sarg sofs2 0, offset_sarg sofs2 (size_arguments sg))).
    {
      eapply ptr_ptrrange_inject; split; eauto.
      unfold offset_sarg. xomega.
    }
    generalize FREE. transport FREE. intros FREE.
    eexists; split.
    + eapply args_removed_free; eauto.
      * clear - Hm FITS H3 FREE.
        intros ofs Hofs. eapply offset_fits_inject; eauto.
        -- eapply Mem.free_range_perm; eauto.
        -- reflexivity.
      * intros ofs ty REG. edestruct H0 as [v Hv]; eauto.
        transport Hv. eauto.
    + rauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @args_removed : typeclass_instances.

(** For replies, the challenge is to construct a version of the source
  memory state which contains the original arguments, and a version of
  the source [Mach.regset] which contains the right mixture of
  original callee-save registers and results from the reply's
  locset. The following lemmas will help. *)

Lemma result_mem R sz sp1 sp2 w m1 m2 w' m1'_ m2'_ m2':
  w ~> w' ->
  Val.inject (mi R w) sp1 sp2 ->
  match_mem R w m1 m2 ->
  match_mem R w' m1'_ m2'_ ->
  Mem.unchanged_on (loc_init_args sz sp2) m2 m2' ->
  Mem.unchanged_on (not_init_args sz sp2) m2'_ m2' ->
  exists m1',
    match_mem R w' m1' m2' /\
    Mem.unchanged_on (loc_init_args sz sp1) m1 m1' /\
    Mem.unchanged_on (not_init_args sz sp1) m1'_ m1'.
Proof.
  (** To achieve this, we will need to define a new [Mem.mix]
    operation of the memory model, corresponding injection and
    extension preservation properties, and add similar conditions to
    the definition of CKLRs. *)
Admitted.

Instance make_locset_cklr R:
  Monotonic make_locset
    (|= (- ==> Val.inject @@ [mi R]) ++> match_mem R ++> Val.inject @@ [mi R] ++>
        (- ==> Val.inject @@ [mi R])).
Proof.
  intros w rs1 rs2 Hrs m1 m2 Hm sp1 sp2 Hsp l.
  unfold make_locset, load_stack. rauto.
Qed.

(** With this, we can state and prove the commutation property. *)

Instance commut_locset_mach R:
  Commutes cc_locset_mach (cc_locset R) (cc_mach R).
Proof.
  intros [[_ w] wR] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
  destruct Hqi2. inv Hq1i. set (ls2 := make_locset rs2 m2 sp2).
  transport H11.
  eexists (se2, (sg, wR'), lmw sg rs2 m2 _). cbn. repeat apply conj; auto.
  - eapply match_stbls_acc; eauto.
  - exists (lq vf2 sg ls2 x). split.
    + constructor; auto; try rauto.
      * intros l Hl. unfold ls2. rewrite <- HwR'. repeat rstep; auto.
    + constructor; auto.
      * destruct H4; congruence.
  - intros r1 r2 (ri & (wR'' & HwR'' & Hr1i) & Hri2).
    destruct Hr1i. inv Hri2. rename rs' into rs2'.
    set (rs1' r := result_regs sg (make_locset rs1 m1 sp1) ls1' (Locations.R r)).
    edestruct (result_mem R (size_arguments sg) sp1 sp2 wR m1 m2 wR'' m1' m2')
      as (m1'' & Hm'' & ? & ?); eauto. etransitivity; eauto.
    exists (mr rs1' m1''). split.
    + constructor; auto.
      * intros r Hr. unfold rs1'. cbn. destruct in_dec; tauto.
      * intros r Hr. unfold rs1'. rewrite <- result_regs_agree_callee_save; auto.
    + exists wR''. split; [rauto | ]. constructor; auto.
      intro r. unfold rs1', result_regs.
      destruct in_dec. { rewrite H19; auto. }
      destruct is_callee_save eqn:Hr; auto.
      rewrite H20 by auto. cbn. generalize (H5 r).
      repeat rstep. change (wR ~> wR''). etransitivity; eauto.
Qed.

(** ** Matching [cc_stacking] *)

(** Next, we show that [cc_stacking] can be reduced to simulation
  conventions involving [cc_locset_mach]. *)

(** *** Incoming calls *)

Lemma cc_lm_stacking:
  ccref (cc_locset_mach @ cc_mach inj) (cc_stacking inj).
Proof.
  intros [[_ wlm] w] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2). cbn in *.
  destruct Hqi2. inv Hq1i.
  exists (stkw inj w sg (make_locset rs1 m1 sp1) sp2 m2).
  split; [ | split].
  - cbn. auto.
  - constructor; auto.
    + cbn -[Z.add Z.mul]. repeat apply conj.
      * apply Mem.unchanged_on_refl.
      * intros. subst. split.
        -- destruct H11.
           ++ apply zero_size_arguments_tailcall_possible in H7.
              rewrite H7. red. intros. xomega.
           ++ inversion H2. subst.
              eapply transport in H7 as (m2_ & Hm2_ & Hm_).
              2: {
                change ?x with (id x) in H7. repeat rstep.
                eapply offset_sarg_ptrrange_inject; eauto.
                eapply Mem.free_range_perm; eauto.
                rewrite (offset_sarg_expand (size_arguments sg)).
                xomega.
              }
              eapply Mem.free_range_perm; eauto.
        -- intros ofs Hofs. destruct H11.
           ++ apply zero_size_arguments_tailcall_possible in H7.
              rewrite H7 in Hofs. xomega.
           ++ inv H2. eapply offset_fits_inject; eauto.
              eapply Mem.free_range_perm; eauto.
      * intros ofs ty REG. destruct H11.
        -- apply tailcall_possible_reg in REG; auto. contradiction.
        -- edestruct H10 as [v Hv]; eauto. rewrite Hv.
           transport Hv. rewrite H11. eauto.
    + destruct H11 as [ | sb1 sofs1 m1 m1_ ]; auto.
      assert (Mem.extends m1_ m1) by eauto using Mem.free_left_extends, Mem.extends_refl.
      destruct H6; cbn in *. erewrite <- Mem.mext_next by eauto. constructor.
      eapply Mem.extends_inject_compose; eauto.
    + destruct 1. intros b1 delta Hb1 Hp.
      eapply Mem.perm_free_2; eauto.
      admit. admit. (* things about injection overlap -- should be okay *)
    + admit. (* type of sp *)
    + destruct H4; cbn in *; congruence.
  - intros r1 r2 Hr. inv Hr.
    edestruct (result_mem inj (size_arguments sg) sp1 sp2 w m1 m2 w' m1' m2' m2')
      as (m1'' & ? & ? & ?); eauto using Mem.unchanged_on_refl.
    set (rs1' r := if is_callee_save r then rs1 r else
                   if in_dec mreg_eq r (regs_of_rpair (loc_result sg)) then ls1' (R r) else
                   Vundef).
    exists (mr rs1' m1''). split.
    + constructor; auto.
      * subst rs1'. intros r REG. cbn.
        destruct in_dec; try contradiction.
        replace (is_callee_save r) with false; auto.
        pose proof (loc_result_caller_save sg) as Hr.
        destruct loc_result; cbn in *; intuition congruence.
      * subst rs1'. intros r REG. cbn.
        rewrite REG. congruence.
    + exists w'; split; auto.
      constructor; auto.
      * intros r. subst rs1'. cbn.
        destruct is_callee_save eqn:CSR; eauto.
        destruct in_dec; eauto.
Admitted.

(** *** Outgoing calls *)

Import Separation.

Lemma inject_incr_separated_inv f f' m1 m2 b1 b2 delta:
  inject_incr f f' ->
  inject_separated f f' m1 m2 ->
  f' b1 = Some (b2, delta) ->
  (Mem.valid_block m1 b1 \/ Mem.valid_block m2 b2) ->
  f b1 = Some (b2, delta).
Proof.
  intros INCR ISEP Hb VALID.
  destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb1.
  - apply INCR in Hb1. congruence.
  - eelim ISEP; eauto. tauto.
Qed.

Lemma unchanged_on_combine P Q m m' :
  Mem.unchanged_on P m m' ->
  Mem.unchanged_on (fun b ofs => Q b ofs /\ ~ P b ofs) m m' ->
  Mem.unchanged_on Q m m'.
Proof.
  clear. intros [ ] [ ].
  split; intros; eauto; destruct (classic (P b ofs)); eauto.
Qed.

Lemma cc_stacking_lm:
  ccref (cc_stacking injp) (cc_locset injp @ cc_locset_mach).
Proof.
  intros w se1 se2 q1 q2 Hse Hq. destruct Hq. cbn -[Z.add Z.mul] in * |- .
  destruct H2 as (UNCH & PERM & ARGS).
  set (ls2 := make_locset rs2 m2 sp2).
  (* we'll deal with making sure sp has thee right form later *)
  assert (exists sb2 sofs2, sp2 = Vptr sb2 sofs2) as (sb2 & sofs2 & Hsp2) by admit.
  edestruct PERM as [PRNG FITS]; eauto.
  edestruct (Mem.range_perm_free m2) as (m2_ & Hm2_); eauto.
  destruct H3; inv Hse; cbn -[Z.add Z.mul] in * |- .
  eassert (Hm_ : _). {
    eapply Mem.free_right_inject; eauto.
    intros. eapply H4; eauto.
    + constructor; eauto.
    + replace (ofs + delta - delta) with ofs by xomega.
    eapply Mem.perm_max, Mem.perm_implies; eauto. constructor.
  }
  exists (se2, (sg, injpw _ _ _ Hm_), lmw sg rs2 m2 (Vptr sb2 sofs2)). repeat apply conj.
  - constructor; cbn; auto. constructor; auto. 
    erewrite Mem.nextblock_free; eauto.
  - exists (lq vf2 sg ls2 m2_). split.
    + constructor; eauto.
      * intros r Hr. destruct Hr; cbn -[Z.add Z.mul]; eauto.
        edestruct ARGS as (v2 & Hv2 & Hv); eauto.
        rewrite Hv2. cbn. auto.
      * constructor.
    + econstructor; eauto.
      * constructor; eauto.
        -- admit. (* size arguments *)
        -- intros ofs ty REG. edestruct ARGS as (v2 & Hv2 & Hv); eauto.
  - intros r1 r2 (ri & (w' & Hw' & Hr1i) & Hri2). cbn -[Z.add Z.mul] in *.
    inv Hw'. inv Hr1i. inv H3. inv Hri2. cbn -[Z.add Z.mul] in *.
    rename m1'0 into m1'. rename m2'0 into m2'_. rename m' into m2'.
    assert (Hm'' : Mem.inject f' m1' m2'). {
      change (m_pred (minjection f' m1') m2').
      eapply m_invar; cbn; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      intros b2 ofs2 (b1 & delta & Hb & Hp) Hb2 Harg. inv Harg.
      eapply inject_incr_separated_inv in Hb;
        eauto using Mem.valid_block_free_1, Mem.perm_valid_block.
      eapply H4; eauto.
      * constructor; eauto.
      * eapply H9; eauto.
        eapply Mem.valid_block_inject_1; eauto.
    }
    exists (injpw f' m1' m2' Hm''); cbn.
    + constructor; eauto.
      * intros b ofs p Hb Hp.
        destruct (classic (loc_init_args (size_arguments sg) (Vptr sb2 sofs2) b ofs)).
        -- eapply Mem.perm_unchanged_on_2; eauto.
        -- eapply Mem.perm_free_3; eauto. eapply Mem.valid_block_free_1 in Hb; eauto.
           eapply H10; eauto. eapply Mem.valid_block_unchanged_on in Hb; eauto.
           eapply Mem.perm_unchanged_on_2; eauto.
      * eapply unchanged_on_combine; eauto.
        apply Mem.unchanged_on_trans with m2_.
        { eapply Mem.free_unchanged_on; eauto.
          intros i Hi [Hoor Hlia]. apply Hlia. constructor. eauto. }
        apply Mem.unchanged_on_trans with m2'_.
        { eapply Mem.unchanged_on_implies; eauto.
          tauto. }
        { eapply Mem.unchanged_on_implies; eauto.
          intros b ofs [_ ?] _. red. auto. }
      * red. unfold Mem.valid_block. erewrite <- (Mem.nextblock_free m2); eauto.
    + intros r REG. rewrite H22; eauto.
    + intros r REG. rewrite H23; eauto.
    + constructor.
    + auto.
    + intros b2 ofs2 Hofs2 b1 delta Hb Hp.
      admit.
(*
      cut (loc_out_of_reach f m1 b2 ofs2).
      * intros Hofs2' b1 delta Hb Hp.
        eapply (Mem.perm_inject f m1' m2'_) in Hp; eauto.
        replace (ofs2 - delta + delta) with ofs2 in Hp by xomega.

        eapply (Mem.perm_inject f' m1' m2'_) in Hp; eauto.
        replace (ofs2 - delta + delta) with ofs2 in Hp by xomega.
 b1 delta Hb Hp. inv Hofs2.
      erewrite <- Mem.unchanged_on_perm in Hp; eauto.
      eapply Mem.perm_free_2; eauto.
      * clear b1 delta Hb Hp. intros b1 delta Hb Hp.
*)
Admitted.

(** *** Typing of [cc_locset_mach] source state *)

(** This only works for [Archi.ptr64 = true], in which case there are
  no actual constraints on register typing. But we need to rely on
  this for now because of the way callee-save register preservation is
  formulated in the stacking proof: there is only a guarantee that the
  original query's source-level register still inject into the reply's
  target-level registers, but there is no guarantee that the
  target-level registers are actually unchanged. This means that on
  incoming calls, [cc_locset_mach] must occur first, before the [inj]
  component, if we are to satisfy the associated preservation property.
  But this means that the [lessdef_loc] component which we must insert
  after [wt_loc] for commutation purposes cannot be absorbed into
  [inj], and for similar reasons it cannot be folded into
  [cc_stacking] either.

  So we work around it using the following properties. *)

Lemma type_of_chunk_of_type ty:
  type_of_chunk (chunk_of_type ty) = ty.
Proof.
  destruct ty; cbn; auto.
Qed.

Lemma always_has_mreg_type v r:
  Val.has_type v (mreg_type r).
Proof.
  unfold mreg_type. change Archi.ptr64 with true.
  destruct v, r; cbn; auto.
Qed.

Lemma wt_loc_out_of_thin_air:
  cceqv (wt_loc @ cc_locset_mach) cc_locset_mach.
Proof.
  split.
  - intros [[xse [xxse sg]] w] se1 se2 q1 q2 [[Hsei] Hse] (_ & [Hq1] & Hq).
    inv Hsei. inv Hq1. exists w; repeat apply conj; auto.
    intros r1 r2 Hr. destruct Hr; cbn in *.
    eexists. split; constructor; auto. constructor.
    intros r Hr. apply always_has_mreg_type.
  - intros w se _ q1 q2 [ ] Hq. destruct Hq.
    exists (se, (se, sg), lmw sg rs m sp). cbn. repeat apply conj; auto.
    + constructor. auto.
    + eexists. split; constructor; auto. constructor.
      intros l Hl. destruct Hl.
      * apply always_has_mreg_type.
      * cbn -[Z.add Z.mul]. rewrite <- (type_of_chunk_of_type ty) at 2.
        destruct sp; cbn -[Z.add Z.mul]; auto.
        destruct Mem.load eqn:Hl; cbn; auto.
        eapply Mem.load_type. eauto.
    + intros r1 r2 (_ & [Hr1] & Hr). auto.
Qed.

Instance wt_loc_qprop R:
  PropagatesQueryInvariant (cc_locset R) wt_loc.
Proof.
  constructor. cbn.
  intros [sg wR] [? xsg] se1 se2 q1 q2 Hse Hxse Hq Hq2. subst. inv Hq. inv Hq2.
  exists (se1, sg). split; auto. constructor.
  intros. eapply val_has_type_inject; eauto. red. eauto.
Qed.

Instance wt_loc_rprop R:
  PropagatesReplyInvariant (cc_locset R) wt_loc.
Proof.
  constructor. cbn.
  intros [se ?] [sg wR] [? ?] se1 se2 q1 q2 r1 r2 Hse ? ? Hq Hq1 Hq2 (wR' & HwR' & Hr) Hr2.
  subst. inv Hq. inv Hq1. inv Hq2. inv Hr. inv Hr2. constructor.
  intros. eapply val_has_type_inject; eauto. red. eauto.
Qed.


