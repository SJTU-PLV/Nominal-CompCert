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

(* One key aspect of this convention is the encoding of arguments: at
  the source level, arguments for the call are stored in abstract
  locations, which become either registers or in-memory stack slots at
  the target level. Crucially, these stack slots must not be
  accessible as memory locations in the source program, otherwise the
  invariant relating abstract and concrete stack locations may be
  broken through aliasing. Hence, in the structural convention the
  source memory cannot be *equal* to the target memory, but instead
  must be a version of the target memory where permissions on the
  arguments region of the stack haven been removed.

  This can be obtained using the memory operation [Mem.free]. However,
  for some of the properties we need the corresponding memory state
  cannot be freely chosen, and we must instead use the following
  characterization. *)

Definition loc_outside_range (b: block) (lo hi: Z) :=
  fun b' ofs => b = b' -> ~ lo <= ofs < hi.

Record free_spec m b lo hi m_ :=
  {
    free_spec_range_perm: Mem.range_perm m b lo hi Cur Freeable;
    free_spec_no_perm ofs k p: lo <= ofs < hi -> ~ Mem.perm m_ b ofs k p;
    free_spec_unchanged: Mem.unchanged_on (loc_outside_range b lo hi) m m_;
    free_spec_nextblock: Mem.nextblock m_ = Mem.nextblock m;
  }.

Lemma free_free_spec m b lo hi m':
  Mem.free m b lo hi = Some m' ->
  free_spec m b lo hi m'.
Proof.
  split.
  - eapply Mem.free_range_perm; eauto.
  - eapply Mem.perm_free_2; eauto.
  - eapply Mem.free_unchanged_on; eauto.
    unfold loc_outside_range. clear. firstorder.
  - eapply Mem.nextblock_free; eauto.
Qed.

Lemma free_spec_perm_outside_range m b lo hi m_ b' ofs k p:
  free_spec m b lo hi m_ ->
  Mem.perm m_ b' ofs k p ->
  loc_outside_range b lo hi b' ofs.
Proof.
  intros Hm_ Hp Hb' Hofs. subst.
  eapply free_spec_no_perm; eauto.
Qed.

Lemma free_spec_valid_block m b lo hi m_ b':
  free_spec m b lo hi m_ ->
  Mem.valid_block m b' <-> Mem.valid_block m_ b'.
Proof.
  intro. unfold Mem.valid_block. erewrite <- free_spec_nextblock; eauto. tauto.
Qed.

Lemma free_spec_perm m b lo hi m_ b' ofs k p:
  free_spec m b lo hi m_ ->
  loc_outside_range b lo hi b' ofs ->
  Mem.perm m b' ofs k p <-> Mem.perm m_ b' ofs k p.
Proof.
  intros; split; intro Hp;
  eapply (Mem.unchanged_on_perm _ m m_); eauto using free_spec_unchanged;
  eapply Mem.perm_valid_block in Hp; eauto.
  rewrite free_spec_valid_block; eauto.
Qed.

Lemma free_spec_perm_3 m b lo hi m_ b' ofs k p:
  free_spec m b lo hi m_ ->
  Mem.perm m_ b' ofs k p ->
  Mem.perm m b' ofs k p.
Proof.
  intros. rewrite free_spec_perm; eauto using free_spec_perm_outside_range.
Qed.

Lemma free_spec_extends m b lo hi m_:
  free_spec m b lo hi m_ ->
  Mem.extends m_ m.
Proof.
  intros Hm_.
  split.
  - eapply free_spec_nextblock; eauto.
  - split; inversion 1; clear H; subst; rewrite ?Z.add_0_r.
    + intros Hp. eapply free_spec_perm; eauto using free_spec_perm_outside_range.
    + intros _. apply Z.divide_0_r.
    + intros Hp. erewrite (Mem.unchanged_on_contents _ m m_).
      * destruct ZMap.get; constructor. apply val_inject_refl.
      * eapply free_spec_unchanged; eauto.
      * eapply free_spec_perm_outside_range; eauto.
      * eapply free_spec_perm_3; eauto.
  - intros b' ofs k p Hp.
    destruct (classic (loc_outside_range b lo hi b' ofs)).
    + erewrite <- free_spec_perm; eauto.
    + right. unfold loc_outside_range in H.
      assert (b = b' /\ lo <= ofs < hi) as [Hb Hofs] by tauto. subst b'. clear H.
      eapply free_spec_no_perm; eauto.
Qed.

Lemma free_spec_inject_inv f m1 m2 b lo hi m2_:
  free_spec m2 b lo hi m2_ ->
  Mem.inject f m1 m2 ->
  (forall ofs, lo <= ofs < hi -> loc_out_of_reach f m1 b ofs) ->
  Mem.inject f m1 m2_.
Proof.
  intros Hm2_ Hm Hp. destruct Hm. split; auto.
  - destruct mi_inj. split; auto.
    + intros b1 b2 delta ofs k p Hb Hp'. erewrite <- free_spec_perm; eauto.
      intros Hb2 Hofs. destruct Hb2. eapply Hp; eauto.
      replace (ofs + delta - delta) with ofs by xomega.
      eauto 3 with mem.
    + intros b1 ofs b2 delta Hb Hp'.
      erewrite (Mem.unchanged_on_contents _ m2 m2_); eauto.
      * eapply free_spec_unchanged; eauto using free_spec_perm_outside_range.
      * eapply free_spec_perm_outside_range; eauto.
        erewrite <- free_spec_perm; eauto.
        intros Hb2 Hofs. subst. eapply Hp; eauto.
        replace (ofs + delta - delta) with ofs by xomega.
        eauto with mem.
  - intros. erewrite <- free_spec_valid_block; eauto.
  - eauto using free_spec_perm_3.
Qed.

Lemma free_spec_unfree m b lo hi m_:
  Mem.range_perm m b lo hi Cur Freeable ->
  (forall ofs k p, lo <= ofs < hi -> ~ Mem.perm m_ b ofs k p) ->
  Pos.le (Mem.nextblock m) (Mem.nextblock m_) ->
  exists m',
    free_spec m' b lo hi m_ /\
    Mem.unchanged_on (fun b' ofs => b = b' /\ lo <= ofs < hi) m m'.
Proof.
  (* mix m and m_ to recover the region from m in m' *)
Admitted.

Lemma free_spec_inject f m1 m2 b1 b2 delta lo hi m1_:
  free_spec m1 b1 lo hi m1_ ->
  Mem.inject f m1 m2 ->
  f b1 = Some (b2, delta) ->
  exists m2_,
    Mem.free m2 b2 (lo + delta) (hi + delta) = Some m2_ /\
    Mem.inject f m1_ m2_.
Admitted.

(** *** Definition *)

(** We can now define the structural convention. *)

Record cc_lm_world :=
  lmw {
    lmw_sg : signature;
    lmw_ls : Locmap.t;
    lmw_m : mem;
    lmw_sb : block;
    lmw_sofs : ptrofs;
  }.

Definition args_removed sg sb sofs m m_ :=
  free_spec m sb (offset_sarg sofs 0) (offset_sarg sofs (size_arguments sg)) m_ /\
  forall ofs, 0 <= ofs < size_arguments sg -> offset_fits sofs ofs.

Definition args_stored sg ls m sb sofs :=
  forall ofs ty,
    let l := S Outgoing ofs ty in
    In l (regs_of_rpairs (loc_arguments sg)) ->
    Mem.load (chunk_of_type ty) m sb (offset_sarg sofs ofs) = Some (ls l).
(* /\
    offset_fits sofs ofs. *)

Inductive cc_locset_mach_mq: cc_lm_world -> locset_query -> mach_query -> Prop :=
  cc_locset_mach_mq_intro sg vf ls m_ rs sb sofs ra m:
    (forall r, ls (R r) = rs r) ->
    args_removed sg sb sofs m m_ ->
    args_stored sg ls m sb sofs ->
    Val.has_type ra Tptr ->
    cc_locset_mach_mq
      (lmw sg ls m sb sofs)
      (lq vf sg ls m_)
      (mq vf (Vptr sb sofs) ra rs m).

Inductive cc_locset_mach_mr: cc_lm_world -> locset_reply -> mach_reply -> Prop :=
  cc_locset_mach_mr_intro sg ls ls' m'_ sb sofs m rs' m':
    (forall r, In r (regs_of_rpair (loc_result sg)) -> rs' r = ls' (R r)) ->
    (forall r, is_callee_save r = true -> rs' r = (ls (R r))) ->
    args_removed sg sb sofs m' m'_ ->
    Mem.unchanged_on (loc_init_args sb sofs (size_arguments sg)) m m' ->
    cc_locset_mach_mr (lmw sg ls m sb sofs) (lr ls' m'_) (mr rs' m').

Program Definition cc_locset_mach: callconv li_locset li_mach :=
  {|
    match_senv _ := eq;
    match_query := cc_locset_mach_mq;
    match_reply := cc_locset_mach_mr;
  |}.

(** ** Mixing memory states *)

(** For incoming calls, [Stacking] uses the simulation convention
  [cc_locset inj @ cc_locset_mach]. However, the proof does not keep
  track of an intermediate memory state. This means that to prove that
  replies are related, we first need to exhibit an intermediate memory
  state such that 1. freeing the arguments region yields the
  source-level memory, and 2. this arguments region is unchanged with
  respect the corresponding memory state of the query.

  To achieve this we use the following construction:
  [Mem_mix m' b lo hi m] merges the region of [m] specified by
  [(b, lo, hi)] into [m']. The intention is that if [m'] was obtained
  from [m] by [Mem.free], potentially followed by additional
  operations, [Mem_mix] will "undo" the free. *)

Parameter Mem_mix : mem -> block -> Z -> Z -> mem -> option mem.

Axiom Mem_mix_free_spec:
  forall m' b lo hi m m'',
    Mem_mix m' b lo hi m = Some m'' ->
    free_spec m'' b lo hi m'.

Axiom Mem_mix_unchanged:
  forall m' b lo hi m m'',
    Mem_mix m' b lo hi m = Some m'' ->
    Mem.unchanged_on (fun b1 ofs1 => ~ (b = b1 /\ lo <= ofs1 < hi)) m' m''.

Axiom Mem_mix_updated:
  forall m' b lo hi m m'',
    Mem_mix m' b lo hi m = Some m'' ->
    Mem.unchanged_on (fun b1 ofs1 => b = b1 /\ lo <= ofs1 < hi) m m''.

Axiom Mem_nextblock_mix:
  forall m' b lo hi m m'',
    Mem_mix m' b lo hi m = Some m'' ->
    Mem.nextblock m'' = Mem.nextblock m'.

Axiom Mem_mix_extends:
  forall m1' m2' b lo hi m1 m2 m2'',
    Mem_mix m2' b lo hi m2 = Some m2'' ->
    Mem.extends m1' m2' ->
    Mem.extends m1 m2 ->
    exists m1'',
      Mem_mix m1' b lo hi m1 = Some m1'' /\
      Mem.extends m1'' m2''.

Axiom Mem_mix_inject:
  forall f' m1' m2' b lo hi f m1 m2 m2'',
    Mem_mix m2' b lo hi m2 = Some m2'' ->
    Mem.inject f' m1' m2' ->
    Mem.inject f m1 m2 ->
    inject_incr f f' ->
    exists m1'',
      Mem_mix m1' b lo hi m1 = Some m1'' /\
      Mem.inject f' m1'' m2''.

Axiom Mem_mix_inject_left:
  forall f f' m1 m2 m1' m2' b1 b2 delta lo hi m1'',
    Mem_mix m1' b1 lo hi m1 = Some m1'' ->
    Mem.inject f m1 m2 ->
    Mem.inject f' m1' m2' ->
    f b1 = Some (b2, delta) ->
    Mem.unchanged_on (fun b ofs => b = b2 /\ lo + delta <= ofs < hi + delta) m2 m2' ->
    Mem.inject f' m1'' m2'.

(** ** Matching [cc_stacking] *)

(** With this, we can prove the simulation convention refinements
  property we need to match the Stacking proof. *)

(** *** Incoming calls *)

Lemma offset_sarg_inject f m1 m2 sb1 sb2 delta sofs1 sofs2 ofs sz:
  Mem.inject f m1 m2 ->
  Mem.range_perm m1 sb1 (offset_sarg sofs1 0) (offset_sarg sofs1 sz) Cur Freeable ->
  (forall ofs, 0 <= ofs <= sz -> offset_fits sofs1 ofs) ->
  0 <= ofs <= sz ->
  f sb1 = Some (sb2, delta) ->
  sofs2 = Ptrofs.add sofs1 (Ptrofs.repr delta) ->
  offset_fits sofs2 ofs /\
  offset_sarg sofs2 ofs = offset_sarg sofs1 ofs + delta.
Proof.
  intros Hm Hp Hofs_sz FITS Hsb Hsofs.
  erewrite ?(access_fits sofs1 _) in * by (apply Hofs_sz; xomega).
  unfold offset_fits, offset_sarg in *.
Abort.

Lemma cc_lm_stacking:
  ccref (cc_locset_mach @ cc_mach inj) (cc_stacking inj).
Proof.
  intros [[_ wlm] w] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2). cbn in *.
  destruct Hqi2. inv Hq1i.
  inversion H2 as [ | | | | ? ? sb2 sofs2 sdelta Hsb Hsofs | ]; clear H2; subst.
  exists (stkw inj w sg ls sb2 (Ptrofs.add sofs (Ptrofs.repr sdelta)) m2).
  split; [ | split].
  - cbn. auto.
  - destruct H15 as [FREE FITS].
    constructor; auto.
    + setoid_rewrite H13. auto.
    + cbn. repeat apply conj.
      * admit.
      * apply Mem.unchanged_on_refl.
      * admit.
      * intros ofs ty REG.
        admit.
    + assert (Mem.extends m_ m1) by eauto using free_spec_extends.
      destruct H6; cbn in *. erewrite <- Mem.mext_next by eauto. constructor.
      eapply Mem.extends_inject_compose; eauto.
    + admit.
    + destruct H4; cbn in *; congruence.
  - intros r1 r2 Hr. inv Hr.
    assert
      (exists m1'',
          Mem_mix m1' sb (offset_sarg sofs 0) (offset_sarg sofs (size_arguments sg)) m1 = Some m1'')
      as [m1'' Hm1''] by admit.
    eassert _ by (eapply Mem_mix_free_spec; eauto).
    set (rs1' r := if is_callee_save r then ls (R r) else
                   if in_dec mreg_eq r (regs_of_rpair (loc_result sg)) then ls1' (R r) else
                   Vundef).
    exists (mr rs1' m1''). split.
    + constructor.
      * subst rs1'. intros r REG. cbn.
        destruct in_dec; try contradiction.
        replace (is_callee_save r) with false; auto.
        pose proof (loc_result_caller_save sg) as Hr.
        destruct loc_result; cbn in *; intuition congruence.
      * subst rs1'. intros r REG. cbn.
        rewrite REG. congruence.
      * destruct H15. split; auto.
      * eapply Mem.unchanged_on_implies.
        -- eapply Mem_mix_updated; eauto.
        -- destruct 1; eauto.
    + exists w'; split; auto.
      constructor.
      * intros r. subst rs1'. cbn.
        destruct is_callee_save eqn:CSR; eauto.
        destruct in_dec; eauto.
      * destruct H6. inv H18. inv H21. cbn in *.
        erewrite <- Mem_nextblock_mix by eauto. constructor.
        eapply Mem_mix_inject_left; eauto.
        eapply Mem.unchanged_on_implies; eauto.
        intros b ofs [Hb Hofs] VLD. subst. constructor.
        admit. (* ptr arith *)
Admitted.

(** *** Outgoing calls *)

(** The following construction is needed both for the commutation
  property associated with [cc_locset_mach] and [cc_mach] and in the
  simulation proof for external calls in [Stacking]. It is used to
  formulate an [li_locset] view of an [li_mach] query. *)

Definition make_locset (rs: Mach.regset) (m: mem) (sp: val) (l: loc) : val :=
  match l with
    | R r => rs r
    | S Outgoing ofs ty =>
      let v := load_stack m sp ty (Ptrofs.repr (fe_ofs_arg + 4 * ofs)) in
      Val.maketotal v
    | _ => Vundef
  end.

Lemma cc_stacking_lm:
  ccref (cc_stacking injp) (cc_locset injp @ cc_locset_mach).
Proof.
  intros w se1 se2 q1 q2 Hse Hq. destruct Hq. cbn in * |- .
  destruct H2 as (? & ? & ? & ?).
  set (ls2 := make_locset rs2 m2 (Vptr sb2 sofs2)).
  edestruct (Mem.range_perm_free m2) as (m2_ & Hm2_); eauto.
  destruct H3; inv Hse; cbn in * |- .
  eassert (Hm_ : _). {
    eapply Mem.free_right_inject; eauto.
    intros. eapply H4; eauto.
    + constructor; eauto.
    + replace (ofs + delta - delta) with ofs by xomega.
    eapply Mem.perm_max, Mem.perm_implies; eauto. constructor.
  }
  exists (se2, (sg, injpw _ _ _ Hm_), lmw sg ls2 m2 sb2 sofs2). repeat apply conj.
  - constructor; cbn; auto. constructor; auto. 
    erewrite Mem.nextblock_free; eauto.
  - exists (lq vf2 sg ls2 m2_). split.
    + constructor; eauto.
      * intros r Hr. destruct Hr; cbn -[Z.add Z.mul]; eauto.
        edestruct H8 as (v2 & Hv2 & Hv); eauto.
        admit. (* ptr arith *)
      * constructor.
    + econstructor; eauto.
      * split; eauto using free_free_spec.
      * intros ofs ty l REG. subst l ls2. cbn -[Z.add Z.mul].
        edestruct H8 as (v2 & Hv2 & Hv); eauto.
        rewrite Hv2. admit. (* ptr arith *)
  - intros r1 r2 (ri & (w' & Hw' & Hr1i) & Hri2). cbn in *.
    inv Hw'. inv Hr1i. inv H9. inv Hri2. destruct H28. cbn in *.
    rename m1'0 into m1'. rename m2'0 into m2'_. rename m' into m2'. 
    assert (Hm'' : Mem.inject f' m1' m2'). {
      eapply Mem.inject_extends_compose; eauto.
      eapply free_spec_extends; eauto.
    }
    exists (injpw f' m1' m2' Hm''); cbn.
    + constructor; eauto.
      * intros b ofs p Hb Hp.
        admit. (* permission inversion on free_spec etc. *)
      * admit. (* the unchanged_on mixing *)
      * red. unfold Mem.valid_block. erewrite <- (Mem.nextblock_free m2); eauto.
    + intros r REG. rewrite H26; eauto.
    + intros r REG. rewrite H27; eauto.
    + constructor.
    + auto.
Admitted.


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

(*
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
  destruct (free_args sg m1 sp1) as [m1_ | ] eqn:H1; [ | constructor].
  unfold free_args in H1. destruct sp1 as [ | | | | | sb1 sofs1]; try discriminate.
  cut (exists w' m2_, w ~> w' /\ free_args sg m2 sp2 = Some m2_ /\ match_mem R w' m1_ m2_).
  - intros (? & ? & ? & ? & ?). rewrite H0. rauto.
  - revert m1 m2 Hm m1_ H1. inv Hsp. revert w H1. cbn [free_args].
    induction regs_of_rpairs.
    + cbn. intros. inv H0. exists w, m2. split; auto. reflexivity.
    + destruct a as [ | [ ]]; cbn -[Z.add Z.mul acc] in *; auto.
      intros. destruct Mem.free eqn:Hm1_ in H0; try discriminate.
      eapply transport in Hm1_. 2: {
        clear Hm1_. repeat rstep.
        eapply ptrbits_ptr_inject; eauto.
        eapply H. pose proof (size_chunk_pos (chunk_of_type ty)). xomega.
      }
      destruct Hm1_ as (m2_ & Hm2_ & w' & Hw' & Hm_).
      edestruct (IHl w') as (w'' & m2__ & Hw'' & Hm2__ & Hm__); eauto.
      { eapply mi_acc; eauto. }
      exists w'', m2__. split; [rauto | ].
      rewrite <- Ptrofs.add_assoc, Hm2_.
      eauto.
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
Admitted.
(*
  intros [[_ [sg ls1]] wR] se1 se2 q1 q2 [[ ] Hse2] (qi & Hq1i & Hqi2).
  cbn in * |- . destruct Hqi2. inv Hq1i. rename m' into m1_. rename ls into ls1.

  (** Synthesizing the query *)
  transport H14. rename x into m2_.
  edestruct match_agree_args as (ls2 & Hargs2 & Hrs2 & Hls); eauto.
  { intro r. rewrite H15. eauto. }
  set (ls2wt l := Val.ensure_type (ls2 l) (Loc.type l)).

  exists (se2, (sg, wR'), (sg, rs2)). repeat apply conj.
  - cbn. split; rauto.
  - exists (lq vf2 sg ls2 m2_). split.
    + econstructor; try rauto; auto.
    + constructor; eauto.
      destruct H4; cbn in *; congruence.
  - intros r1 r2 (ri & (wR'' & HwR'' & Hr1i) & Hri2). 
    destruct Hr1i. inv Hri2. rename rs' into rs2'.
    set (rs1' r := result_regs sg ls1 ls1' (Locations.R r)).
    exists (mr rs1' m1'). split.
    + constructor; auto.
      * intros r Hr. unfold rs1'. rewrite <- result_regs_agree_callee_save; auto.
      * intros r Hr. unfold rs1'. cbn. destruct in_dec; tauto.
    + exists wR''. split; [rauto | ]. constructor; auto.
      intro r. unfold rs1', result_regs.
      destruct in_dec. { rewrite H18; auto. }
      destruct is_callee_save eqn:Hr; auto.
      rewrite H14 by auto. rewrite H15. generalize (H5 r).
      repeat rstep. change (wR ~> wR''). rauto.
Qed.
*)

(** ** [cc_mach_asm] *)

Instance commut_mach_asm R:
  Commutes cc_mach_asm (cc_mach R) (cc_asm R).
Proof.
  intros [[_ [rs1 nb1]] wR] se1 se2 q1 q2 [[ ] Hse2] (qi & Hq1i & Hqi2).
  cbn in * |- . destruct Hq1i. destruct q2 as [rs2 m2], Hqi2 as [Hrs Hm]. rename m into m1.
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
