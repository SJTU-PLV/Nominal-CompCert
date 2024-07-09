Require Import Axioms.
Require Import Events.
Require Import LanguageInterface.
Require Import CallconvAlgebra.
Require Import CKLR.
Require Import Extends.

(** The idea which causes this file: Can we enhence a forward simulation with a [CKLR], such that we can
    formulate the memory transitions during the whole simulation diagram instead of only in
    queries and replies? This may be cleaner than the [Lens] solution we are using. *)

(** One issue is that can we define an [id] cklr for the passes using [id] callconv? *)
(** The current answer is *No* because we cannot fulfill the [cklr_store] condition defined in CKLR.v,
    which basically says that if m1<->m2, an injected pair of values are stored into them, m1'<->m2' should hold.
    But if Vundef and Vint 42 are stored, the [eq] relation of memories are broken. *)

(** So we have to change [cklr] to make it more general? Maybe add a [match_value w] relation instead of
    just using Val.inject (mi w). *)

(** Or from the opposite perspective, why Jeremie use (mi w)? This seems to be some form of *hardcoding* of the
    [match_value] relation which all passes should obey. Can we somehow *hardcode* the injp R-G conditions for
    all passes similarly to make the proof easier? *)
Program Definition id: cklr :=
  {|
    world := unit;
    wacc := ⊤;
    mi w := inject_id;
    match_mem w := eq;
    match_stbls w := eq;
  |}.

Next Obligation.
  repeat rstep. apply inject_incr_refl.
Qed.

Next Obligation.
  rauto.
Qed.


Next Obligation.
  repeat intro. subst. apply Genv.match_stbls_id.
Qed.

Next Obligation.
  intros [ ] m1 m2 Hm lo hi.
  destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn:H1. subst.
  exists tt; split; rauto.
Qed.

Next Obligation.
  intros [ ] m1 m2 Hm [[b lo] hi] r2 Hr.
  apply coreflexivity in Hr; subst. simpl. red.
  destruct (Mem.free m2 b lo hi) as [m2'|] eqn:Hm1'; [|constructor].
  constructor.
  exists tt; split; rauto.
Qed.

Next Obligation.
  intros [ ] chunk m1 m2 Hm [b ofs] p2 Hp.
  apply coreflexivity in Hp; subst. simpl. red.
  destruct (Mem.load chunk m2 b ofs) as [v1|] eqn:Hv1; [|constructor].
  rewrite val_inject_lessdef_eqrel.
  constructor. constructor.
Qed.

Next Obligation.
  intros [ ] chunk m1 m2 Hm [b ofs] p2 Hp v1 v2 Hv.
  apply coreflexivity in Hp; subst. simpl. red.
  destruct (Mem.store chunk m2 b ofs v1) as [m1'|] eqn:Hm1'; [|constructor].
  red in Hv.
  apply val_inject_lessdef in Hv.
  rewrite Hm1'.
  constructor. exists tt; split; rauto.
Qed.

Next Obligation.
  intros [ ] m1 m2 Hm [b ofs] p2 Hp sz.
  apply coreflexivity in Hp; subst. simpl. red.
  destruct (Mem.loadbytes m1 b ofs sz) as [v1|] eqn:Hv1; [|constructor].
  edestruct Mem.loadbytes_extends as (v2 & Hv2 & Hv); eauto.
  rewrite Hv2. rauto.
Qed.

Next Obligation.
  intros [ ] m1 m2 Hm [b1 ofs1] p2 Hp vs1 vs2 Hv.
  apply coreflexivity in Hp. subst. simpl. red.
  destruct (Mem.storebytes m1 b1 ofs1 vs1) as [m1'|] eqn:Hm1'; [|constructor].
  edestruct Mem.storebytes_within_extends as (m2' & Hm2' & Hm'); eauto.
  eapply list_rel_forall2. apply Hv.
  rewrite Hm2'. constructor. exists tt; split; rauto.
Qed.

Next Obligation.
  intros [ ] m1 m2 Hm [b1 ofs1] p2 Hp p k H.
  apply coreflexivity in Hp. subst. simpl in *.
  eapply Mem.perm_extends; eauto.
Qed.

Next Obligation.
  intros [ ] m1 m2 Hm b1 b2 Hb.
  apply coreflexivity in Hb. subst.
  apply Mem.valid_block_extends; eauto.
Qed.

Next Obligation.
  intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 Hb Hb1' Hb2' Hp1 Hp2.
  inv Hb1'. inv Hb2'. eauto.
Qed.

Next Obligation.
  extlia.
Qed.

Next Obligation.
  rewrite Z.add_0_r.
  assumption.
Qed.

Next Obligation.
  intuition extlia.
Qed.

Next Obligation.
  inv H0. inv H3. rewrite Z.add_0_r in H1.
  eapply Mem.perm_extends_inv; eauto.
Qed.

Next Obligation.
  destruct H0 as (?&?&?).
  inv H. inv H1. rewrite mext_sup. rewrite mext_sup0.
  reflexivity.
Qed.

(** * Useful lemmas *)

Lemma ext_lessdef w v1 v2:
  Val.inject (mi ext w) v1 v2 <-> Val.lessdef v1 v2.
Proof.
  symmetry. apply val_inject_lessdef.
Qed.

Lemma ext_lessdef_list w vs1 vs2:
  Val.inject_list (mi ext w) vs1 vs2 <-> Val.lessdef_list vs1 vs2.
Proof.
  split; induction 1; constructor; auto; apply val_inject_lessdef; auto.
Qed.

Lemma ext_extends w m1 m2:
  match_mem ext w m1 m2 <-> Mem.extends m1 m2.
Proof.
  reflexivity.
Qed.
