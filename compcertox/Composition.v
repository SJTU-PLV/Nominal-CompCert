From Coq Require Import
     Relations
     RelationClasses
     List.
From compcert.lib Require Import
     Coqlib.
From compcert.common Require Import
     LanguageInterface
     Events Globalenvs
     Smallstep Linking
     Memory Values
     CallconvAlgebra
     CategoricalComp
     FlatComp.
From compcert.cfrontend Require Import
     Clight Ctypes.
From compcert.compcertox Require Import
     Lifting AbRel CModule
     TensorComp SkelLinking.

Program Definition cc_null {liA liB}: callconv liA liB :=
  {|
    ccworld := Empty_set;
    match_senv w _ _ := False;
    match_query w _ _ := False;
    match_reply w _ _ := False;
  |}.
Solve All Obligations with
  cbn; intros; subst; intuition auto.

Notation "0" := cc_null : cc_scope.

(* FIXME: why the precedence can't be looser than 9? *)
(* Notation "[ R ]" := (singleton_rel R) (at level 9): krel_scope. *)

Generalizable All Variables.

(** ** Definitions for CAL in CompCertOX *)

Section LAYER_DEF.
  (* Ls is the high level spec with Ks as the abstract data whereas the program
     running on top of Lf is the low level spec *)
  Context {Ks Kf} (Ls: layer Ks) (Lf: layer Kf).

  Section PROG.
    Context (p: Clight.program).
    Definition prog_layer_comp sk := comp_semantics' (Clight.semantics2 p @ Kf) Lf sk.
    Record prog_sim (R: abrel Ks Kf) : Prop :=
      mk_prog_sim {
          psim_sk_order: linkorder (skel Lf) (skel Ls)
                         /\ linkorder (AST.erase_program p) (skel Ls);
          psim_simulation: forward_simulation 0 R Ls (prog_layer_comp (skel Ls))
        }.
  End PROG.

  Section CMOD.
    Context (M: cmodule).
    Definition cmod_layer_comp sk := comp_semantics' (semantics M @ Kf) Lf sk.
    Record cmod_sim (R: abrel Ks Kf) : Prop :=
      mk_cmod_sim {
          csim_sk_order: linkorder (skel Lf) (skel Ls)
                         /\ linkorder (cmod_skel M) (skel Ls);
          csim_simulation: forward_simulation 0 R Ls (cmod_layer_comp (skel Ls));
        }.
  End CMOD.

End LAYER_DEF.

(* "M:Y" part should have higher priority than the type annotation "a:T" which
   is at level 100 *)
Notation " X ⊢ [ R ] M : Y " := (cmod_sim Y X M R) (at level 85, M at level 99).

Instance sim_monotonic {Ks Kf: Type}:
  Proper ((forward_simulation 1 1) --> (forward_simulation 1 1) ==> eq  ==> eq ==> impl)
         (@cmod_sim Ks Kf).
Proof.
  intros L2 L2' HL2 L1 L1' HL1 M N Hmn R S Hrs H.
  unfold impl, flip in *. subst. destruct H as ((?&?)&?). split; [split|].
  - destruct HL1. destruct X.
    destruct HL2. destruct X. congruence.
  - destruct HL2. destruct X. congruence.
  - eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_left.
    eapply compose_forward_simulations. eauto.

    eapply open_fsim_ccref. apply cc_compose_id_right.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations. eauto.

    destruct HL2. destruct X. rewrite fsim_skel.
    unfold cmod_layer_comp.
    eapply categorical_compose_simulation'; eauto. reflexivity.
Qed.

Goal forall K1 K2 (L1: layer K1) (L2: layer K2) R M L2',
    L1 ⊢ [ R ] M : L2 -> L2' ≤ L2 -> L1 ⊢ [ R ] M : L2'.
Proof.
  intros * H HL2. now rewrite HL2.
Qed.

(** *** Promoting a Clight program into a singleton CModule *)

Section HCOMP_SINGLETON.

  Import SmallstepLinking Smallstep.
  Context {li} (L: semantics li li).
  Context `{!ProgramSem L}.

  Let LS := fun k : unit + Empty_set =>
              match k with
              | inl _ => L
              | inr e => match e with end
              end.

  Inductive singleton_match: state L -> list (frame LS) -> Prop :=
  | singleton_match_intro s: singleton_match s (st LS (inl tt) s :: nil).

  Ltac esca := eexists; split; try constructor; intuition auto.
  Lemma hcomp_singleton_fsim: L ≤ SmallstepLinking.semantics' LS (skel L).
  Proof.
    constructor. econstructor; eauto. intros i.
    { split; cbn; intros. exists (inl tt). apply H. destruct H as [[|] Hx]. apply Hx. inv e. }
    intros se _ [ ] [ ] _. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := singleton_match); cbn; intros; subst.
    - esca. eapply incoming_query_valid. eauto.
    - inv H. esca.
    - inv H. exists tt. eexists; repeat apply conj; eauto. constructor; eauto.
      intros [|]. destruct u. eapply outgoing_query_invalid; eauto. inv e.
      intros; subst. esca.
    - inv H0. esca.
    - apply well_founded_ltof.
  Qed.

End HCOMP_SINGLETON.

Lemma singleton_sim `(R: abrel Ks Kf) Ls Lf p:
  prog_sim Ls Lf p R -> cmod_sim Ls Lf p R.
Proof.
  intros ((?&?)&?). split; [split|]; eauto.
  - unfold cmod_layer_comp, semantics, ref. cbn.

    eapply open_fsim_ccref. apply cc_compose_id_right.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations. eauto.

    unfold prog_layer_comp.
    eapply categorical_compose_simulation'; [ | reflexivity | eauto | eauto ].
    apply lifting_simulation.
    apply hcomp_singleton_fsim. typeclasses eauto.
Qed.

(** ** Composition Rules  *)

Lemma cc_compose_null {a b c}:
  @ccref a b (cc_compose (li2:=c) 0 0) 0.
Proof. intros x. destruct x. easy. Qed.

(** *** Vertical Composition *)

Section VCOMP.

  Context `{R: abrel Ks Kn} `{S: abrel Kn Kf} {M N: cmodule}
          `(HL1: cmod_sim Ls Ln M R) `(HL2: cmod_sim Ln Lf N S).
  Hypothesis HR: disjoint_abrel R S.
  Context `{!CategoricalLinkable (semantics M) (semantics N)}.
  Context MN (HMN: cmod_app M N = Some MN).

  Lemma vcomp_skel_link: linkorder (cmod_skel MN) (skel Ls).
  Proof.
    destruct HL1 as [[A B] ?].
    destruct HL2 as [[C D] ?].
    eapply link_lub.
    - exact B.
    - eapply linkorder_trans. exact D. exact A.
    - now apply cmod_app_skel.
  Qed.

  Theorem layer_vcomp: cmod_sim Ls Lf MN (R @ S).
  Proof.
    destruct HL1 as [[Hsk1 Hmod1] H1].
    destruct HL2 as [[Hsk2 Hmod2] H2].
    split. split; eauto.
    eapply linkorder_trans; eauto.
    eapply vcomp_skel_link.

    edestruct (cmodule_abrel S M).
    exploit @categorical_compose_simulation'.
    constructor. exact X. apply H2.
    instantiate (1 := (skel Ls)). 1-2: assumption.
    clear X. intros X.

    eapply open_fsim_ccref. eapply cc_compose_null.
    unfold flip. apply krel_comp_ref; eauto.
    eapply compose_forward_simulations.
    apply H1. unfold cmod_layer_comp.

    eapply open_fsim_ccref. apply cc_compose_id_right.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations. apply X. clear X.

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_left.
    eapply compose_forward_simulations.
    unfold cmod_layer_comp. apply assoc1.

    eapply categorical_compose_simulation';
      [ | apply identity_forward_simulation
        | apply vcomp_skel_link
        | eapply linkorder_trans; eauto
      ].

    eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_left.
    eapply compose_forward_simulations.
    apply lift_categorical_comp2.
    apply lifting_simulation.
    apply cmodule_categorical_comp_simulation; eauto.
  Qed.

End VCOMP.

(** *** Horizontal Composition *)

Lemma layer_fsim_id {K} (L: layer K):
  forward_simulation 0 1 L L.
Proof.
  constructor.
  eapply Forward_simulation with _ (fun _ _ _ => _); auto.
  - firstorder.
  - intros se _ [ ] [ ] _.
    eapply forward_simulation_plus with (match_states := eq);
    cbn; intros; subst; eauto 10 using plus_one. inv q1.
  - apply well_founded_ltof.
Qed.

Lemma if_rewrite {A B} (f: A -> B) a b:
  (fun (i : bool) => f (if i then a else b)) = (fun i => if i then f a else f b).
Proof.
  apply Axioms.functional_extensionality; intros [|]; auto.
Qed.

Section HCOMP.

  Context `{R: abrel Ks Kf} {M N: cmodule}
          `(HL1: cmod_sim Ls1 Lf M R) `(HL2: cmod_sim Ls2 Lf N R).
  Context MN (HMN: cmod_app M N = Some MN).
  Context sk (Hsk: link (skel Ls1) (skel Ls2) = Some sk).

  Lemma hcomp_skel_link: linkorder (cmod_skel MN) sk.
  Proof.
    eapply link_monotonic.
    3-4: eauto using cmod_app_skel. apply HL1. apply HL2.
  Qed.

  Let Mi := (fun i : bool => if i then semantics M else semantics N).
  Context `{!FlatLinkable Mi}.

  Let L i := match i with true => Ls1 | false => Ls2 end.

  Theorem layer_hcomp: cmod_sim (flat_comp_semantics' L sk) Lf MN R.
  Proof.
    destruct HL1 as [[Hsk1 Hmod1] H1].
    destruct HL2 as [[Hsk2 Hmod2] H2].
    split. split; cbn; eauto.
    eapply linkorder_trans; eauto. eapply link_linkorder; eauto.
    apply hcomp_skel_link.
    (* monotonicity *)
    eapply open_fsim_ccref. eapply cc_compose_null.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations.

    set (Ls := fun i => match i with true => cmod_layer_comp Lf M (skel Ls1)
                             | false => cmod_layer_comp Lf N (skel Ls2) end).
    apply (flat_composition_simulation' _ _ _ Ls); try (intros [|]; auto).
    1-2: eapply link_linkorder in Hsk; intuition eauto.
    (* distributivity *)
    unfold cmod_layer_comp.
    set (Ls := fun i => match i with true => semantics M @ Kf | false => semantics N @ Kf end).
    set (Lsk := fun i => match i with true => skel Ls1 | false => skel Ls2 end).
    set (LX := fun i => comp_semantics' (Ls i) Lf (Lsk i)).
    replace (flat_comp_semantics' _ sk) with (flat_comp_semantics' LX sk).
    2: {
      f_equal. subst LX. apply Axioms.functional_extensionality.
      intros [|]; reflexivity.
    }

    eapply open_fsim_ccref. eapply cc_compose_id_left.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations.
    eapply distributivity2. constructor. exact true.

    (* under approximation *)
    eapply categorical_compose_simulation'.
    - subst Ls. rewrite <- if_rewrite. etransitivity.
      apply lift_flat_comp2. apply lifting_simulation.
      apply cmodule_flat_comp_simulation; auto.
    - apply layer_fsim_id.
    - apply hcomp_skel_link.
    - eapply linkorder_trans; eauto. eapply link_linkorder; eauto.
  Qed.

End HCOMP.

(** *** Tensor Product *)

Lemma cc_id_null:
  cceqv (@cc_id li_null) 0.
Proof. split; intros x *; easy. Qed.

Section TCOMP.

  Context `(R1: abrel Ks1 Kf1) `(R2: abrel Ks2 Kf2) (M N: cmodule).
  Context `(HL1: Lf1 ⊢ [R1] M : Ls1) `(HL2: Lf2 ⊢ [R2] N : Ls2).
  Context sks (Hsks: link (skel Ls1) (skel Ls2) = Some sks)
          skf (Hskf: link (skel Lf1) (skel Lf2) = Some skf)
          MN (HMN: cmod_app M N = Some MN).
  Let Mi := (fun i : bool => if i then semantics M else semantics N).
  Context `{!FlatLinkable Mi}.
  Hypothesis HR: disjoint_abrel R1 R2.

  Lemma tens_skel_link1: linkorder skf sks.
  Proof.
    eapply link_monotonic.
    3-4: eauto. apply HL1. apply HL2.
  Qed.
  Lemma tens_skel_link2: linkorder (cmod_skel MN) sks.
  Proof.
    eapply link_monotonic.
    3-4: eauto using cmod_app_skel. apply HL1. apply HL2.
  Qed.

  Lemma layer_tcomp: cmod_sim (tensor_comp_semantics' Ls1 Ls2 sks)
                         (tensor_comp_semantics' Lf1 Lf2 skf) MN (R1 * R2).
  Proof.
    destruct HL1 as [[HLsk1 Hmod1] H1].
    destruct HL2 as [[HLsk2 Hmod2] H2].
    split. split. apply tens_skel_link1. apply tens_skel_link2.

    rewrite <- (proj1 cc_id_null).
    rewrite -> (proj2 cc_id_null) in H1, H2.
    exploit @tensor_compose_simulation;
      [ exact H1 | exact H2 | .. ]; eauto.
    1-2: eapply link_linkorder in Hsks; apply Hsks.
    intros X. eapply open_fsim_ccref. apply cc_compose_id_left.
    unfold flip. apply cc_compose_id_right.
    eapply compose_forward_simulations. exact X. clear X.

    unfold tensor_comp_semantics', cmod_layer_comp.

    etransitivity.
    {
      apply flat_composition_simulation'. instantiate (1 := fun i => match i with true => _ | false => _ end).
      intros [|].
      - instantiate (1 := comp_semantics' (semantics M @ (Kf1 * Kf2)) (lift_layer_k Lf1) (skel Ls1)).
        etransitivity. apply map_monotonicity. apply lift_categorical_comp1.
        etransitivity. apply map_ext_comp.
        etransitivity. apply map_int_comp. typeclasses eauto.
        eapply categorical_compose_simulation'.
        + apply lts_lifting_assoc.
        + reflexivity.
        + exact Hmod1.
        + exact HLsk1.
      - instantiate (1 := comp_semantics' (semantics N @ (Kf1 * Kf2)) (layer_comm (lift_layer_k Lf2)) (skel Ls2)).
        etransitivity. apply map_monotonicity. apply map_monotonicity. apply lift_categorical_comp1.
        etransitivity. apply map_monotonicity. apply map_ext_comp.
        etransitivity. apply map_ext_comp.
        etransitivity. apply map_int_comp. typeclasses eauto.
        etransitivity. apply map_int_comp. typeclasses eauto.
        eapply categorical_compose_simulation'.
        + etransitivity. 2: apply lts_lifting_comm.
          etransitivity. 2: apply map_monotonicity; apply lts_lifting_assoc.
          reflexivity.
        + reflexivity.
        + exact Hmod2.
        + exact HLsk2.
      - intros [|]; cbn.
        1-2: eapply link_linkorder in Hsks; apply Hsks.
    }

    set (LX:= fun i:bool => if i then semantics M @ (Kf1 * Kf2) else semantics N @ (Kf1 * Kf2)).
    set (LY:= fun i:bool => if i then lift_layer_k Lf1 else layer_comm (lift_layer_k Lf2)).
    set (Lsk:= fun i:bool => if i then skel Ls1 else skel Ls2).
    replace (flat_comp_semantics' _ sks) with (flat_comp_semantics' (fun i:bool => comp_semantics' (LX i) (LY i) (Lsk i)) sks).
    2: {
      subst LX  LY Lsk. cbn. f_equal. apply Axioms.functional_extensionality.
      intros [|]; reflexivity.
    }

    etransitivity. apply categorical_flat_interchangeable. cbn.
    eapply categorical_compose_simulation'.
    - subst LX. rewrite <- if_rewrite with (f := fun x => x @ (Kf1 * Kf2)).
      etransitivity. apply lift_flat_comp2. apply lifting_simulation.
      apply cmodule_flat_comp_simulation; eauto.
    - reflexivity.
    - apply tens_skel_link2.
    - apply tens_skel_link1.
  Qed.

End TCOMP.

(** ** An instance of empty layer *)
Section NULL.
  Context {K: Type}.

  Definition null_lts : lts li_null (li_c @ K) unit :=
    {|
      genvtype := unit;
      Smallstep.step _ := fun s1 t s2 => False;
      Smallstep.initial_state := fun q s => False;
      Smallstep.at_external := fun s q => False;
      Smallstep.after_external := fun s1 r s2 => False;
      Smallstep.final_state := fun s r => False;
      Smallstep.globalenv := tt
    |}.

  Definition null_layer sk : Smallstep.semantics li_null (li_c @ K) :=
    {|
      Smallstep.skel := sk;
      Smallstep.state := unit;
      Smallstep.activate _ := null_lts;
      Smallstep.footprint _ := False;
    |}.

End NULL.

Lemma null_layer_fsim {K1 K2: Type} sk1 sk2 sk:
  forward_simulation 1 1 (tensor_comp_semantics' (@null_layer K1 sk1) (@null_layer K2 sk2) sk) (null_layer sk).
Proof.
  constructor. econstructor.
  - reflexivity.
  - intros. intuition. inv H. destruct x; inv H0.
  - instantiate (1 := fun _ _ _ => _). cbn beta.
    intros se1 se2 w Hse Hse1. inv Hse.
    apply forward_simulation_step; cbn.
    + intros. inv H0. destruct i; inv H1;inv H; inv H.
    + intros. inv H0. destruct i. inv H1. inv H0. inv H1. inv H0.
    + intros. inv H0. destruct i. inv H1. inv H0. inv H1. inv H0.
    + intros. inv H. destruct i.
      * destruct s. destruct s'. inv H1. inv H.
      * destruct s. destruct s'. inv H1. inv H.
  - apply well_founded_ltof.
    Unshelve. intros. exact True.
Qed.
