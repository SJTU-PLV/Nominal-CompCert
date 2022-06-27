From Coq Require Import
     Relations
     RelationClasses
     List.
From compcert.compcertox Require Import
     Lifting AbRel.
From compcert.lib Require Import
     Coqlib Maps.
From compcert.common Require Import
     LanguageInterface
     AST Events Globalenvs
     Smallstep Linking
     SmallstepLinking
     Memory Values
     CallconvAlgebra
     CategoricalComp
     FlatComp.
From compcert.cfrontend Require Import
     Clight Ctypes.
Require Coq.omega.Omega.

(* A module is a list of compilation units. Specifically, they are Clight
   programs at this time. Note that in the layer library the modules are
   organized as mapping from identifiers to vars or functions. A module like
   that is transformed into a Clight program by [make_program] because separate
   compilation is not supported. However, here a module is nothing but a list of
   programs and the semantics is given by the horizontal composition of the
   Clight programs *)
(* Notation cmodule := (list Clight.program). *)
Record cmodule : Type :=
  mk_cmodule {
      cmod_progs :> list Clight.program;
      cmod_skel : AST.program unit unit;
      cmod_skel_order :
      Forall
        (fun (p: Clight.program) => linkorder (AST.erase_program p) cmod_skel) cmod_progs;
  }.

Program Definition cmod_of_program (p: Clight.program) :=
  {|
    cmod_progs := p :: nil;
    cmod_skel := AST.erase_program p;
  |}.
Next Obligation.
  constructor. apply linkorder_refl. constructor.
Qed.
Coercion cmod_of_program : Clight.program >-> cmodule.

(** The index of the program family *)
Fixpoint pos (M: list Clight.program): Type :=
  match M with
  | nil => Empty_set
  | p :: ps => unit + pos ps
  end.

(** Turn a module into a program family *)
Definition ref (M: list Clight.program) (k: pos M): Smallstep.semantics li_c li_c.
Proof.
  induction M as [| p ps].
  - inv k.
  - destruct k.
    + refine (Clight.semantics2 p).
    + apply IHps. apply p0.
Defined.

Definition semantics (M: cmodule): Smallstep.semantics li_c li_c :=
  SmallstepLinking.semantics' (ref M) (cmod_skel M).

Require Import FunctionalExtensionality.
Require Import FinFun.

Global Instance cmod_progrom_sem M: ProgramSem (semantics M).
Proof.
  split.
  - intros. inv H. destruct H0 as (?&?&?&?).
  split; eauto. eexists; split; eauto.
  cbn. eexists; eauto.
  - intros. inv H. intros [Hq [x [Hx1 Hx2]]].
    destruct Hx1 as [j1 Hj]. apply (H1 j1).
    split; auto. exists x; split; auto.
Qed.

Program Definition cmod_app M N : option cmodule :=
  match Linking.link (cmod_skel M) (cmod_skel N) with
  | Some sk =>
      Some {|
          cmod_progs := cmod_progs M ++ cmod_progs N;
          cmod_skel := sk;
        |}
  | None => None
  end.
Next Obligation.
  rename Heq_anonymous into Hsk. apply symmetry in Hsk.
  apply link_linkorder in Hsk as [].
  apply Forall_forall. intros *. rewrite in_app.
  intros [HM|HN].
  - eapply linkorder_trans. 2: exact H.
    pose proof (cmod_skel_order M). rewrite Forall_forall in H1.
    now apply H1.
  - eapply linkorder_trans. 2: exact H0.
    pose proof (cmod_skel_order N). rewrite Forall_forall in H1.
    now apply H1.
Qed.

Section APP.

  Context M N MN (H: cmod_app M N = Some MN).

  Lemma cmod_app_progs: cmod_progs MN = cmod_progs M ++ cmod_progs N.
  Proof.
    revert H. unfold cmod_app.
    generalize (eq_refl (A:=option (AST.program unit unit)) (x:= link (cmod_skel M) (cmod_skel N))).
    generalize (link (cmod_skel M) (cmod_skel N)) at 1 3.
    intros [sk|].
    - intros. inv H. easy.
    - easy.
  Qed.

  Lemma cmod_app_skel: link (cmod_skel M) (cmod_skel N) = Some (cmod_skel MN).
  Proof.
    revert H. unfold cmod_app.
    generalize (eq_refl (A:=option (AST.program unit unit)) (x:= link (cmod_skel M) (cmod_skel N))).
    generalize (link (cmod_skel M) (cmod_skel N)) at 1 3.
    intros [sk|].
    - intros. inv H. easy.
    - easy.
  Qed.

  Let L := fun b => match b with | true => (semantics M) | false => (semantics N) end.
  Let J := fun b => match b with | true => pos M | false => pos N end.
  Definition Lij: forall (b: bool), J b -> Smallstep.semantics li_c li_c.
  Proof.
    intros [|] j.
    - refine (ref M j).
    - refine (ref N j).
  Defined.

  Let SK := fun b => match b with | true => cmod_skel M | false => cmod_skel N end.
  Lemma Leq: L = (fun i => semantics' (fun j => Lij i j) (SK i)).
  Proof.
    apply functional_extensionality. intros [|]; reflexivity.
  Qed.

  Definition F: pos (M ++ N) -> {b : bool & J b}.
  Proof.
    intros x. induction (cmod_progs M) as [| p ps].
    - refine (existT _ false x).
    - cbn in *. destruct x.
      + refine (existT _ true (inl u)).
      + specialize (IHps p0) as [[|] pp].
        * refine (existT _ true (inr pp)).
        * refine (existT _ false pp).
  Defined.

  Definition G: {b : bool & J b} -> pos (M ++ N).
  Proof.
    intros [[|] j].
    - induction (cmod_progs M) as [| p ps].
      + inv j.
      + cbn. destruct j.
        * refine (inl u).
        * refine (inr (IHps p0)).
    - induction (cmod_progs M) as [| p ps].
      + refine j.
      + refine (inr _). apply IHps. exact j.
  Defined.

  Lemma FG_bij: Bijective F.
  Proof.
    exists G. split; intros x.
    - unfold F, G. cbn.
      induction (cmod_progs M) as [| p ps].
      + reflexivity.
      + cbn in *. destruct x.
        * reflexivity.
        * cbn in *. specialize (IHps p0).
          remember (list_rect (fun l : list Clight.program => pos (l ++ N) -> _) _ _ ps p0) as lr.
          destruct lr as [b pb]. destruct b.
          -- f_equal. apply IHps.
          -- f_equal. apply IHps.
    - unfold F, G. cbn. destruct x as [[|] j].
      + cbn in *. induction (cmod_progs M) as [| p ps].
        * cbn in *. inv j.
        * cbn in *. destruct j.
          -- constructor.
          -- specialize (IHps p0). cbn in *.
             rewrite IHps. constructor.
      + cbn in *. induction (cmod_progs M) as [| p ps].
        * cbn in *. constructor.
        * cbn in *. rewrite IHps. constructor.
  Qed.

  Lemma LFeq: (fun i : pos (M ++ N) => (fun p : {x : bool & J x} => Lij (projT1 p) (projT2 p)) (F i)) = ref (M ++ N).
  Proof.
    apply functional_extensionality. intros x.
    unfold F, Lij.
    induction (cmod_progs M) as [| p ps].
    - cbn in *. reflexivity.
    - cbn in *. destruct x.
      + reflexivity.
      + cbn in *. specialize (IHps p0).
        remember (list_rect (fun l : list Clight.program => pos (l ++ N) -> _) _ _ ps p0) as lr.
        destruct lr as [b pb]. destruct b.
        * cbn in *. apply IHps.
        * cbn in *. apply IHps.
  Qed.

  Lemma cmodule_app_simulation:
    SmallstepLinking.semantics' L (cmod_skel MN) ≤ semantics MN.
  Proof.
    rewrite Leq.
    etransitivity. apply level_simulation1.
    etransitivity. eapply bijective_map_simulation1 with (F := F).
    apply FG_bij. unfold semantics.
    rewrite cmod_app_progs. rewrite <- LFeq.
    reflexivity.
  Qed.

  Section CAT_APP.
    Context `{!CategoricalLinkable (semantics M) (semantics N)}.

    Lemma cmodule_categorical_comp_simulation:
      comp_semantics' (semantics M) (semantics N) (cmod_skel MN) ≤ semantics MN.
    Proof.
      etransitivity.
      apply categorical_compose_approximation; typeclasses eauto.
      fold L. rewrite Leq.
      etransitivity. apply level_simulation1.
      etransitivity. eapply bijective_map_simulation1 with (F := F).
      apply FG_bij. unfold semantics.
      rewrite cmod_app_progs. rewrite <- LFeq.
      reflexivity.
    Qed.
  End CAT_APP.

  Section FLAT_APP.
    Context `{!FlatLinkable L}.

    Lemma cmodule_flat_comp_simulation:
      flat_comp_semantics' L (cmod_skel MN) ≤ semantics MN.
    Proof.
      etransitivity.
      apply flat_composition_approximation;
        [ intros [|]; typeclasses eauto
        | eauto | decide equality ].
      rewrite Leq.
      fold @SmallstepLinking.semantics.
      etransitivity. apply level_simulation1.
      etransitivity. eapply bijective_map_simulation1 with (F := F).
      apply FG_bij. unfold semantics.
      rewrite cmod_app_progs. rewrite <- LFeq.
      reflexivity.
    Qed.
  End FLAT_APP.

End APP.

Lemma cmodule_abrel {Ks Kf} (R: abrel Ks Kf) M:
  forward_simulation R R (semantics M @ Ks) (semantics M @ Kf).
Proof.
  eapply open_fsim_ccref. apply cc_compose_id_left.
  unfold flip. apply cc_compose_id_left.
  eapply compose_forward_simulations.
  apply lift_horizontal_comp1.

  eapply open_fsim_ccref. apply cc_compose_id_right.
  unfold flip. apply cc_compose_id_right.
  eapply compose_forward_simulations.
  2: { apply lift_horizontal_comp2. }

  apply semantics_simulation'.
  - intros. induction (cmod_progs M) as [| p ps]; try easy.
    destruct i.
    + cbn. apply clight_sim.
    + apply IHps.
  - cbn. destruct M as [ps sk Hsk].
    intros i. cbn in *. induction ps as [| p ps].
    + inv i.
    + cbn in *. destruct i.
      * rewrite -> Forall_forall in Hsk. apply Hsk. apply in_eq.
      * apply IHps.
        rewrite -> Forall_forall in *.
        intros x Hx. apply Hsk. now apply in_cons.
Qed.

Require Import Integers.

(* FIXME: move to Clight *)
Global Instance clight_program_sem p: ProgramSem (semantics2 p).
Proof.
  split.
  - intros. inv H. clear -H0. unfold valid_query; cbn.
    unfold Genv.find_funct in H0.
    destruct vf; try congruence.
    destruct Ptrofs.eq_dec; try congruence.
    split. intros X. discriminate X.
    subst. unfold Genv.find_funct_ptr in H0.
    destruct Genv.find_def eqn: Hdef; try congruence.
    destruct g; try congruence. inv H0.
    unfold globalenv in Hdef; cbn -[Genv.find_def] in *.
    rewrite Genv.find_def_spec in Hdef.
    destruct Genv.invert_symbol eqn: Hse; try congruence.
    exists i. split. unfold footprint_of_program.
    rewrite Hdef. auto.
    unfold Genv.symbol_address.
    apply Genv.invert_find_symbol in Hse.
    rewrite Hse. auto.
  - intros. inv H. unfold valid_query. cbn.
    intros [? (i & Hi & Hse)].
    unfold Genv.find_funct in H0.
    destruct vf; try congruence.
    destruct Ptrofs.eq_dec; try congruence.
    unfold Genv.find_funct_ptr in H0.
    destruct Genv.find_def eqn: Hdef; try congruence.
    destruct g eqn: Hg; try congruence. inv H0.
    unfold globalenv in Hdef. cbn -[Genv.find_def] in *.
    rewrite Genv.find_def_spec in Hdef.
    destruct Genv.invert_symbol eqn: Hs; try congruence.
    apply Genv.invert_find_symbol in Hs.
    unfold Genv.symbol_address in Hse.
    destruct (Genv.find_symbol se i) eqn: Hxe; try congruence.
    inv Hse. exploit Genv.find_symbol_injective.
    apply Hs. apply Hxe. intros ->.
    unfold footprint_of_program in Hi. rewrite Hdef in Hi.
    subst f. cbn in *. discriminate Hi.
Qed.

Section LINKABLE.
  Definition program_vertical_linkable (p1 p2: Clight.program) :=
    forall id f ef ts t cc,
      (prog_defmap p1) ! id = Some (Gfun (Internal f)) ->
      (prog_defmap p2) ! id = Some (Gfun (External ef ts t cc)) -> False.

  Definition cmodule_vertical_linkable (M N: cmodule) :=
    forall pm pn, In pm M -> In pn N -> program_vertical_linkable pm pn.

  Definition program_horizontal_linkable (p1 p2: Clight.program) :=
    program_vertical_linkable p1 p2 /\ program_vertical_linkable p2 p1.

  Definition cmodule_horizontal_linkable (M N: cmodule) :=
    forall pm pn, In pm M -> In pn N -> program_horizontal_linkable pm pn.

  Lemma cmodule_program M idx:
    exists p, In p M /\ ref M idx = Clight.semantics2 p.
  Proof.
    induction M; [ easy | ].
    destruct idx.
    - eexists; split. now left. easy.
    - specialize (IHM p) as (x & Hx & Hp).
      exists x. split. now right. apply Hp.
  Qed.

  Lemma cmodule_vertical_linkable_cond M N:
    cmodule_vertical_linkable M N -> CategoricalLinkable (semantics M) (semantics N).
  Proof.
    intros H se s q Hext Hvq.
    destruct Hvq as [Hq (id & (i & Hfp) & Hsymbol)].
    destruct (cmodule_program M i) as (pm & Hpm & Hm). rewrite Hm in Hfp.
    inversion Hext as [j ? ? ? Hx Hvq]. subst. clear Hext Hvq.
    destruct (cmodule_program N j) as (pn & Hpn & Hn).
    remember (ref N j) as pref. clear Heqpref. subst pref.
    cbn in Hx. inv Hx. cbn -[prog_defmap] in *.
    unfold footprint_of_program in Hfp.
    destruct ((prog_defmap pm) ! id) eqn: Hp1; try easy.
    destruct g; try easy. destruct f0; try easy.
    specialize (H pm pn Hpm Hpn). eapply H. eauto.
    unfold Genv.symbol_address in Hsymbol.
    destruct Genv.find_symbol eqn:Hb; try congruence.
    unfold Genv.find_funct in H0. subst.
    destruct Ptrofs.eq_dec; try congruence.
    unfold Genv.find_funct_ptr in H0.
    destruct Genv.find_def eqn:Hf in H0; try congruence.
    destruct g; try congruence. inv H0.
    rewrite Genv.find_def_spec in Hf.
    destruct Genv.invert_symbol eqn:Hb'; try congruence.
    apply Genv.invert_find_symbol in Hb'.
    assert (id = i0) by (eapply Genv.genv_vars_inj; eauto).
    subst. rewrite Hf. subst f. reflexivity.
  Qed.

  Lemma program_categorical_linkable_cond (p1 p2: Clight.program):
    (forall id f ef ts t cc,
        (prog_defmap p1) ! id = Some (Gfun (Internal f)) ->
        (prog_defmap p2) ! id = Some (Gfun (External ef ts t cc)) ->
        False) ->
    CategoricalLinkable (semantics p1) (semantics p2).
  Proof.
    intros. apply cmodule_vertical_linkable_cond.
    unfold cmodule_vertical_linkable, program_vertical_linkable.
    intros. inv H0; try easy. inv H1; try easy.
    eapply H; eauto.
  Qed.

  Lemma cmodule_horizontal_linkable_cond M N:
    cmodule_horizontal_linkable M N ->
    FlatLinkable (fun (i: bool) => if i then semantics M else semantics N).
  Proof.
    intros H. unfold FlatLinkable.
    intros [|] [|] * Ht Hvq; auto; exfalso.
    - assert (Hl: CategoricalLinkable (semantics N) (semantics M)).
      { apply cmodule_vertical_linkable_cond. intros p1 p2 Hp1 Hp2. apply H; eauto. }
      exploit Hl; eauto.
    - assert (Hl: CategoricalLinkable (semantics M) (semantics N)).
      { apply cmodule_vertical_linkable_cond. intros p1 p2 Hp1 Hp2. specialize (H p1 p2). apply H; eauto. }
      exploit Hl; eauto.
  Qed.

End LINKABLE.

(* Deal with dependent rewriting *)
Section XXX.

  Variable A : Type.
  Variable B : Type.
  Variable comp_b : B -> B -> option B.
  Variable prop_ab : list A -> B -> Prop.

  Hypothesis comp_prop:
    forall a1 a2 b1 b2 b,
      prop_ab a1 b1 -> prop_ab a2 b2 ->
      comp_b b1 b2 = Some b -> prop_ab (a1 ++ a2) b.

  Record R :=
    mk_R {
        R_a : list A;
        R_b : B;
        R_prop : prop_ab R_a R_b;
      }.

  Program Definition comp_r (r1 r2: R) : option R :=
    match comp_b (R_b r1) (R_b r2)  with
    | Some b =>
        Some {|
          R_a := R_a r1 ++ R_a r2;
          R_b := b;
        |}
    | None => None
    end.
  Next Obligation.
    eapply comp_prop; eauto.
    apply R_prop. apply R_prop.
  Qed.

  Lemma comp_r_a (r1 r2 r: R):
    comp_r r1 r2 = Some r ->
    R_a r = R_a r1 ++ R_a r2.
  Proof.
    unfold comp_r.
    generalize (@eq_refl (option B) (comp_b (R_b r1) (R_b r2))).
    generalize (comp_b (R_b r1) (R_b r2)) at 1 3.
    intros [o|].
    - intros H X. inv X. reflexivity.
    - intros H X. inv X.
  Qed.

End XXX.
