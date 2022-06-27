Require Import AST Linking Coqlib.
Require Ctypes.
Import Maps.

Class LinkerProp {A} (L: Linker A) : Prop :=
  {
    link_lub x y z a:
      linkorder x a -> linkorder y a ->
      link x y = Some z -> linkorder z a;

    link_monotonic x y z a b c:
      linkorder x a -> linkorder y b ->
      link x y = Some z -> link a b = Some c ->
      linkorder z c;
  }.

Transparent Ctypes.Linker_fundef.
Instance fundef_linker_prop F: LinkerProp (Ctypes.Linker_fundef F).
Proof.
  split.
  - intros * Hx Hy Hz.
    inv Hx; inv Hy.
    + destruct a. inv Hz.
      cbn in *. destruct (_ && _ && _ && _). inv Hz.
      constructor. inv Hz.
    + inv Hz. constructor.
    + inv Hz. constructor.
    + cbn in *. destruct (_ && _ && _ && _). inv Hz.
      constructor. inv Hz.
  - intros * Hx Hy Hz Hc.
    inv Hx; inv Hy.
    + rewrite Hz in Hc. inv Hc. apply linkorder_refl.
    + destruct a. inv Hc.
      destruct e; inv Hc.
      cbn in *. destruct (_ && _ && _ && _). inv Hz.
      constructor. inv Hz.
    + destruct b. inv Hc.
      destruct e; inv Hc.
      cbn in *. destruct (_ && _ && _ && _). inv Hz.
      constructor. inv Hz.
    + inv Hc.
Qed.
Opaque Ctypes.Linker_fundef.

Transparent Linker_varinit.
Transparent Linker_vardef.
Transparent Linker_def.
Lemma link_varinit_either x y z:
  link_varinit x y = Some z -> x = z \/ y = z.
Proof with (solve [ now left | now right ]).
  intros H. unfold link_varinit in H.
  destruct (classify_init x).
  - inv H...
  - destruct (classify_init y).
    + inv H...
    + destruct zeq. inv H... inv H.
    + destruct zeq. inv H... inv H.
  - destruct (classify_init y).
    + inv H...
    + destruct zeq. inv H... inv H.
    + inv H.
Qed.

Lemma link_varinit_inv_l x y:
  link_varinit x y = Some x ->
  y = nil \/ y = AST.Init_space (AST.init_data_list_size x) :: nil.
Proof.
  intros H. unfold link_varinit in H.
  destruct (classify_init x) eqn: Hx.
  - inv H. now left.
  - destruct (classify_init y) eqn: Hy.
    + now left.
    + right. destruct zeq; congruence.
    + right. destruct zeq; try congruence.
      (* this is funny *)
      subst. inversion H.
      rewrite H1 at 1. rewrite H1 at 1. reflexivity.
  - destruct (classify_init y) eqn: Hy.
    + now left.
    + right. destruct zeq; congruence.
    + inv H.
Qed.

Lemma link_varinit_inv_r x y:
  link_varinit y x = Some x ->
  y = nil \/ y = AST.Init_space (AST.init_data_list_size x) :: nil.
Proof.
  intros H. unfold link_varinit in H.
  destruct (classify_init y) eqn: Hy.
  - now left.
  - destruct (classify_init x) eqn: Hx.
    + inv H.
    + right. destruct zeq; congruence.
    + right. f_equal.
      destruct zeq; congruence.
  - destruct (classify_init x) eqn: Hx.
    + inv H. now left.
    + right. destruct zeq; try congruence.
      subst. inversion H.
      rewrite H1 at 1. rewrite H1 at 1. reflexivity.
    + inv H.
Qed.

Instance varinit_linker_prop: LinkerProp Linker_varinit.
Proof.
  split.
  - intros * Hx Hy Hz.
    eapply link_varinit_either in Hz.
    destruct Hz; subst; eauto.
  - intros * Hx Hy Hz Hc.
    exploit link_varinit_either. exact Hz. intros X.
    exploit link_varinit_either. exact Hc. intros Y.
    destruct X, Y; subst; eauto.
    + exploit link_varinit_inv_l. exact Hz. intros X.
      exploit link_varinit_inv_r. exact Hc. intros Y.
      destruct X, Y; subst.
      * inv Hx; now constructor.
      * cbn in Hc. destruct c.
        -- inv Hc.
        -- inv Hx.
           ++ constructor. easy. reflexivity.
           ++ constructor.
           ++ constructor. easy. cbn.
              rewrite Z.add_0_r. symmetry. apply Z.max_l.
              pose proof (AST.init_data_list_size_pos c).
              pose proof (AST.init_data_size_pos i). omega.
      * inv Hx; now constructor.
      * cbn in Hc. destruct c.
        -- inv Hc.
        -- inv Hx.
           ++ constructor. easy. reflexivity.
           ++ constructor.
           ++ constructor. easy. cbn.
              rewrite Z.add_0_r. symmetry. apply Z.max_l.
              pose proof (AST.init_data_list_size_pos c).
              pose proof (AST.init_data_size_pos i). omega.
    + exploit link_varinit_inv_r. exact Hz. intros X.
      exploit link_varinit_inv_l. exact Hc. intros Y.
      destruct X, Y; subst.
      * inv Hy; now constructor.
      * destruct c.
        -- inv Hc.
        -- inv Hy.
           ++ constructor. easy. reflexivity.
           ++ constructor.
           ++ constructor. easy. cbn.
              rewrite Z.add_0_r. symmetry. apply Z.max_l.
              pose proof (AST.init_data_list_size_pos c).
              pose proof (AST.init_data_size_pos i). omega.
      * inv Hy; now constructor.
      * destruct c.
        -- inv Hx. easy.
        -- inv Hy.
           ++ constructor. easy. reflexivity.
           ++ constructor.
           ++ constructor. easy. cbn.
              rewrite Z.add_0_r. symmetry. apply Z.max_l.
              pose proof (AST.init_data_list_size_pos c).
              pose proof (AST.init_data_size_pos i). omega.
Qed.

Instance vardef_linker_prop {V} {LV: Linker V}:
  LinkerProp LV -> LinkerProp (@Linker_vardef _ LV).
Proof.
  split.
  - intros * Hx Hy Hz.
    inv Hx. inv Hy. cbn in Hz.
    unfold link_vardef in Hz. cbn in Hz.
    destruct link eqn: X; try congruence.
    destruct link_varinit eqn: Y; try congruence.
    rewrite !eqb_reflx in Hz. cbn in Hz. inv Hz.
    constructor.
    + eapply link_lub. 3: eauto. all: eauto.
    + eapply link_lub. 3: eauto. all: eauto.
  - intros * Hx Hy Hz Hc.
    inv Hx. inv Hy. cbn in Hz, Hc.
    unfold link_vardef in Hz, Hc. cbn in Hz, Hc.
    destruct (link info1 info0) eqn: Hx;
      destruct (link info2 info3) eqn: Hy; try congruence.
    destruct (link_varinit i1 i0) eqn: Hu;
      destruct (link_varinit i2 i3) eqn: Hv; try congruence.
    destruct (eqb ro ro0); destruct (eqb vo vo0); cbn in *; try congruence.
    inv Hz. inv Hc. constructor.
    + eapply link_monotonic. 3-4: eauto. all: eauto.
    + eapply link_monotonic. 3-4: eauto. all: eauto.
Qed.

Instance def_linker_prop {F V} {LF: Linker F} {LV: Linker V}:
  LinkerProp LF -> LinkerProp LV -> LinkerProp (@Linker_def _ _ LF LV).
Proof.
  split.
  - intros * Hx Hy Hz.
    inv Hx; inv Hy.
    + cbn in Hz. destruct link eqn: X; try congruence. inv Hz.
      constructor. eapply link_lub. 3: eauto. all: eauto.
    + cbn in Hz. destruct link_vardef eqn: X; try congruence. inv Hz.
      constructor. eapply link_lub. 3: eauto. all: eauto.
  - intros * Hx Hy Hz Hc.
    inv Hx; inv Hy.
    + cbn in Hz, Hc.
      destruct (link fd1 fd0) eqn: X;
        destruct (link fd2 fd3) eqn: Y; try congruence.
      inv Hz. inv Hc. constructor. eapply link_monotonic.
      3-4: eauto. all: eauto.
    + inv Hz.
    + inv Hz.
    + cbn in Hz, Hc.
      destruct (link_vardef v1 v0) eqn: X;
        destruct (link_vardef v2 v3) eqn: Y; try congruence.
      inv Hz. inv Hc. constructor. eapply link_monotonic.
      3-4: eauto. all: eauto.
Qed.
Opaque Linker_varinit.
Opaque Linker_vardef.
Opaque Linker_def.

Instance unit_linker_prop:
  LinkerProp Linker_unit.
Proof. split; intros; constructor. Qed.

Instance prog_linker_prop {F V} {LF: Linker F} {LV: Linker V}:
  LinkerProp LF -> LinkerProp LV -> LinkerProp (@Linker_prog _ _ LF LV).
Proof.
  split.
  - intros * Hx Hy Hz.
  eapply link_prog_inv in Hz as (H1 & H2 & H3).
  repeat apply conj.
    + subst. cbn. apply Hx.
    + subst. cbn.
      apply incl_app. apply Hx. apply Hy.
    + intros * X.
      subst. rewrite prog_defmap_elements in X.
      rewrite PTree.gcombine in X. 2: reflexivity.
      unfold link_prog_merge in X.
      destruct Hx as (X1 & X2 & X3).
      destruct Hy as (Y1 & Y2 & Y3).
      destruct (AST.prog_defmap x) ! id eqn: A;
        destruct (AST.prog_defmap y) ! id eqn: B.
      * specialize (X3 _ _ A) as (gdx & Hx1 & Hx2 & Hx3).
        specialize (Y3 _ _ B) as (gdy & Hy1 & Hy2 & Hy3).
        rewrite Hx1 in Hy1. inv Hy1.
        exists gdy. split; eauto. split.
        ++ eapply link_lub. 3: eauto. all: eauto.
        ++ intros C. specialize (Hx3 C). specialize (Hy3 C). subst.
           specialize (H2 _ _ _ A B). destruct H2.
           specialize (X2 _ H2). easy.
      * specialize (X3 _ _ A) as (gdx & Hx1 & Hx2 & Hx3). inv X.
        exists gdx. repeat apply conj; eauto.
      * specialize (Y3 _ _ B) as (gdy & Hy1 & Hy2 & Hy3). inv X.
        exists gdy. repeat apply conj; eauto.
      * easy.
  - intros * Hx Hy Hz Hc.
    eapply link_prog_inv in Hz as (Z1 & Z2 & Z3).
    eapply link_prog_inv in Hc as (C1 & C2 & C3). subst. cbn in *.
    destruct Hx as (X1 & X2 & X3).
    destruct Hy as (Y1 & Y2 & Y3).
    repeat apply conj.
    + cbn. congruence.
    + intros X HX. apply in_app.
      apply in_app in HX as [|]; [ left | right ]; eauto.
    + intros *. setoid_rewrite prog_defmap_elements. cbn. intros X.
      rewrite PTree.gcombine in X. 2: reflexivity.
      unfold link_prog_merge in X.
      destruct (AST.prog_defmap x) ! id eqn: A;
        destruct (AST.prog_defmap y) ! id eqn: B.
      * specialize (X3 _ _ A) as (gdx & Hx1 & Hx2 & Hx3).
        specialize (Y3 _ _ B) as (gdy & Hy1 & Hy2 & Hy3).
        specialize (C2 _ _ _ Hx1 Hy1) as (H1 & H2 & (gd & Hgd)).
        exists gd. repeat apply conj.
        -- rewrite PTree.gcombine. 2: reflexivity.
           unfold link_prog_merge. rewrite Hx1. rewrite Hy1. assumption.
        -- eapply link_monotonic. 3-4: eauto. all: eauto.
        -- intros Hab. rewrite in_app in Hab.
           apply Classical_Prop.not_or_and in Hab as [Ha Hb]. easy.
      * specialize (X3 _ _ A) as (gdx & Hx1 & Hx2 & Hx3).
        destruct (AST.prog_defmap b) ! id eqn : C.
        -- specialize (C2 _ _ _ Hx1 C) as (H1 & H2 & (gd & Hgd)).
           exists gd. repeat apply conj.
           ++ rewrite PTree.gcombine. 2: reflexivity.
              unfold link_prog_merge. rewrite Hx1. rewrite C. exact Hgd.
           ++ inv X. eapply linkorder_trans; eauto.
              eapply link_linkorder in Hgd. apply Hgd.
           ++ intros Hab. rewrite in_app in Hab.
              apply Classical_Prop.not_or_and in Hab as [Ha Hb]. easy.
        -- exists gdx. repeat apply conj.
           ++ rewrite PTree.gcombine. 2: reflexivity.
              unfold link_prog_merge. rewrite Hx1. rewrite C. reflexivity.
           ++ inv X. exact Hx2.
           ++ inv X. intros Hab. rewrite in_app in Hab.
              apply Classical_Prop.not_or_and in Hab as [Ha Hb]. eauto.
      * specialize (Y3 _ _ B) as (gdy & Hy1 & Hy2 & Hy3).
        destruct (AST.prog_defmap a) ! id eqn : C.
        -- specialize (C2 _ _ _ C Hy1) as (H1 & H2 & (gd & Hgd)).
           exists gd. repeat apply conj.
           ++ rewrite PTree.gcombine. 2: reflexivity.
              unfold link_prog_merge. rewrite C. rewrite Hy1. exact Hgd.
           ++ inv X. eapply linkorder_trans; eauto.
              eapply link_linkorder in Hgd. apply Hgd.
           ++ intros Hab. rewrite in_app in Hab.
              apply Classical_Prop.not_or_and in Hab as [Ha Hb]. easy.
        -- exists gdy. repeat apply conj.
           ++ rewrite PTree.gcombine. 2: reflexivity.
              unfold link_prog_merge. rewrite C. rewrite Hy1. reflexivity.
           ++ inv X. exact Hy2.
           ++ inv X. intros Hab. rewrite in_app in Hab.
              apply Classical_Prop.not_or_and in Hab as [Ha Hb]. eauto.
      * inv X.
Qed.
