Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Integers.
Require Import Memory.
Require Import Smallstep.
Require Import Inject InjectFootprint.
Require Import Callconv ForwardSim.

(** * Test1: compose injp' ⋅ injp' = injp' *)

(*
L1 <=injp'->injp' L2 ->
L2 <=injp'->injp' L3 ->
L1 <= injp'-> injp' L3
*)

Variable cons_se2 : Genv.symtbl -> meminj -> Genv.symtbl.

Section CONSTRUCT_SE2.

Context (sk1 sk2 sk3 : AST.program unit unit) (se1 se3: Genv.symtbl).
Context (f : meminj).

Hypotheses COMP : Genv.skel_symtbl_compatible  sk1 sk3 se1 se3.
Hypotheses MS : Genv.match_stbls' f se1 se3.
Hypotheses LE1 : Genv.skel_le sk2 sk1.
Hypotheses LE2 : Genv.skel_le sk3 sk2.

Definition se2 := cons_se2 se1 f.
(* Basiclly remove all the ids and blocks that are unmapped by f from se1 to se3 from se1*)

Lemma se2_symb: forall id, Genv.find_symbol se2 id =
                match Genv.find_symbol se1 id with
                |Some b => if f b then Some b else None
                |None => None
                end.
Admitted.

Lemma se2_info: forall b, Genv.find_info se2 b =
                       if f b then Genv.find_info se1 b else None.
Admitted.

Lemma se2_sup : forall b,
    sup_In b (Genv.genv_sup se2) <->
    sup_In b (Genv.genv_sup se1) /\ (exists b', f b = Some (b', 0)).
Admitted.

Lemma se2_public : forall id, Genv.public_symbol se2 id= Genv.public_symbol se1 id.
Admitted.

Theorem MS1 : Genv.match_stbls' (meminj_dom f) se1 se2.
Proof.
  inversion MS. unfold meminj_dom. constructor; intros; eauto.
  - eapply se2_public.
  - intros. unfold meminj_dom in H0.
    destruct (f b1); inv H0; eauto.
  - intros. exists b2. apply se2_sup in H.
    destruct H as [A [b B]].
    rewrite B. eauto.
  - destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H.
    setoid_rewrite se2_symb. split; intro.
    setoid_rewrite H. rewrite Hb. reflexivity.
    destruct Genv.find_symbol eqn:F2. destruct (f b); inv H.
    eauto. inv H.
  - destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H.
    setoid_rewrite se2_info. rewrite Hb. eauto.
  - destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H.
    split; intro. exploit mge_dom'; eauto. intro. subst.
    rewrite se2_sup. split; eauto.
    rewrite se2_sup in H. destruct H. eauto.
Qed.

Theorem MS2 : Genv.match_stbls' f se2 se3.
Proof.
  inversion MS. constructor; intros; eauto.
  - rewrite se2_public. eauto.
  - eapply mge_dom'; eauto. rewrite se2_sup in H. destruct H. eauto.
  - split; intro. setoid_rewrite se2_symb in H0.
    destruct (Genv.find_symbol se1 id) eqn: F1; try congruence.    
    destruct (f b) eqn: INJ; try congruence. inv H0. eapply mge_symb'; eauto.
    eapply mge_symb' in H0; eauto. setoid_rewrite se2_symb.
    setoid_rewrite H0. rewrite H. reflexivity.
  - setoid_rewrite se2_info. rewrite H. eapply mge_info'; eauto.
  - split; intro. rewrite se2_sup in H0. destruct H0. eapply mge_separated'; eauto.
    erewrite <- mge_separated' in H0; eauto.
    exploit mge_dom'; eauto. intro. subst.
    rewrite se2_sup. split; eauto.
Qed.

Theorem LE: Genv.skel_le sk3 sk1.
Proof. etransitivity; eauto. Qed.

Lemma Valid2: Genv.valid_for sk2 se2.
  red. intros.
  (*Seems wrong here*)

Abort.





Lemma skel_le_defnames : forall sk1 sk2 id,
    Genv.skel_le sk2 sk1 ->
    In id (AST.prog_defs_names sk2) ->
    In id (AST.prog_defs_names sk1).
Admitted.

Theorem COMP1 : Genv.skel_symtbl_compatible sk1 sk2 se1 se2.
Proof.
  destruct COMP as [V1 [V3 [RE MAIN]]].
  split. eauto. split. admit.
  split. intros.
  - exploit RE; eauto.
    destruct (Genv.find_symbol se2 id) as [b|] eqn:F2; try congruence.
    rewrite se2_symb in F2.
    destruct (Genv.find_symbol se1 id) eqn:F1; try congruence.
    destruct (f b0) as [[tb d]|] eqn: INJ; try congruence. inv F2.
    inv MS. eapply mge_symb' in F1 as F3; eauto. setoid_rewrite F3. congruence.
    intro. eapply skel_le_defnames; eauto.
  - intro. apply MAIN. red. red in H.
    destruct H as [b [A B]].
    exists b. split. auto.
    destruct (Genv.find_symbol se3 (AST.prog_main sk1)) eqn:F3m; eauto.
    inversion MS. exploit mge_img'; eauto. eapply Genv.genv_symb_range; eauto.
    intros [b2 INJ].
    eapply mge_symb' in F3m as F1m; eauto.
    rewrite se2_symb in B. setoid_rewrite F1m in B. rewrite INJ in B.
    congruence.
Admitted.

End CONSTRUCT_SE2.





Section COMPOSE_FORWARD_SIMULATIONS.

Context (L1: semantics li_c li_c) (L2: semantics li_c li_c) (L3: semantics li_c li_c).


Definition id_world (w:injp_world) :=
  match w with
    injpw f m1 m2 Hm => injpw (meminj_dom f) m1 m1 (mem_inject_dom f m1 m2 Hm)
  end.


Lemma compose_fsim_components':
  fsim_components' (cc_c' injp') (cc_c' injp') L1 L2 ->
  fsim_components' (cc_c' injp') (cc_c' injp') L2 L3 ->
  fsim_components' (cc_c' injp') (cc_c' injp') L1 L3.
Proof.
  intros [index order match_states Hsk props order_wf].
  intros [index' order' match_states' Hsk' props' order_wf'].
  set (ff_index := (index' * index)%type).
  set (ff_order := lex_ord (clos_trans _ order') order).
  set (ff_match_states :=
         fun se1 se3 (w: injp_world) (i: ff_index) (s1: state L1) (s3: state L3) =>
           exists s2,
             match_states se1 se1 (id_world w) (snd i) s1 s2 /\
             match_states' se1 se3 w (fst i) s2 s3).
  apply Forward_simulation' with ff_order ff_match_states.
  3: { unfold ff_order. auto using wf_lex_ord, wf_clos_trans. }
  1: { etransitivity; eauto. }
  intros se1 se2 w Hse2 Hcompat. cbn in *.
  assert (Hse1: injp_match_stbls' (id_world w) se1 se1).
  { clear - Hse2.
    inv Hse2. constructor; eauto.
    inv H. constructor; intros; eauto.
    - unfold meminj_dom in H2. destruct (f b1); try discriminate
    
  }
  assert (Hse1: Genv.valid_for (skel L1) se1).
  {}
  Search Genv.skel_le.
  { rewrite <- Hsk. eapply match_senv_valid_for; eauto. }
  constructor.
- (* valid query *)
  intros q1 q3 (q2 & Hq12 & Hq23).
  erewrite fsim_match_valid_query by eauto.
  eapply fsim_match_valid_query; eauto.
- (* initial states *)
  intros q1 q3 s1 (q2 & Hq12 & Hq23) Hs1.
  edestruct (@fsim_match_initial_states liA1) as (i & s2 & A & B); eauto.
  edestruct (@fsim_match_initial_states liA2) as (i' & s3 & C & D); eauto.
  exists (i', i); exists s3; split; auto. exists s2; auto.
- (* final states *)
  intros. cbn. destruct H as (s3 & A & B).
  edestruct (@fsim_match_final_states liA1) as (r2 & Hr2 & Hr12); eauto.
  edestruct (@fsim_match_final_states liA2) as (r3 & Hr3 & Hr23); eauto.
- (* external states *)
  intros. destruct H as [s3 [A B]].
  edestruct (@fsim_match_external liA1) as (w12 & q2 & Hq2 & Hq12 & Hw12 & Hk12); eauto.
  edestruct (@fsim_match_external liA2) as (w23 & q3 & Hq3 & Hq23 & Hw23 & Hk23); eauto.
  exists (se2, w12, w23), q3. cbn; repeat apply conj; eauto.
  intros r1 r3 s1' (r2 & Hr12 & Hr23) Hs1'.
  edestruct Hk12 as (i12' & s2' & Hs2' & Hs12'); eauto.
  edestruct Hk23 as (i23' & s3' & Hs3' & Hs23'); eauto.
  exists (i23', i12'), s3'. split; auto. exists s2'; auto.
- (* simulation *)
  intros. destruct H0 as [s3 [A B]]. destruct i as [i2 i1]; simpl in *.
  edestruct (@fsim_simulation' liA1) as [(i1' & s3' & C & D) | (i1' & C & D & E)]; eauto.
+ (* L2 makes one or several steps. *)
  edestruct (@simulation_plus liA2) as [(i2' & s2' & P & Q) | (i2' & P & Q & R)]; eauto.
* (* L3 makes one or several steps *)
  exists (i2', i1'); exists s2'; split. auto. exists s3'; auto.
* (* L3 makes no step *)
  exists (i2', i1'); exists s2; split.
  right; split. subst t; apply star_refl. red. left. auto.
  exists s3'; auto.
+ (* L2 makes no step *)
  exists (i2, i1'); exists s2; split.
  right; split. subst t; apply star_refl. red. right. auto.
  exists s3; auto.
Qed.

Lemma compose_forward_simulations:
  forward_simulation ccA12 ccB12 L1 L2 ->
  forward_simulation ccA23 ccB23 L2 L3 ->
  forward_simulation (ccA12 @ ccA23) (ccB12 @ ccB23) L1 L3.
Proof.
  intros [X] [Y]. constructor.
  apply compose_fsim_components; auto.
Qed.

End COMPOSE_FORWARD_SIMULATIONS.
