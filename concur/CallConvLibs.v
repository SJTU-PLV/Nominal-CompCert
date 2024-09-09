Require Import LanguageInterface CallconvAlgebra Invariant.
Require Import CKLR Inject InjectFootprint Extends.
Require Import Mach Locations Conventions Asm.
Require Import ValueAnalysis.
Require Import Allocproof Lineartyping Asmgenproof0.
Require Import Maps Stacklayout.

Require Import CallconvBig CallConvAlgebra VCompBig.
Require Import StackingproofC CallConv.
Import GS.

Section TRANS.

  Context {li1 li2} (cc : LanguageInterface.callconv li1 li2).
  Variable L1 : semantics li1 li1.
  Variable L2 : semantics li2 li2.

  Hypothesis OLDSIM: Smallstep.forward_simulation cc cc L1 L2.

  Lemma NEWSIM: GS.forward_simulation cc L1 L2.
  Proof.
    intros. inv OLDSIM. constructor.
    inv X. econstructor; eauto.
    intros. exploit fsim_lts0; eauto.
    intros FPros.
    instantiate (1:= fun se1 se2 wB gw idx s1 s2 =>  fsim_match_states0 se1 se2 wB idx s1 s2).
    simpl.
    inv FPros. econstructor; eauto.
    - intros. exploit fsim_match_final_states0; eauto.
      intros [r2 [A B]]. exists r2. exists tt. intuition auto. reflexivity. reflexivity.
    - intros. exploit fsim_match_external0; eauto.
    intros (w0 & q2 & A & B & C).
    exists w0, q2. intuition auto. reflexivity.
    eapply H4; eauto.
  Qed.

End TRANS.


(*    
Program Definition cc_id {li : language_interface} : callconv li li :=
  {|
    ccworld := unit;
    ccworld_world := world_unit;
    match_senv w := eq;
    match_query w := eq;
    match_reply w := eq;
  |}.
 *)

Lemma cctrans_id_1 {li1 li2 : language_interface} : forall (cc: callconv li1 li2),
    cctrans (cc_compose cc_id cc) cc.
Proof.
  constructor.
  econstructor. instantiate (1:= fun w1 w => eq (snd w1) w).
  - econstructor. repeat apply conj; eauto.
    + instantiate (1:= (se1,(tt,w2))). econstructor; eauto. reflexivity.
    + econstructor; eauto. split. reflexivity. auto.
    + reflexivity.
    + intros. destruct wp1 as [xx wp2']. simpl in H1, H2.  subst wp2'.
      destruct wp1' as [xy wp2'']. destruct H3. destruct H2. simpl in *.
      eexists. split; eauto. split; eauto.
      destruct H4 as [r1' [A B]]. subst. auto.
  - red. intros. destruct w1 as [se' [tt w2]].
    simpl in H. destruct H as [Heq H]. subst se'.
    simpl in H0. destruct H0 as [q1' [Heq H0]]. subst q1'.
    destruct wp1 as [tt' wp2'].
    destruct H1. simpl in H1, H3. simpl in H2. subst wp2'.
    exists w2. intuition auto.
    exists (tt, wp2'). intuition auto.
    split; auto. exists r1. split. econstructor; eauto. auto.
Qed.

Lemma cctrans_id_2 {li1 li2 : language_interface} : forall (cc: callconv li1 li2),
    cctrans (cc_compose cc cc_id) cc.
Proof.
  constructor.
  econstructor. instantiate (1:= fun w1 w => eq (fst w1) w).
  - econstructor. repeat apply conj; eauto.
    + instantiate (1:= (se2,(w2,tt))). econstructor; eauto. reflexivity.
    + exists q2. split; auto. econstructor; eauto.
    + reflexivity.
    + intros. destruct wp1 as [wp2' xx]. simpl in H1, H2.  subst wp2'.
      destruct wp1' as [wp2'' xy]. destruct H3. destruct H2. simpl in *.
      eexists. split; eauto. split; eauto.
      destruct H4 as [r1' [A B]]. subst. auto.
  - red. intros. destruct w1 as [se' [w2 tt]].
    simpl in H. destruct H as [H Heq]. subst se'.
    simpl in H0. destruct H0 as [q2' [H0 Heq]]. subst q2'.
    destruct wp1 as [wp2' tt'].
    destruct H1. simpl in H1, H3. simpl in H2. subst wp2'.
    exists w2. intuition auto.
    exists (wp2',tt). intuition auto. split; simpl. auto. reflexivity.
    exists r2. split. auto. econstructor; eauto.
Qed.

Lemma oldfsim_newfsim_ccid : forall {li : language_interface} (L1 L2: semantics li li),
    Smallstep.forward_simulation LanguageInterface.cc_id LanguageInterface.cc_id L1 L2 ->
    forward_simulation cc_id L1 L2.
Proof.
  intros. generalize (NEWSIM LanguageInterface.cc_id L1 L2).
  intro. apply H0. auto.
Qed.


(** Q : Can we (Should we) define the new [injp] as [cklr] instead of several different
        callconvs for different interfaces ?
      
    1. Compare the [c_injp] defined above v.s. [cc_c injp]. 
       Can we define another version of cc_c based on another [cklr] equipped with acci and acce?
    2. Try []

  *)

Lemma compose_id_new_injp_1 {li1 li2: language_interface} : forall (cc: callconv li1 li2) L1 L2 L3,
    Smallstep.forward_simulation 1 1 L1 L2 ->
    forward_simulation cc L2 L3 ->
    forward_simulation cc L1 L3.
Proof.
  intros.
  rewrite <- cctrans_id_1.
  eapply st_fsim_vcomp; eauto. eapply oldfsim_newfsim_ccid; eauto.
Qed.

Lemma compose_id_new_injp_2 {li1 li2: language_interface} : forall (cc: callconv li1 li2) L1 L2 L3,
    forward_simulation cc L1 L2 ->
    Smallstep.forward_simulation 1 1 L2 L3 ->
    forward_simulation cc L1 L3.
Proof.
  intros. rewrite <- cctrans_id_2.
  eapply st_fsim_vcomp; eauto. eapply oldfsim_newfsim_ccid; eauto.
Qed.

(** Algebratic properties *)


Require Import Extends.

(** c_ext cannot be defined using cc_unit_world because [cc_c] uses <> diamond constructer for match_reply*)
Program Definition c_ext : callconv li_c li_c := cc_c ext.
(*  {|
    ccworld := unit;
    ccworld_world := world_unit;
    match_senv w := eq;
    match_query w := cc_c_query ext w;
    match_reply w := cc_c_reply ext w;
  |}.
*)
Lemma cctrans_ext_comp : cctrans (cc_compose c_ext c_ext) c_ext.
Proof.
  constructor.
  econstructor. instantiate (1:= fun _ _ => True).
  - red. intros. inv H.  inv H0. simpl in H, H1, H2.
    exists (se2, (tt,tt)). intuition auto. econstructor; eauto. reflexivity. reflexivity.
    exists (cq vf1 sg vargs1 m1). split.
    econstructor; eauto. reflexivity. simpl.
    generalize dependent vargs1.
    induction 1. constructor. constructor; eauto. reflexivity.
    simpl. eapply Mem.extends_refl.
    econstructor; eauto.
    exists tt. intuition auto. destruct wp1'. simpl in H6. 
    destruct H6 as [r1' [[? [A0 A]][? [B0 B]]]]. inv A. inv B. simpl in *.
    exists tt. split. eauto.
    econstructor; simpl; eauto.
    eapply val_inject_id. eapply Val.lessdef_trans; eapply val_inject_id; eauto.
    eapply Mem.extends_extends_compose; eauto.
  - red. intros. destruct w1 as [se' [w11 w12]]. inv H. inv H3. inv H4. inv H2.
    inv H0. inv H. inv H0. inv H2. simpl in H9, H11, H12, H , H3, H4.
    exists tt. intuition auto. reflexivity. constructor.
    constructor; simpl; eauto.
    eapply val_inject_id. eapply Val.lessdef_trans; eapply val_inject_id; eauto.
    eapply CallConv.val_inject_lessdef_list_compose. eauto.
    eapply (ext_lessdef_list tt). eauto.
    eapply Mem.extends_extends_compose; eauto.
    exists (tt,tt). split. reflexivity. split. exists r1. destruct H2 as [? [X H2]]. inv H2. simpl in *.
    split. exists tt. split. eauto.
    econstructor; simpl; eauto. eapply val_inject_id.
    eapply Val.lessdef_refl.
    eapply Mem.extends_refl.
    exists tt. split. eauto.
    econstructor; eauto. auto.
Qed.


Lemma oldfsim_newfsim_ext_c : forall  (L1 L2: semantics li_c li_c),
    Smallstep.forward_simulation (cc_c ext) (cc_c ext) L1 L2 ->
    forward_simulation c_ext L1 L2.
Proof.
  intros. red in H. inv H. constructor.
  inv X. econstructor; eauto.
  intros. exploit fsim_lts0; eauto.
  intros FPros.
  instantiate (1:= fun se1 se2 wB gw idx s1 s2 =>  fsim_match_states0 se1 se2 wB idx s1 s2).
  simpl.
  inv FPros. econstructor; eauto.
  - intros. exploit fsim_match_final_states0; eauto.
    intros [r2 [A B]]. exists r2. exists tt. intuition auto. reflexivity. reflexivity.
  - intros. exploit fsim_match_external0; eauto.
    intros (w0 & q2 & A & B & C).
    exists w0, q2. intuition auto. reflexivity.
    eapply H4; eauto.
Qed.


(** Big Problem : bring lower cklrs to C level *)

Program Instance lens_injp_locset : Lens (signature * injp_world) injp_world :=
  {
    get := snd;
    set := fun w wp => (fst w, wp);
  }.

Program Instance injp_world_id_l : World (signature * injp_world) :=
    {
      w_state := injp_world;
      w_lens := lens_injp_locset;
      w_acci := injp_acci;
      w_acce := injp_acce;
      w_acci_trans := injp_acci_preo;
    }.
(* cc_locset *)
Program Definition locset_injp : callconv li_locset li_locset :=
  {|
    ccworld := signature * injp_world;
    ccworld_world := injp_world_id_l;
    match_senv w := CKLR.match_stbls injp (snd w);
    match_query w := cc_locset_query injp (fst w) (snd w);
    match_reply w := cc_locset_reply injp (fst w) (snd w);    
  |}.
Next Obligation.
  inv H. inv H0. auto.
Qed.
Next Obligation.
  intros. inv H. erewrite <- Genv.valid_for_match; eauto.
Qed.

Infix "@" := GS.cc_compose (at level 30, right associativity).

Inductive match12_stacking : injp_world -> (injp_world * unit) -> Prop :=
|match12_stacking_intro : forall f m1 m2 Hm Hm' t,
    match12_stacking (injpw f m1 m2 Hm) ((injpw f m1 m2 Hm'),t).

Lemma Stackingtrans : cctrans (cc_stacking_injp) (locset_injp @ cc_locset_mach).
Proof.
  constructor.
  econstructor. instantiate (1:= match12_stacking).
  - red. intros w2 se1 se2 q1 q2 Hse Hq.
    destruct w2 as [se [[sig wx] [sig' rs]]].
    destruct Hse as [Hse1 Hse2]. simpl in Hse1, Hse2. inv Hse2.
    destruct Hq as [q1' [Hq1 Hq2]]. inv Hq2. simpl in Hq1. inv Hq1.
    inv H9. simpl in H4, Hse1, H8.
    set (rs2 := (make_locset rs lmw_m lmw_sp)).
    inv H5.
    + (*no stack-allocated arguments *)
      red in H.
    exists (stkw injp (injpw f m1 m_ Hm) sig' ls1 lmw_sp m_).
    repeat apply conj; eauto.
    -- econstructor; eauto. admit. (*to de added in LM*)
       intros. apply H8. constructor. constructor; eauto with mem.
       split. intro. extlia. intros. exfalso. admit.
       intros. rewrite H in H0. inv H0. extlia.
    -- simpl. constructor.
    -- intros. inv H0. simpl in H1, H3.
       exists (wp1', tt). simpl. repeat apply conj; eauto.
       simpl.  inv H1. constructor; eauto.
       simpl. inv H2. constructor; eauto.
       inv H3.
       set (ls2' := make_locset rs2' m2' lmw_sp).
       exists (lr ls2' m2'). split.
       constructor; eauto. constructor.
       constructor; eauto.

       red in H8.
       intros. specialize (H8 (R r)) as HH.
       exploit HH. constructor.
       intro VINJ1.
       exploit H16. eauto. intro VINJ2. simpl in VINJ1.
       admit. (** need fix, about callee-save regs *)
       eauto with mem.
       intros. rewrite H in H0. inv H0. extlia.
    +
      assert (Hm' : Mem.inject f m1 lmw_m). admit.
      (** It is correct *)
      simpl in Hse1.
     exists (stkw injp (injpw f m1 lmw_m Hm') sig' ls1 (Vptr sb sofs) lmw_m).
     repeat apply conj; eauto.
     -- inv Hse1. constructor; eauto. erewrite <- Mem.support_free; eauto.
     -- econstructor; eauto. admit. (*to de added in LM*)
       intros. apply H8. constructor. constructor; eauto with mem.
       split. intros. do 2 eexists. split. reflexivity. split.
       eapply Mem.free_range_perm. eauto. eauto.
       intros. exploit H2; eauto. intros [v Hv]. exists v. split. auto.
       exploit H8. eapply loc_external_arg. eauto.
       simpl. setoid_rewrite Hv. simpl. auto.
       intros. red. intros. inv H3.
       intro. exploit Mem.perm_inject. eauto. apply Hm1. eauto.
       replace (ofs - delta + delta) with ofs by lia.
       intros.
       eapply Mem.perm_free_2; eauto. 
    -- simpl. admit. (** match should contain [args_removed] *)
    -- intros. inv H3. simpl in H5, H11.
       exists (wp1', tt). simpl. repeat apply conj; eauto.
       ++ admit. (** todo *)
       ++ admit. (** todo *)
       ++ admit. (** todo *)
  - red. intros. simpl in wp1, wp2, w1.
    inv H0. inv H. cbn in H1. inv H2.
    (* Compute ccworld (locset_injp @ cc_locset_mach). *)
    exists (se2, (sg, (injpw f m1 m2 Hm), (lmw sg rs2 m2 sp2))).
    repeat apply conj; eauto.
    + simpl. inv H1. constructor; eauto.
    + simpl. auto.
    + simpl. auto.
    + simpl. set (ls2 := make_locset rs2 m2 sp2).
      exists (lq vf2 sg ls2 m2). split.
      constructor; eauto. red. intros; simpl; eauto.
      inv H. eauto. inv H6. admit. 
      constructor.
      constructor; eauto. admit.
      (** seems to be right here *)
    + intros. simpl in H. destruct wp2' as [wp2' a]. destruct a. destruct H.
      inv H2. simpl in H. exists wp2'. simpl in H0.
      simpl. split. auto. split. admit.
      destruct wp2'. constructor.
Admitted.
(** Seems can be proved? *)

Definition mach_ext := cc_mach ext.
Definition l_ext := cc_locset ext.

(** We have to change cc_locset_mach. But the problem is how? *)
Lemma LM_trans_ext : cctrans (cc_locset_mach @ mach_ext) (l_ext @ cc_locset_mach).
Proof.
  constructor. econstructor.
  - red. intros [se' [[sg a] [sg' rs]]] se1 se2 q1 q2.
    intros [Hse1 Hse2] [q1' [Hq1 Hq2]].
    simpl in a. inv Hse1. inv Hse2. inv Hq1. inv Hq2.
    simpl in H1, H, H0.
    (* Compute (ccworld (cc_locset_mach @ mach_ext)). *)
    exists (se2,((lmw sg rs lmw_m vf2),tt)).
    repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. constructor.
    + Abort.

(** * Lemmas about CL cc_c_locset *)


(** Ad-hoc locmap constructions for CL transformations *)
Definition Locmap_set_list (rs : Locmap.t) (vals: list val) (pairs : list (rpair loc)) := rs.

Definition set (l : loc) (v : val) (m: Locmap.t) (p: loc):=
  if Loc.eq l p then v else m p.

Definition setpairloc (p : rpair loc) (v: val) (m: Locmap.t) :=
  match p with
  |One l => set l v m
  |Twolong hi lo => set lo (Val.loword v) (set hi (Val.hiword v) m)
  end.

Lemma setpairloc_gsspair : forall l v m m',
    setpairloc (One l) v m = m' ->
    Locmap.getpair (One l) m'= v.
Proof.
  intros.
  - simpl in *. subst m'. unfold set. rewrite pred_dec_true; auto.
Qed.

Lemma setpairloc_gss : forall l v m m',
    setpairloc (One l) v m = m' ->
    m' l = v.
Proof.
  intros.
  - simpl in *. subst m'. unfold set. rewrite pred_dec_true; auto.
Qed.

Lemma setpairloc_gso1 : forall l v m m' l',
    setpairloc (One l) v m = m' ->
    l <> l' ->
    Locmap.getpair (One l') m' = Locmap.getpair (One l') m.
Proof.
  intros.
  - simpl in *. subst m'. unfold set. rewrite pred_dec_false; auto.
Qed.

Lemma setpairloc_gso : forall l v m m' l',
    setpairloc (One l) v m = m' ->
    l <> l' ->
    m' l' = m l'.
Proof.
  intros.
  - simpl in *. subst m'. unfold set. rewrite pred_dec_false; auto.
Qed.

(**  Prove that the locations  [loc_arguments sg] is norepet *)
Lemma notin_loc_arguments_win64_y : forall l x y1 y2 t,
    y1 < y2 ->
    ~ In (One (S Outgoing y1 t)) (loc_arguments_win64 l x y2).
Proof.
  induction l; intros.
  - simpl. auto.
  - simpl. repeat destr.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
Qed.

Lemma notin_loc_arguments_win64_x_int : forall tys r1 r2 ireg y,
    list_nth_z int_param_regs_win64 r1 = Some ireg ->
    r1 < r2 ->
    ~ In (One (R ireg)) (loc_arguments_win64 tys r2 y).
Proof.
  induction tys; intros.
  - simpl. auto.
  - cbn -[list_nth_z]. repeat destr.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
Qed.

Lemma notin_loc_arguments_win64_x_float : forall tys r1 r2 ireg y,
    list_nth_z float_param_regs_win64 r1 = Some ireg ->
    r1 < r2 ->
    ~ In (One (R ireg)) (loc_arguments_win64 tys r2 y).
Proof.
    induction tys; intros.
  - simpl. auto.
  - cbn -[list_nth_z]. repeat destr.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
Qed.

Lemma notin_loc_arguments_elf64_y : forall l x y z1 z2 t,
    z1 < z2 ->
    ~ In (One (S Outgoing z1 t)) (loc_arguments_elf64 l x y z2).
Proof.
  induction l; intros.
  - simpl. auto.
  - simpl. repeat destr.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
Qed.

Lemma notin_loc_arguments_elf64_x_int : forall tys r1 r2 ireg y z,
    list_nth_z int_param_regs_elf64 r1 = Some ireg ->
    r1 < r2 ->
    ~ In (One (R ireg)) (loc_arguments_elf64 tys r2 y z).
Proof.
  induction tys; intros.
  - simpl. auto.
  - cbn -[list_nth_z]. repeat destr.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
Qed.

Lemma notin_loc_arguments_elf64_y_float : forall tys r1 r2 ireg x z,
    list_nth_z float_param_regs_elf64 r1 = Some ireg ->
    r1 < r2 ->
    ~ In (One (R ireg)) (loc_arguments_elf64 tys x r2 z).
Proof.
   induction tys; intros.
  - simpl. auto.
  - cbn -[list_nth_z]. repeat destr.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
Qed.

Lemma loc_arguments_norepet sg:
  list_norepet (loc_arguments sg).
Proof.
  unfold loc_arguments. replace Archi.ptr64 with true by reflexivity.
  destruct Archi.win64.
* cut (forall x y, list_norepet (loc_arguments_win64 (sig_args sg) x y)).
  - eauto.
  - induction (sig_args sg); cbn -[list_nth_z].
    + constructor.
    + intros x y.
      destruct a, (list_nth_z) eqn: Hz;
        cbn; constructor; eauto;
        try (apply notin_loc_arguments_win64_y; lia);
        try (eapply notin_loc_arguments_win64_x_int; try apply Hz; lia);
      try (eapply notin_loc_arguments_win64_x_float; try apply Hz; lia).
* cut (forall x y z, list_norepet (loc_arguments_elf64 (sig_args sg) x y z)).
  - intros. apply (H 0 0 0).
  - induction sig_args; cbn -[list_nth_z].
    + constructor.
    + intros x y z.
      destruct a, list_nth_z eqn: Hz; cbn; constructor; eauto;
        try (apply notin_loc_arguments_elf64_y; lia);
        try (eapply notin_loc_arguments_elf64_x_int; try apply Hz; lia);
      try (eapply notin_loc_arguments_elf64_y_float; try apply Hz; lia).
Qed.

Lemma CL_trans_ext : cctrans (cc_c_locset @ l_ext) (c_ext @ cc_c_locset).
Proof.
  constructor.
  econstructor. instantiate (1:= eq).
  - red. intros [se' [x sg]] se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]].
    simpl in x,sg. destruct x. inv Hse2. inv Hse1. inv Hq2. inv Hq1.
    cbn in H4, H5, H6.
    exists (se2,(sg,(sg,tt))). repeat apply conj; eauto.
    + constructor; eauto. constructor. constructor.
    + generalize (loc_arguments_always_one sg). intro Hone.
      generalize (loc_arguments_norepet sg). intro Hnorepet.
      assert (exists rs1, (fun p : rpair loc => Locmap.getpair p rs1) ## (loc_arguments sg) = vargs1 /\
                       forall l : loc, loc_external sg l -> Val.inject inject_id (rs1 l) (rs l)).
      { generalize dependent vargs1.
        induction loc_arguments; cbn; intros.
        - inv H5. exists rs. split. auto. intros. reflexivity.
        - inv H5. exploit IHl; eauto. intros.
          exploit Hone. right. eauto. auto.
          inv Hnorepet. auto.
          exploit Hone. left. reflexivity. intros [la Hla].
          intros [rs1 [A B]].
          exists (setpairloc a v rs1). split.
          + simpl. f_equal.  rewrite Hla.
          erewrite setpairloc_gsspair; eauto.
          rewrite <- A.
          apply map_ext_in. intros. exploit Hone; eauto.
          right. eauto. intros [la0 Hla0]. rewrite Hla0.
          erewrite setpairloc_gso1; eauto. rewrite Hla. reflexivity.
          inv Hnorepet. congruence.
          + intros. rewrite Hla.
            destruct (Loc.eq la l0).
            * subst. erewrite setpairloc_gss; eauto.
            * erewrite setpairloc_gso. 2: eauto. eauto. auto.
      }
      destruct H as [rs1 [A B]].
      exists (lq vf1 sg rs1 m1). split. econstructor; eauto.
      constructor; eauto.
    + intros. exists (tt,tt). split. simpl. auto.
      split. auto. inv H1. destruct wp1'. inv H0.
      destruct H2 as [r1' [Hr1 Hr2]]. inv Hr1. inv Hr2.
      destruct H0. inv H2. simpl in H11, H13. clear H H1 H3 H8 H0.
      eexists. simpl. split. exists tt. split. reflexivity.
      constructor; simpl; eauto.
      2: {constructor. reflexivity. }
      red in H11. simpl.
      destruct (loc_result_always_one sg) as [r Hr]. rewrite Hr in *. cbn in *.
      apply H11. auto.
  - red. intros [? ?] [? ?] [se [sg [sg' t]]]. simpl in w,w0,w1,w2,sg,sg',t.
    intros se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]] A1 A2.  inv Hse1. inv Hse2.
    inv Hq1. inv Hq2. simpl in H3, H5,H6. clear A1 A2.
    (* Compute (ccworld (c_ext @ cc_c_locset)). *)
    exists (se2,(tt,sg)). repeat apply conj; eauto. reflexivity. reflexivity.
    + constructor; eauto. constructor. constructor.
    + eexists. split. econstructor; eauto.
      2: { econstructor. reflexivity. }
      simpl. red in H5.
      pose proof (loc_arguments_external sg).
      induction loc_arguments; cbn in *; auto.
      constructor; auto.
      apply locmap_getpair_inject.
      assert (forall_rpair (loc_external sg) a) by eauto.
      destruct a; cbn in *; intuition auto.
    + intros r1 r2 [a b] AC1 Hr. destruct Hr as [r1' [[x [Hx Hr1]] Hr2]].
      inv Hr1. inv Hr2. simpl in H, H0.
      exists (tt,tt). split. reflexivity. split.
      set (rs'' := Locmap.setpair (loc_result sg) vres1 (rs')).
      econstructor. split. econstructor. instantiate (1:= rs'').
      unfold rs''. simpl.
      destruct (loc_result_always_one sg) as [r ->].
      cbn. rewrite Locmap.gss. reflexivity.
      econstructor. split. reflexivity. constructor; eauto.
      red. intros.  unfold rs''.
      destruct (loc_result_always_one sg) as [r' Hr]. rewrite Hr in *. cbn in *.
      intuition subst. rewrite Locmap.gss. auto.
      destruct a. destruct b. reflexivity.
Qed.

Lemma CL_trans_injp : cctrans (cc_c_locset @ locset_injp) (c_injp @ cc_c_locset).
Proof.
  constructor.
  econstructor. instantiate (1:= fun w1 w2 => snd w1 = fst w2).
  - red. intros [se' [wp sg]] se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]].
    simpl in sg. inv Hse2. inv Hse1. inv Hq2. inv Hq1. inv H9.
    cbn in H7, H8.
    (* Compute (ccworld (cc_c_locset @ locset_injp)). *)
    exists (se1,(sg,(sg,(injpw f m0 m Hm)))). repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. constructor; eauto.
    + generalize (loc_arguments_always_one sg). intro Hone.
      generalize (loc_arguments_norepet sg). intro Hnorepet.
      assert (exists rs1, (fun p : rpair loc => Locmap.getpair p rs1) ## (loc_arguments sg) = vargs1 /\
                       forall l : loc, loc_external sg l -> Val.inject f (rs1 l) (rs l)).
      { generalize dependent vargs1.
        induction loc_arguments; cbn; intros.
        - inv H8. exists (Locmap.init Vundef).
          split. auto. intros. constructor.
        - inv H8. exploit IHl; eauto. intros.
          exploit Hone. right. eauto. auto.
          inv Hnorepet. auto.
          exploit Hone. left. reflexivity. intros [la Hla].
          intros [rs1 [A B]].
          exists (setpairloc a v rs1). split.
          + simpl. f_equal.  rewrite Hla.
          erewrite setpairloc_gsspair; eauto.
          rewrite <- A.
          apply map_ext_in. intros. exploit Hone; eauto.
          right. eauto. intros [la0 Hla0]. rewrite Hla0.
          erewrite setpairloc_gso1; eauto. rewrite Hla. reflexivity.
          inv Hnorepet. congruence.
          + intros. rewrite Hla.
            destruct (Loc.eq la l0).
            * subst. erewrite setpairloc_gss; eauto.
            * erewrite setpairloc_gso. 2: eauto. eauto. auto.
      }
      destruct H2 as [rs1 [A B]].
      exists (lq vf1 sg rs1 m0). split. econstructor; eauto.
      constructor; eauto. constructor.
    + intros. destruct wp1 as [a wp1]. simpl in a, wp1.
      destruct wp2 as [wp2 b]. simpl in b, wp2. inv H2.
      destruct wp1' as [a' wp1']. simpl in H6. subst wp2.
      destruct H3. simpl in H2,H3. destruct H4. simpl in H4,H6.
      exists (wp1',tt). split. simpl. split. auto. auto. split.
      destruct b. split; auto.
      destruct H5 as [r1' [Hr1 Hr2]]. inv Hr1. inv Hr2. inv H13.
      simpl in H5, H11. subst wp1'. simpl in *.
      eexists. simpl. split. 
      constructor; simpl; eauto.
      2: {constructor. reflexivity. }
      red in H11. simpl.
      destruct (loc_result_always_one sg) as [r Hr]. rewrite Hr in *. cbn in *.
      apply H11. auto.
  - red. intros [? ?] [? ?] [se [sg [sg' t]]]. simpl in w,w0,w1,w2,sg,sg',t.
    intros se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]] A1 A2.  inv Hse1. inv Hse2. inv A2. destruct A1. simpl in H4, H5, H2. inv H3. simpl in H6.
    inv H6.
    inv Hq1. inv Hq2. inv H11. simpl in H8, H10.
    (* Compute (ccworld (c_injp @ cc_c_locset)). *)
    exists (se2,((injpw f m m3 Hm),sg)). repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. constructor; eauto.
    + eexists. split. econstructor; eauto.
      2: { econstructor. }
      2: { econstructor. reflexivity. }
      simpl. red in H10.
      pose proof (loc_arguments_external sg).
      induction loc_arguments; cbn in *; auto.
      constructor; auto.
      apply locmap_getpair_inject.
      assert (forall_rpair (loc_external sg) a) by eauto.
      destruct a; cbn in *; intuition auto.
    + intros r1 r2 [a b] AC1 Hr. simpl in AC1. destruct AC1.
      simpl in H2, H3. clear H3.
      destruct Hr as [r1' [Hr1 Hr2]].
      inv Hr1. inv Hr2. simpl in H6. inv H6. simpl in H3.
      exists (tt,(injpw f0 m1' m2' Hm4)). split. split; auto.
      simpl. inv H2. constructor; auto. split. simpl.
      set (rs'' := Locmap.setpair (loc_result sg) vres1 (rs')).
      exists (lr rs'' m1'). split.
      econstructor. 
      unfold rs''. simpl.
      destruct (loc_result_always_one sg) as [r ->].
      cbn. rewrite Locmap.gss. reflexivity.
      econstructor. simpl.
      red. intros.  unfold rs''.
      destruct (loc_result_always_one sg) as [r' Hr]. rewrite Hr in *. cbn in *.
      intuition subst. rewrite Locmap.gss. auto.
      constructor. reflexivity.
Qed.

(** TODO: wt_loc through CL *)



