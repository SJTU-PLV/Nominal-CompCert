(** Preliminary experiments about incorporating state encapsulation into
  CompCert languages *)

From compcert Require Import
     AST Coqlib Maps Values Integers Errors Events
     LanguageInterface Smallstep Globalenvs Memory Floats.
From compcert Require Import
     CategoricalComp.
From compcert.compcertox Require Import
     TensorComp Lifting.
From coqrel Require Import RelClasses.

(** * State Encapsulation of CompCert LTS *)

(** ** Preliminaries *)
Record PSet : Type :=
  mk_pset {
      pset_type :> Type;
      pset_init : pset_type;
    }.
Definition pset_prod (A: PSet) (B: PSet) :=
  {|
    pset_type := A * B;
    pset_init := (pset_init A, pset_init B);
  |}.
Infix "*" := pset_prod.
Definition pset_unit :=
  {|
    pset_type := unit;
    pset_init := tt
  |}.

Record ReflTranRel (X: Type) :=
  {
    rel :> X -> X -> Prop;
    rel_refl : Reflexive rel;
    rel_tran : Transitive rel;
  }.
Existing Instance rel_refl.
Existing Instance rel_tran.

(* A generalized version of Kripke world *)
Record world :=
  mk_world {
      w_type :> PSet;
      (* internal transition step *)
      w_int_step : ReflTranRel w_type;
      (* external transition step *)
      w_ext_step : ReflTranRel w_type;
    }.
Arguments w_int_step {_}.
Arguments w_ext_step {_}.
Infix "*->" := w_int_step (at level 60, no associativity).
Infix ":->" := w_ext_step (at level 60, no associativity).
Program Definition pset_world (p: PSet) :=
  {|
    w_type := p;
    w_int_step := {| rel s t := True; |};
    w_ext_step := {| rel s t := s = t |};
  |}.
Next Obligation. intros x y z. intros; subst; easy. Qed.
Program Definition world_prod (u: world) (v: world) :=
  {|
    w_type := u * v;
    w_int_step := {| rel '(u, v) '(u', v') := u *-> u' /\ v *-> v' |};
    w_ext_step := {| rel '(u, v) '(u', v') := u :-> u' /\ v :-> v' |};
  |}.
Next Obligation. intros x. destruct x. split; reflexivity. Qed.
Next Obligation.
  intros [a b] [c d] [e f] [A B] [C D].
  split; etransitivity; eauto.
Qed.
Next Obligation. intros x. destruct x. split; reflexivity. Qed.
Next Obligation.
  intros [a b] [c d] [e f] [A B] [C D].
  split; etransitivity; eauto.
Qed.
Infix "*" := world_prod: world_scope.
Delimit Scope world_scope with world.
Bind Scope world_scope with world.

(** ** Semantics with Encapsulation *)
Record esemantics {liA liB} := {
    pstate : PSet;              (** persistent state *)
    esem :> semantics liA (liB @ pstate)
  }.
Arguments esemantics : clear implicits.

Infix "+->" := esemantics (at level 70).

(** *** Composition *)
Definition comp_esem {liA liB liC} (L1: liB +-> liC) (L2: liA +-> liB) : option (liA +-> liC) :=
  match comp_semantics $(L1 @ pstate L2) L2 with
  | Some L =>
      Some {|
        pstate := pstate L1 * pstate L2;
        esem := L;
      |}
  | None => None
  end.

(** *** Construction *)

(* TODO: move this to TensorComp.v and add instance priority *)
Instance li_func_comp {liA liB liC} (F: LiFunc liA liB) (G: LiFunc liB liC): LiFunc liA liC.
Proof. split; intros; apply F; apply G; easy. Defined.

Definition encap_store {K: PSet} {liA liB} (L: liA +-> liB@K) : liA +-> liB :=
  {|
    pstate := pstate L * K;
    esem := $L
  |}.

Instance li_func_unit {liA}: LiFunc liA (liA@unit).
Proof. split; intros; apply X. Defined.

Definition encap_fbk {liA liB} (L: semantics liA liB) : liA +-> liB :=
  {|
    pstate := pset_unit;
    esem := $L;
  |}.

(** ** Simulations *)
Set Implicit Arguments.

Module ST.

  Record callconv {li1 li2} :=
    mk_callconv {
      ccworld : world;
      match_query : ccworld -> query li1 -> query li2 -> Prop;
      match_reply : ccworld -> reply li1 -> reply li2 -> Prop;
    }.
  Arguments callconv: clear implicits.

  Program Definition callconv_lift {li1 li2}
          (cc: callconv li1 li2) (U V: PSet) : callconv (li1@U) (li2@V) :=
    {|
      ccworld := (ccworld cc * (pset_world U) * (pset_world V))%world;
      match_query '(w, u, v) '(q1, uq) '(q2, vq) :=
        match_query cc w q1 q2 /\ u = uq /\ v = vq;
      match_reply '(w, u, v) '(q1, uq) '(q2, vq) :=
        match_reply cc w q1 q2 /\ u = uq /\ v = vq;
    |}.

  Section FSIM.

    Context {liA1 liA2} (ccA: callconv liA1 liA2).
    Context {liB1 liB2} (ccB: callconv liB1 liB2).
    Context (wA: ccworld ccA) (wB: ccworld ccB)
            (winv: ccworld ccA -> ccworld ccB -> Prop).
    Context {state1 state2: Type}.

    (* There is supposed to be a relation between the wB and wA, which is
       re-established at the end *)
    Record fsim_properties
           (L1: lts liA1 liB1 state1) (L2: lts liA2 liB2 state2)
           (index: Type) (order: index -> index -> Prop)
           (match_states: ccworld ccA -> ccworld ccB -> index -> state1 -> state2 -> Prop) :=
      {
        fsim_match_initial_states:
          forall q1 q2 s1 wB', wB :-> wB' -> match_query ccB wB' q1 q2 -> initial_state L1 q1 s1 ->
          exists i, exists s2, initial_state L2 q2 s2 /\
          exists wA' wB'', wA :-> wA' /\ wB' *-> wB'' /\ match_states wA' wB'' i s1 s2;
        fsim_match_final_states:
          forall wA wB i s1 s2 r1, match_states wA wB i s1 s2 -> final_state L1 s1 r1 ->
          exists r2, final_state L2 s2 r2 /\
          exists wB', wB *-> wB' /\ match_reply ccB wB' r1 r2 /\ winv wA wB';
        fsim_match_external:
          forall wA wB i s1 s2 q1, match_states wA wB i s1 s2 -> at_external L1 s1 q1 ->
          exists q2, at_external L2 s2 q2 /\ exists wA', wA :-> wA' /\ match_query ccA wA' q1 q2 /\
          forall r1 r2 s1' wA'', wA' *-> wA'' -> match_reply ccA wA'' r1 r2 -> after_external L1 s1 r1 s1' ->
          exists i' s2', after_external L2 s2 r2 s2' /\
          exists wA''' wB', wA'' :-> wA''' /\ wB *-> wB' /\ match_states wA''' wB' i' s1' s2';
        fsim_simulation:
          forall s1 t s1', Step L1 s1 t s1' ->
          forall wA wB i s2, match_states wA wB i s1 s2 ->
          exists i', exists s2', (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i)) /\
          exists wA' wB', wA :-> wA' /\ wB *-> wB' /\ match_states wA' wB' i' s1' s2';
      }.

  End FSIM.

  Arguments fsim_properties {_ _} _ {_ _} _ _ _ _ {_ _} L1 L2 index order match_states.
  Record fsim_components {liA1 liA2} (ccA: callconv liA1 liA2)
         {liB1 liB2} (ccB: callconv liB1 liB2) L1 L2 :=
    Forward_simulation {
        fsim_index: Type;
        fsim_order: fsim_index -> fsim_index -> Prop;
        fsim_match_states: _;
        fsim_invariant: ccworld ccA -> ccworld ccB -> Prop;

        fsim_invariant_env_step:
          forall wA wB, fsim_invariant wA wB -> forall wB', wB :-> wB' -> fsim_invariant wA wB';
        fsim_skel: skel L1 = skel L2;
        fsim_initial_world: fsim_invariant (pset_init (ccworld ccA)) (pset_init (ccworld ccB));
        fsim_footprint: forall i, footprint L1 i <-> footprint L2 i;
        fsim_lts wA wB se1 se2:
          fsim_invariant wA wB ->
          fsim_properties ccA ccB wA wB fsim_invariant (activate L1 se1) (activate L2 se2)
                        fsim_index fsim_order (fsim_match_states se1 se2);
        fsim_order_wf:
          well_founded fsim_order;
      }.
  Arguments Forward_simulation {_ _ ccA _ _ ccB L1 L2 fsim_index}.

  Definition forward_simulation {liA1 liA2} ccA {liB1 liB2} ccB L1 L2 :=
    inhabited (@fsim_components liA1 liA2 ccA liB1 liB2 ccB L1 L2).

End ST.

Module E.

  Definition forward_simulation {liA1 liA2} (ccA: ST.callconv liA1 liA2)
             {liB1 liB2} (ccB: ST.callconv liB1 liB2)
             (L1: liA1 +-> liB1) (L2: liA2 +-> liB2) :=
    ST.forward_simulation ccA (ST.callconv_lift ccB (pstate L1) (pstate L2))
                       (esem L1) (esem L2).

End E.

(** ** Properties *)

(** *** Composition *)
Generalizable All Variables.

(** Composition of Stateful Simulations *)

Section FSIM.
  Context `(ccA: ST.callconv liA1 liA2)
          `(ccB: ST.callconv liB1 liB2)
          `(ccC: ST.callconv liC1 liC2)
          (L1s: semantics liB1 liC1) (L2s: semantics liA1 liB1)
          (L1t: semantics liB2 liC2) (L2t: semantics liA2 liB2).
  Context (HL1: ST.fsim_components ccB ccC L1s L1t)
          (HL2: ST.fsim_components ccA ccB L2s L2t)
          (wA : ST.ccworld ccA) (wC: ST.ccworld ccC)
          (se1 se2: Genv.symtbl).

  Variant index := | index1: ST.fsim_index HL1 -> index
                   | index2: ST.fsim_index HL1 -> ST.fsim_index HL2 -> index.

  Variant order: index -> index -> Prop :=
    | order1 i1 i1': ST.fsim_order HL1 i1 i1' ->
                     order (index1 i1) (index1 i1')
    | order2 i1 i2 i2': ST.fsim_order HL2 i2 i2' ->
                        order (index2 i1 i2) (index2 i1 i2').

  Inductive match_states: ST.ccworld ccA -> ST.ccworld ccC -> index ->
                          comp_state L1s L2s -> comp_state L1t L2t -> Prop :=
  | match_st1 wa wb wc i1 s1 s1':
    ST.fsim_match_states HL1 se1 se2 wb wc i1 s1 s1' ->
    ST.fsim_invariant HL2 wa wb ->
    match_states wa wc (index1 i1) (st1 L1s L2s s1) (st1 L1t L2t s1')
  | match_st2 wa wb wc i1 i2 s1 t1 s2 t2 :
    ST.fsim_match_states HL2 se1 se2 wa wb i2 s2 t2 ->
    (forall r1 r2 (s1' : state L1s) wb',
        wb *-> wb' ->
        ST.match_reply ccB wb' r1 r2 ->
        after_external (L1s se1) s1 r1 s1' ->
        exists (i' : ST.fsim_index HL1) (t1' : state L1t),
          after_external (L1t se2) t1 r2 t1' /\
            exists wb'' wc', wb' :-> wb'' /\ wc *-> wc' /\
                          ST.fsim_match_states HL1 se1 se2 wb'' wc' i' s1' t1') ->
    match_states wa wc (index2 i1 i2) (st2 L1s L2s s1 s2) (st2 L1t L2t t1 t2).

  Definition inv : ST.ccworld ccA -> ST.ccworld ccC -> Prop :=
    fun wa wc => exists wb, ST.fsim_invariant HL1 wb wc /\ ST.fsim_invariant HL2 wa wb.

  Lemma st_fsim_comp' sk sk':
    inv wA wC ->
    ST.fsim_properties ccA ccC wA wC inv
                       (comp_semantics' L1s L2s sk se1)
                       (comp_semantics' L1t L2t sk' se2)
                       index order match_states.
  Proof.
    intros (wB & INV1 & INV2). split; cbn.
    - intros q1 q2 s1 wC' WC Hq H. inv H.
      pose proof (ST.fsim_lts HL1 _ _ se1 se2 INV1).
      edestruct @ST.fsim_match_initial_states as (idx & s' & Hs' & Hs); eauto.
      destruct Hs as (wB' & wC'' & W1 & W2 & HS).
      exists (index1 idx), (st1 L1t L2t s').
      split. econstructor; eauto.
      exists wA, wC''. repeat split; eauto. reflexivity.
      econstructor. apply HS. eapply ST.fsim_invariant_env_step; eauto.
    - intros wa wb i s1 s2 r1 Hs Hf. inv Hf. inv Hs.
      rename wb into wc. rename wb0 into wb.
      pose proof (ST.fsim_lts HL1 _ _ se1 se2 INV1).
      edestruct @ST.fsim_match_final_states as (r' & H' & Hr'); eauto.
      destruct Hr' as (wc' & W & Hr' & INV).
      exists r'. split. econstructor; eauto.
      exists wc'. repeat split; eauto.
      exists wb. split; eauto.
    - intros wa wc i s1 s2 q1 Hs H. inv H. inv Hs.
      pose proof (ST.fsim_lts HL2 _ _ se1 se2 INV2).
      edestruct @ST.fsim_match_external as (q' & H' & wa' & WA & Hq' & HH); eauto.
      exists q'. split. econstructor; eauto.
      exists wa'. repeat split; eauto.
      intros r1 r2 xs1 wa'' WA' Hr HH'. inv HH'.
      specialize (HH _ _ _ _ WA' Hr H6) as (i2' & xs2 & Haft & Hss).
      destruct Hss as (wa''' & wb' & WA'' & WB & HS).
      eexists (index2 i1 i2'), (st2 L1t L2t _ _).
      split. econstructor; eauto.
      exists wa''', wc. repeat split; eauto. reflexivity.
      econstructor. exact HS.
      intros ? ? ? wbx WBX. apply H7. etransitivity; eauto.
    - intros s1 t s2 Hstep wa wc idx t1 Hs.
      inv Hstep; inv Hs.
      + pose proof (ST.fsim_lts HL1 _ _ se1 se2 INV1).
        edestruct @ST.fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
        destruct Hs' as (wb' & wc' & WB & WC & HS).
        exists (index1 idx'), (st1 L1t L2t s2'). split.
        * destruct Hs2'; [ left | right ].
          apply plus_internal1. auto.
          split. apply star_internal1. apply H2. constructor; apply H2.
        * exists wa, wc'. repeat split; eauto. reflexivity.
          econstructor; eauto. eapply @ST.fsim_invariant_env_step; eauto.
      + pose proof (ST.fsim_lts HL2 _ _ se1 se2 INV2).
        edestruct @ST.fsim_simulation as (idx' & xs2' & Hs2' & Hs'); eauto.
        destruct Hs' as (wa' & wb' & WA & WB & HS).
        exists (index2 i1 idx'), (st2 L1t L2t t0 xs2'). split.
        * destruct Hs2'; [ left | right ].
          -- apply plus_internal2. auto.
          -- split. apply star_internal2. apply H1.
             constructor. apply H1.
        * exists wa', wc. repeat split; eauto. reflexivity.
          econstructor; eauto.
          intros r1 r2 sr wb'' WB'. apply H7. etransitivity; eauto.
      + pose proof (ST.fsim_lts HL1 _ _ se1 se2 INV1).
        edestruct @ST.fsim_match_external as (q' & H' & wb' & WB & Hq' & HH); eauto.
        pose proof (ST.fsim_lts HL2 _ _ se1 se2 H6).
        edestruct @ST.fsim_match_initial_states as (i2 & s' & Hs' & Hs); eauto.
        destruct Hs as (wa' & wb'' & WA & WB' & Hs).
        exists (index2 i1 i2), (st2 L1t L2t s1' s'). split.
        * left. apply plus_one. eapply step_push; eauto.
        * exists wa', wc. repeat split; eauto. reflexivity.
          econstructor; eauto.
          intros r1 r2 sr wb''' WB'' HR Haft.
          specialize (HH r1 r2 sr wb'''). apply HH. etransitivity; eauto.
          exact HR. exact Haft.
      + pose proof (ST.fsim_lts HL2 _ _ se1 se2 INV2).
        edestruct @ST.fsim_match_final_states as (r' & H' & Hr'); eauto.
        edestruct Hr' as (wb' & WB & Hr & INV).
        edestruct H8 as (idx & t1 & HH & HX); eauto.
        destruct HX as (wb'' & wc' & WB' & WC & HS).
        exists (index1 idx), (st1 L1t L2t t1). split.
        * left. apply plus_one. eapply step_pop; eauto.
        * exists wa, wc'. repeat split; eauto. reflexivity.
          econstructor. exact HS.
          eapply ST.fsim_invariant_env_step; eauto.
  Qed.

End FSIM.

Section COMP.

  Context `(ccA: ST.callconv liA1 liA2)
          `(ccB: ST.callconv liB1 liB2)
          `(ccC: ST.callconv liC1 liC2)
          (L1s: semantics liB1 liC1) (L2s: semantics liA1 liB1)
          (L1t: semantics liB2 liC2) (L2t: semantics liA2 liB2).
  Context (HL1: ST.forward_simulation ccB ccC L1s L1t)
          (HL2: ST.forward_simulation ccA ccB L2s L2t).
  Context `(HLs: comp_semantics L1s L2s = Some Ls)
          Lt (HLt: comp_semantics L1t L2t = Some Lt).

  Lemma st_fsim_comp : ST.forward_simulation ccA ccC Ls Lt.
  Proof.
    destruct HL1 as [Ha]. destruct HL2 as [Hb].
    unfold comp_semantics, option_map in HLs, HLt.
    destruct (Linking.link (skel L1s) (skel L2s)) as [sk1|] eqn:Hsk1; try discriminate. inv HLs.
    destruct (Linking.link (skel L1t) (skel L2t)) as [sk2|] eqn:Hsk2; try discriminate. inv HLt.
    constructor.
    eapply ST.Forward_simulation
      with (@order _ _ ccA _ _ ccB _ _ ccC L1s L2s L1t L2t Ha Hb)
           (@match_states _ _ ccA _ _ ccB _ _ ccC L1s L2s L1t L2t Ha Hb)
           (@inv _ _ ccA _ _ ccB _ _ ccC L1s L2s L1t L2t Ha Hb).
    - intros wa wc (wb & I1 & I2) wc' WC.
      exists wb; split; eauto. eapply ST.fsim_invariant_env_step; eauto.
    - destruct Ha. destruct Hb. cbn. congruence.
    - exists (pset_init (ST.ccworld ccB)).
      split. apply Ha. apply Hb.
    - cbn. intros i. destruct Ha, Hb.
      rewrite fsim_footprint, fsim_footprint0. reflexivity.
    - intros wa wc se1 se2 INV. eapply st_fsim_comp'; eauto.
    - clear - Ha Hb. intros [|].
      + induction (ST.fsim_order_wf Ha f). constructor.
        intros. inv H1. apply H0. auto.
      + induction (ST.fsim_order_wf Hb f0). constructor.
        intros. inv H1. apply H0. auto.
  Qed.

End COMP.

(** Lifting Simulations with Additional States *)

Section LIFT.

  Context `(ccA: ST.callconv liA1 liA2)
          `(ccB: ST.callconv liB1 liB2)
          `(X: ST.fsim_components ccA ccB L1 L2).
  Context (K1 K2: PSet).

  Lemma st_fsim_lift': ST.forward_simulation
                        (ST.callconv_lift ccA K1 K2)
                        (ST.callconv_lift ccB K1 K2)
                        (L1@K1) (L2@K2).
  Proof.
    constructor.
    eapply ST.Forward_simulation with
      (ST.fsim_order X)
      (fun se1 se2 '(wa, k1a, k2a) '(wb, k1b, k2b) i '(s1, k1) '(s2, k2) =>
         ST.fsim_match_states X se1 se2 wa wb i s1 s2 /\
           k1a = k1 /\ k1b = k1 /\ k2a = k2 /\ k2b = k2)
      (fun '(wa, k1a, k2a) '(wb, k1b, k2b) => ST.fsim_invariant X wa wb /\ k1a = k1b /\ k2a = k2b).
    - intros [[wa k1a] k2a] [[wb k1b] k2b] (INV & -> & ->) [[wb' k1b'] k2b'] W.
      destruct W as [[W U] V]. inv U. inv V. repeat split; eauto.
      eapply ST.fsim_invariant_env_step; eauto.
    - apply X.
    - cbn. repeat split; eauto. apply X.
    - intros i. cbn. apply X.
    - intros [[wa k1a] k2a] [[wb k1b] k2b] se1 se2 (I & -> & ->). split; cbn.
      + intros. prod_crush. subst.
        pose proof (ST.fsim_lts X _ _ se1 se2 I).
        edestruct @ST.fsim_match_initial_states as (idx & s' & Hs' & Hs); eauto.
        destruct Hs as (wa' & wb'' & W1 & W2 & HS).
        eexists idx, (s', _). repeat split; eauto.
        eexists (wa', _, _), (wb'', _, _). repeat split; eauto.
      + intros. prod_crush. subst.
        pose proof (ST.fsim_lts X _ _ se1 se2 I).
        edestruct @ST.fsim_match_final_states as (r' & H' & Hr'); eauto.
        destruct Hr' as (wb' & W & Hr' & INV).
        eexists (r', _). repeat split; eauto.
        eexists (wb', _, _). repeat split; eauto.
      + intros. prod_crush. subst.
        pose proof (ST.fsim_lts X _ _ se1 se2 I).
        edestruct @ST.fsim_match_external as (q' & H' & wa' & WA & Hq' & HH); eauto.
        eexists (q', _). repeat split; eauto.
        eexists (wa', _, _). repeat split; eauto.
        intros. prod_crush. subst.
        edestruct HH as (i' & s2' & Haft & Hs); eauto.
        destruct Hs as (wa'' & wb' & WA' & WB & HS).
        eexists i', (s2', _). repeat split; eauto.
        eexists (wa'', _, _), (wb', _, _). repeat split; eauto.
      + intros. prod_crush. subst.
        pose proof (ST.fsim_lts X _ _ se1 se2 I).
        edestruct @ST.fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
        destruct Hs' as (wa' & wb' & WA & WB & HS).
        destruct Hs2'.
        * eexists idx', (s2', _). split.
          -- left. apply lifting_step_plus; eauto.
          -- eexists (wa', _, _), (wb', _, _).
             repeat split; eauto.
        * eexists idx', (s2', _). split.
          -- right. split. apply lifting_step_star; eauto. all: apply H2.
          -- eexists (wa', _, _), (wb', _, _).
             repeat split; eauto.
    - apply X.
  Qed.

End LIFT.


Lemma st_fsim_lift `(ccA: ST.callconv liA1 liA2) `(ccB: ST.callconv liB1 liB2)
      L1 L2 (K1 K2: PSet):
  ST.forward_simulation ccA ccB L1 L2 ->
  ST.forward_simulation
                        (ST.callconv_lift ccA K1 K2)
                        (ST.callconv_lift ccB K1 K2)
                        (L1@K1) (L2@K2).
Proof.
  intros [H]. apply st_fsim_lift'. apply H.
Qed.

(** Composition of Components with Encapsulated States *)
Section COMP.
  Context `(ccA: ST.callconv liA1 liA2)
          `(ccB: ST.callconv liB1 liB2)
          `(ccC: ST.callconv liC1 liC2)
          (L1s: liB1 +-> liC1) (L2s: liA1 +-> liB1)
          (L1t: liB2 +-> liC2) (L2t: liA2 +-> liB2).
  Context (HL1: E.forward_simulation ccB ccC L1s L1t)
          (HL2: E.forward_simulation ccA ccB L2s L2t).
  Context `(HLs: comp_esem L1s L2s = Some Ls)
          Lt (HLt: comp_esem L1t L2t = Some Lt).

  Lemma encap_fsim_comp : E.forward_simulation ccA ccC Ls Lt.
  Proof.
    unfold E.forward_simulation in *.
    unfold comp_esem in *.
  Admitted.

End COMP.

Require Import Ctypes Cop Clight.

(** ** ClightP semantics *)
Module ClightP.

  Inductive val : Type :=
  | Val : Values.val -> val
  | Array : nat -> ZMap.t val -> val
  | Struct : list ident -> PMap.t val -> val.

  Record privvar (V: Type) : Type :=
    mkprivvar {
        pvar_info: V;         (**r language-dependent info, e.g. a type *)
        pvar_init: val;       (**r initialization data *)
      }.

  Inductive expr : Type :=
  | Econst_int: int -> type -> expr       (**r integer literal *)
  | Econst_float: float -> type -> expr   (**r double float literal *)
  | Econst_single: float32 -> type -> expr (**r single float literal *)
  | Econst_long: int64 -> type -> expr    (**r long integer literal *)
  | Evar: ident -> type -> expr           (**r variable *)
  | Etempvar: ident -> type -> expr       (**r temporary variable *)
  | Ederef: expr -> type -> expr          (**r pointer dereference (unary [*]) *)
  | Eaddrof: expr -> type -> expr         (**r address-of operator ([&]) *)
  | Eunop: unary_operation -> expr -> type -> expr  (**r unary operation *)
  | Ebinop: binary_operation -> expr -> expr -> type -> expr (**r binary operation *)
  | Ecast: expr -> type -> expr   (**r type cast ([(ty) e]) *)
  | Efield: expr -> ident -> type -> expr (**r access to a member of a struct or union *)
  | Esizeof: type -> type -> expr         (**r size of a type *)
  | Ealignof: type -> type -> expr        (**r alignment of a type *)
  (* two new cases for persistent data and struct and array *)
  | Epvar : ident -> type -> expr
  | Eaccess : expr -> Z + ident -> type -> expr.

  Definition typeof (e: expr) : type :=
    match e with
    | Econst_int _ ty => ty
    | Econst_float _ ty => ty
    | Econst_single _ ty => ty
    | Econst_long _ ty => ty
    | Evar _ ty => ty
    | Etempvar _ ty => ty
    | Ederef _ ty => ty
    | Eaddrof _ ty => ty
    | Eunop _ _ ty => ty
    | Ebinop _ _ _ ty => ty
    | Ecast _ ty => ty
    | Efield _ _ ty => ty
    | Esizeof _ ty => ty
    | Ealignof _ ty => ty
    | Epvar _ ty => ty
    | Eaccess _ _ ty => ty
    end.

  Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Sassign : expr -> expr -> statement (**r assignment [lvalue = rvalue] *)
  | Sset : ident -> expr -> statement   (**r assignment [tempvar = rvalue] *)
  | Scall: option ident -> expr -> list expr -> statement (**r function call *)
  | Sbuiltin: option ident -> external_function -> typelist -> list expr -> statement (**r builtin invocation *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
  | Sloop: statement -> statement -> statement (**r infinite loop *)
  | Sbreak : statement                      (**r [break] statement *)
  | Scontinue : statement                   (**r [continue] statement *)
  | Sreturn : option expr -> statement      (**r [return] statement *)
  | Sswitch : expr -> labeled_statements -> statement  (**r [switch] statement *)
  | Slabel : label -> statement -> statement
  | Sgoto : label -> statement

  | Supdate : expr -> expr -> statement

  with labeled_statements : Type :=            (**r cases of a [switch] *)
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements.
  (**r [None] is [default], [Some x] is [case x] *)

  Fixpoint select_switch_default (sl: labeled_statements): labeled_statements :=
    match sl with
    | LSnil => sl
    | LScons None s sl' => sl
    | LScons (Some i) s sl' => select_switch_default sl'
    end.

  Fixpoint select_switch_case (n: Z) (sl: labeled_statements): option labeled_statements :=
    match sl with
    | LSnil => None
    | LScons None s sl' => select_switch_case n sl'
    | LScons (Some c) s sl' => if zeq c n then Some sl else select_switch_case n sl'
    end.

  Definition select_switch (n: Z) (sl: labeled_statements): labeled_statements :=
    match select_switch_case n sl with
    | Some sl' => sl'
    | None => select_switch_default sl
    end.

  (** Turn a labeled statement into a sequence *)

  Fixpoint seq_of_labeled_statement (sl: labeled_statements) : statement :=
    match sl with
    | LSnil => Sskip
    | LScons _ s sl' => Ssequence s (seq_of_labeled_statement sl')
    end.

  Record function : Type :=
    mkfunction {
        fn_return: type;
        fn_callconv: calling_convention;
        fn_params: list (ident * type);
        fn_vars: list (ident * type);
        fn_temps: list (ident * type);
        fn_body: statement
      }.
  Definition fundef := Ctypes.fundef function.
  Definition type_of_function (f: function) : type :=
    Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

  Definition type_of_fundef (f: fundef) : type :=
    match f with
    | Internal fd => type_of_function fd
    | External id args res cc => Tfunction args res cc
    end.


  Record program : Type := {
      prog_defs: list (ident * globdef fundef type);
      prog_private: list (ident * privvar type);
      prog_public: list ident;
      prog_main: ident;
      prog_types: list composite_definition;
      prog_comp_env: composite_env;
      prog_comp_env_eq: build_composite_env prog_types = OK prog_comp_env
    }.

  Definition program_of_program (p: program) : AST.program fundef type :=
    {|
      AST.prog_defs := p.(prog_defs);
      AST.prog_public := p.(prog_public);
      AST.prog_main := p.(prog_main); |}.
  Coercion program_of_program: program >-> AST.program.

  Record genv := { genv_genv :> Genv.t fundef type;
                   genv_cenv :> composite_env }.

  Definition globalenv (se: Genv.symtbl) (p: program) :=
    {| genv_genv := Genv.globalenv se p; genv_cenv := p.(prog_comp_env) |}.

  Section SEM.
    Open Scope Z_scope.

    Definition penv : Type := PTree.t val.
    Variable ge: genv.

    Inductive alloc_variables: env -> mem ->
                               list (ident * type) ->
                               env -> mem -> Prop :=
    | alloc_variables_nil:
      forall e m,
        alloc_variables e m nil e m
    | alloc_variables_cons:
      forall e m id ty vars m1 b1 m2 e2,
        Mem.alloc m 0 (sizeof ge ty) = (m1, b1) ->
        alloc_variables (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
        alloc_variables e m ((id, ty) :: vars) e2 m2.

    Inductive bind_parameters (e: env):
                               mem ->
                               list (ident * type) -> list Values.val ->
                               mem -> Prop :=
    | bind_parameters_nil:
      forall m,
        bind_parameters e m nil nil m
    | bind_parameters_cons:
      forall m id ty params v1 vl b m1 m2,
        PTree.get id e = Some(b, ty) ->
        assign_loc ge ty m b Ptrofs.zero Full v1 m1 ->
        bind_parameters e m1 params vl m2 ->
        bind_parameters e m ((id, ty) :: params) (v1 :: vl) m2.

    Section EXPR.

      Variable e: env.
      Variable le: temp_env.
      Variable pe: penv.
      Variable m: mem.

      Coercion Val : Values.val >-> val.

      Inductive eval_expr: expr -> val -> Prop :=
      | eval_Econst_int:   forall i ty,
          eval_expr (Econst_int i ty) (Vint i)
      | eval_Econst_float:   forall f ty,
          eval_expr (Econst_float f ty) (Vfloat f)
      | eval_Econst_single:   forall f ty,
          eval_expr (Econst_single f ty) (Vsingle f)
      | eval_Econst_long:   forall i ty,
          eval_expr (Econst_long i ty) (Vlong i)
      | eval_Etempvar:  forall id ty v,
          le!id = Some v ->
          eval_expr (Etempvar id ty) v
      | eval_Eaddrof: forall a ty loc ofs,
          eval_lvalue a loc ofs Full ->
          eval_expr (Eaddrof a ty) (Vptr loc ofs)
      | eval_Eunop:  forall op a ty v1 v,
          eval_expr a (Val v1) ->
          sem_unary_operation op v1 (typeof a) m = Some v ->
          eval_expr (Eunop op a ty) v
      | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
          eval_expr a1 (Val v1) ->
          eval_expr a2 (Val v2) ->
          sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m = Some v ->
          eval_expr (Ebinop op a1 a2 ty) v
      | eval_Ecast:   forall a ty v1 v,
          eval_expr a (Val v1) ->
          sem_cast v1 (typeof a) ty m = Some v ->
          eval_expr (Ecast a ty) v
      | eval_Esizeof: forall ty1 ty,
          eval_expr (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
      | eval_Ealignof: forall ty1 ty,
          eval_expr (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof ge ty1)))
      | eval_Elvalue: forall a loc ofs bf v,
          eval_lvalue a loc ofs bf ->
          deref_loc (typeof a) m loc ofs bf v ->
          eval_expr a v
      (* the new case *)
      | eval_Epvar: forall id ty v,
          pe!id = Some v ->
          eval_expr (Epvar id ty) v
      | eval_Earray: forall a i ty v sz vs,
          eval_expr a (Array sz vs) ->
          i < Z.of_nat sz ->
          ZMap.get i vs = v ->
          eval_expr (Eaccess a (inl i) ty) v
      | eval_Estruct: forall a f ty v fs vs,
          eval_expr a (Struct fs vs) ->
          In f fs ->
          PMap.get f vs = v ->
          eval_expr (Eaccess a (inr f) ty) v

      with eval_lvalue: expr -> block -> ptrofs -> bitfield -> Prop :=
      | eval_Evar_local:   forall id l ty,
          e!id = Some(l, ty) ->
          eval_lvalue (Evar id ty) l Ptrofs.zero Full
      | eval_Evar_global: forall id l ty,
          e!id = None ->
          Genv.find_symbol ge id = Some l ->
          eval_lvalue (Evar id ty) l Ptrofs.zero Full
      | eval_Ederef: forall a ty l ofs,
          eval_expr a (Vptr l ofs) ->
          eval_lvalue (Ederef a ty) l ofs Full
      | eval_Efield_struct:   forall a i ty l ofs id co att delta bf,
          eval_expr a (Vptr l ofs) ->
          typeof a = Tstruct id att ->
          ge.(genv_cenv)!id = Some co ->
          field_offset ge i (co_members co) = OK (delta, bf) ->
          eval_lvalue (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf
      | eval_Efield_union:   forall a i ty l ofs id co att delta bf,
          eval_expr a (Vptr l ofs) ->
          typeof a = Tunion id att ->
          ge.(genv_cenv)!id = Some co ->
          union_field_offset ge i (co_members co) = OK (delta, bf) ->
          eval_lvalue (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf.

      Scheme eval_expr_ind2 := Minimality for eval_expr Sort Prop
          with eval_lvalue_ind2 := Minimality for eval_lvalue Sort Prop.
      Combined Scheme eval_expr_lvalue_ind from eval_expr_ind2, eval_lvalue_ind2.

      Inductive eval_exprlist: list expr -> typelist -> list Values.val -> Prop :=
      | eval_Enil:
        eval_exprlist nil Tnil nil
      | eval_Econs:   forall a bl ty tyl v1 v2 vl,
          eval_expr a (Val v1) ->
          sem_cast v1 (typeof a) ty m = Some v2 ->
          eval_exprlist bl tyl vl ->
          eval_exprlist (a :: bl) (Tcons ty tyl) (v2 :: vl).

    End EXPR.

    Definition block_of_binding (id_b_ty: ident * (block * type)) :=
      match id_b_ty with (id, (b, ty)) => (b, 0, sizeof ge ty) end.

    Definition blocks_of_env (e: env) : list (block * Z * Z) :=
      List.map block_of_binding (PTree.elements e).

    (** Transition relation *)

    Inductive cont: Type :=
    | Kstop: cont
    | Kseq: statement -> cont -> cont
    | Kloop1: statement -> statement -> cont -> cont
    | Kloop2: statement -> statement -> cont -> cont
    | Kswitch: cont -> cont
    | Kcall: option ident -> function -> env -> temp_env -> cont -> cont.

    Fixpoint call_cont (k: cont) : cont :=
      match k with
      | Kseq s k => call_cont k
      | Kloop1 s1 s2 k => call_cont k
      | Kloop2 s1 s2 k => call_cont k
      | Kswitch k => call_cont k
      | _ => k
      end.

    Definition is_call_cont (k: cont) : Prop :=
      match k with
      | Kstop => True
      | Kcall _ _ _ _ _ => True
      | _ => False
      end.

    Inductive state: Type :=
    | State (f: function) (s: statement) (k: cont)
            (e: env) (le: temp_env) (m: mem) : state
    | Callstate (vf: Values.val) (args: list Values.val)
                (k: cont) (m: mem) : state
    | Returnstate (res: Values.val) (k: cont) (m: mem) : state.

    Fixpoint find_label (lbl: label) (s: statement) (k: cont)
             {struct s}: option (statement * cont) :=
      match s with
      | Ssequence s1 s2 =>
          match find_label lbl s1 (Kseq s2 k) with
          | Some sk => Some sk
          | None => find_label lbl s2 k
          end
      | Sifthenelse a s1 s2 =>
          match find_label lbl s1 k with
          | Some sk => Some sk
          | None => find_label lbl s2 k
          end
      | Sloop s1 s2 =>
          match find_label lbl s1 (Kloop1 s1 s2 k) with
          | Some sk => Some sk
          | None => find_label lbl s2 (Kloop2 s1 s2 k)
          end
      | Sswitch e sl =>
          find_label_ls lbl sl (Kswitch k)
      | Slabel lbl' s' =>
          if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
      | _ => None
      end

    with find_label_ls (lbl: label) (sl: labeled_statements) (k: cont)
                       {struct sl}: option (statement * cont) :=
           match sl with
           | LSnil => None
           | LScons _ s sl' =>
               match find_label lbl s (Kseq (seq_of_labeled_statement sl') k) with
               | Some sk => Some sk
               | None => find_label_ls lbl sl' k
               end
           end.

    Fixpoint update_penv_helper (a: expr) (v: val) (w: Values.val) : option (ident * val) :=
      match a, v with
      | Epvar i _, Val _ => Some (i, Val w)
      | Eaccess e (inl x) _, Array sz vs =>
          match update_penv_helper e (ZMap.get x vs) w with
          | Some (i, v') => Some (i, Array sz (ZMap.set x v' vs))
          | None => None
          end
      | Eaccess e (inr f) _, Struct fs vs =>
          match update_penv_helper e (PMap.get f vs) w with
          | Some (i, v') => Some (i, Struct fs (PMap.set f v' vs))
          | None => None
          end
      | _, _ => None
      end.

    Variable function_entry:
      function -> list Values.val -> mem -> env -> temp_env -> mem -> Prop.

    Inductive step: state * penv -> trace -> state * penv -> Prop :=

    | step_assign:   forall f a1 a2 k e le pe m loc ofs bf v2 v m',
        eval_lvalue e le pe m a1 loc ofs bf ->
        eval_expr e le pe m a2 (Val v2) ->
        sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
        assign_loc ge (typeof a1) m loc ofs bf v m' ->
        step (State f (Sassign a1 a2) k e le m, pe)
             E0 (State f Sskip k e le m', pe)

    | step_set:   forall f id a k e le pe m v,
        eval_expr e le pe m a (Val v) ->
        step (State f (Sset id a) k e le m, pe)
             E0 (State f Sskip k e (PTree.set id v le) m, pe)

    | step_update: forall f a1 a2 k e le pe m id v w v' w',
        eval_expr e le pe m a1 v ->
        eval_expr e le pe m a2 (Val w) ->
        sem_cast w (typeof a2) (typeof a1) m = Some w' ->
        update_penv_helper a1 v w = Some (id, v') ->
        step (State f (Supdate a1 a2) k e le m, pe)
             E0 (State f Sskip k e le m, PTree.set id v pe)

    | step_call:   forall f optid a al k e le pe m tyargs tyres cconv vf vargs fd,
        classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
        eval_expr e le pe m a (Val vf) ->
        eval_exprlist e le pe m al tyargs vargs ->
        Genv.find_funct ge vf = Some fd ->
        type_of_fundef fd = Tfunction tyargs tyres cconv ->
        step (State f (Scall optid a al) k e le m, pe)
             E0 (Callstate vf vargs (Kcall optid f e le k) m, pe)

    | step_builtin:   forall f optid ef tyargs al k e le pe m vargs t vres m',
        eval_exprlist e le pe m al tyargs vargs ->
        external_call ef ge vargs m t vres m' ->
        step (State f (Sbuiltin optid ef tyargs al) k e le m, pe)
             t (State f Sskip k e (set_opttemp optid vres le) m', pe)

    | step_seq:  forall f s1 s2 k e le pe m,
        step (State f (Ssequence s1 s2) k e le m, pe)
             E0 (State f s1 (Kseq s2 k) e le m, pe)
    | step_skip_seq: forall f s k e le pe m,
        step (State f Sskip (Kseq s k) e le m, pe)
             E0 (State f s k e le m, pe)
    | step_continue_seq: forall f s k e le pe m,
        step (State f Scontinue (Kseq s k) e le m, pe)
             E0 (State f Scontinue k e le m, pe)
    | step_break_seq: forall f s k e le pe m,
        step (State f Sbreak (Kseq s k) e le m, pe)
             E0 (State f Sbreak k e le m, pe)

    | step_ifthenelse:  forall f a s1 s2 k e le pe m v1 b,
        eval_expr e le pe m a (Val v1) ->
        bool_val v1 (typeof a) m = Some b ->
        step (State f (Sifthenelse a s1 s2) k e le m, pe)
             E0 (State f (if b then s1 else s2) k e le m, pe)

    | step_loop: forall f s1 s2 k e le pe m,
        step (State f (Sloop s1 s2) k e le m, pe)
             E0 (State f s1 (Kloop1 s1 s2 k) e le m, pe)
    | step_skip_or_continue_loop1:  forall f s1 s2 k e le pe m x,
        x = Sskip \/ x = Scontinue ->
        step (State f x (Kloop1 s1 s2 k) e le m, pe)
             E0 (State f s2 (Kloop2 s1 s2 k) e le m, pe)
    | step_break_loop1:  forall f s1 s2 k e le pe m,
        step (State f Sbreak (Kloop1 s1 s2 k) e le m, pe)
             E0 (State f Sskip k e le m, pe)
    | step_skip_loop2: forall f s1 s2 k e le pe m,
        step (State f Sskip (Kloop2 s1 s2 k) e le m, pe)
             E0 (State f (Sloop s1 s2) k e le m, pe)
    | step_break_loop2: forall f s1 s2 k e le pe m,
        step (State f Sbreak (Kloop2 s1 s2 k) e le m, pe)
             E0 (State f Sskip k e le m, pe)

    | step_return_0: forall f k e le pe m m',
        Mem.free_list m (blocks_of_env e) = Some m' ->
        step (State f (Sreturn None) k e le m, pe)
             E0 (Returnstate Vundef (call_cont k) m', pe)
    | step_return_1: forall f a k e le pe m v v' m',
        eval_expr e le pe m a (Val v) ->
        sem_cast v (typeof a) f.(fn_return) m = Some v' ->
        Mem.free_list m (blocks_of_env e) = Some m' ->
        step (State f (Sreturn (Some a)) k e le m, pe)
             E0 (Returnstate v' (call_cont k) m', pe)
    | step_skip_call: forall f k e le pe m m',
        is_call_cont k ->
        Mem.free_list m (blocks_of_env e) = Some m' ->
        step (State f Sskip k e le m, pe)
             E0 (Returnstate Vundef k m', pe)

    | step_switch: forall f a sl k e le pe m v n,
        eval_expr e le pe m a (Val v) ->
        sem_switch_arg v (typeof a) = Some n ->
        step (State f (Sswitch a sl) k e le m, pe)
             E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m, pe)
    | step_skip_break_switch: forall f x k e le pe m,
        x = Sskip \/ x = Sbreak ->
        step (State f x (Kswitch k) e le m, pe)
             E0 (State f Sskip k e le m, pe)
    | step_continue_switch: forall f k e le pe m,
        step (State f Scontinue (Kswitch k) e le m, pe)
             E0 (State f Scontinue k e le m, pe)

    | step_label: forall f lbl s k e le pe m,
        step (State f (Slabel lbl s) k e le m, pe)
             E0 (State f s k e le m, pe)

    | step_goto: forall f lbl k e le pe m s' k',
        find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
        step (State f (Sgoto lbl) k e le m, pe)
             E0 (State f s' k' e le m, pe)

    | step_internal_function: forall vf f vargs k m e le pe m1,
      forall FIND: Genv.find_funct ge vf = Some (Internal f),
        function_entry f vargs m e le m1 ->
        step (Callstate vf vargs k m, pe)
             E0 (State f f.(fn_body) k e le m1, pe)

    | step_external_function: forall vf ef targs tres cconv vargs k m vres t m' pe,
      forall FIND: Genv.find_funct ge vf = Some (External ef targs tres cconv),
        external_call ef ge vargs m t vres m' ->
        step (Callstate vf vargs k m, pe)
             t (Returnstate vres k m', pe)

    | step_returnstate: forall v optid f e le pe k m,
        step (Returnstate v (Kcall optid f e le k) m, pe)
             E0 (State f Sskip k e (set_opttemp optid v le) m, pe).

    Inductive initial_state: c_query * penv -> state * penv -> Prop :=
    | initial_state_intro: forall vf f targs tres tcc vargs m pe,
        Genv.find_funct ge vf = Some (Internal f) ->
        type_of_function f = Tfunction targs tres tcc ->
        val_casted_list vargs targs ->
        Mem.sup_include (Genv.genv_sup ge) (Mem.support m) ->
        initial_state
          (cq vf (signature_of_type targs tres tcc) vargs m, pe)
          (Callstate vf vargs Kstop m, pe).

    Inductive at_external: state * penv -> c_query * penv -> Prop :=
    | at_external_intro name sg targs tres cconv vf vargs k m pe:
      let f := External (EF_external name sg) targs tres cconv in
      Genv.find_funct ge vf = Some f ->
      at_external
        (Callstate vf vargs k m, pe)
        (cq vf sg vargs m, pe).

    Inductive after_external: state * penv -> c_reply * penv -> state * penv -> Prop :=
    | after_external_intro vf vargs k m pe vres m' pe':
      after_external
        (Callstate vf vargs k m, pe)
        (cr vres m', pe')
        (Returnstate vres k m', pe').

    Inductive final_state: state * penv -> c_reply * penv -> Prop :=
    | final_state_intro: forall r m pe,
        final_state
          (Returnstate r Kstop m, pe)
          (cr r m, pe).

  End SEM.

  Inductive function_entry1 (ge: genv) (f: function) (vargs: list Values.val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
  | function_entry1_intro: forall m1,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters ge e m1 f.(fn_params) vargs m' ->
      le = create_undef_temps f.(fn_temps) ->
      function_entry1 ge f vargs m e le m'.

  Definition step1 (ge: genv) := step ge (function_entry1 ge).

  (** Second, parameters as temporaries. *)

  Inductive function_entry2 (ge: genv)  (f: function) (vargs: list Values.val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
  | function_entry2_intro:
    list_norepet (var_names f.(fn_vars)) ->
    list_norepet (var_names f.(fn_params)) ->
    list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps)) ->
    alloc_variables ge empty_env m f.(fn_vars) e m' ->
    bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
    function_entry2 ge f vargs m e le m'.

  Definition step2 (ge: genv) := step ge (function_entry2 ge).

  Definition add_private (pe: penv) (x: ident * privvar type) : penv :=
    match x with
      (i, v) => PTree.set i (pvar_init _ v) pe
    end.

  Definition empty_penv : penv := PTree.empty val.

  Definition add_privates (pe: penv) (x: list (ident * privvar type)) : penv :=
    List.fold_left add_private x pe.

  Program Definition clightp1 (p : program) : esemantics li_c li_c :=
    {|
      pstate := penv;
      init_pstate := add_privates empty_penv (prog_private p);
      esem := Semantics_gen step1
                            initial_state
                            at_external
                            (fun _ => after_external)
                            (fun _ => final_state)
                            globalenv p;
    |}.

  Program Definition clightp2 (p : program) : esemantics li_c li_c :=
    {|
      pstate := penv;
      init_pstate := add_privates empty_penv (prog_private p);
      esem := Semantics_gen step2
                            initial_state
                            at_external
                            (fun _ => after_external)
                            (fun _ => final_state)
                            globalenv p;
    |}.

End ClightP.

(** ** Compile ClightP to Clight *)

Section TRANSF.
  Open Scope Z_scope.
  Open Scope error_monad_scope.
  Import ClightP.

  Fixpoint transl_lvalue (a: expr) : res Clight.expr :=
    match a with
    | Epvar i ty => OK (Clight.Evar i ty)
    | Eaccess e (inr f) ty =>
        do te <- transl_lvalue e;
        OK (Clight.Efield te f ty)
    | Eaccess e (inl i) ty =>
        do te <- transl_lvalue e;
        OK (Clight.Ebinop Oadd te
                             (Clight.Econst_int (Int.repr i) (Tint I32 Unsigned noattr))
                             (Tpointer ty noattr))
    | _ => Error (msg "transl_lvalue")
    end.

  Fixpoint transl_expr (a: expr) : res Clight.expr :=
    match a with
    | Econst_int i ty => OK (Clight.Econst_int i ty)
    | Econst_float f ty => OK (Clight.Econst_float f ty)
    | Econst_single s ty => OK (Clight.Econst_single s ty)
    | Econst_long l ty => OK (Clight.Econst_long l ty)
    | Evar i ty => OK (Clight.Evar i ty)
    | Etempvar i ty => OK (Clight.Etempvar i ty)
    | Ederef e ty =>
        do te <- transl_expr e;
        OK (Clight.Ederef te ty)
    | Eaddrof e ty =>
        do te <- transl_expr e;
        OK (Clight.Eaddrof te ty)
    | Eunop o e ty =>
        do te <- transl_expr e;
        OK (Clight.Eunop o te ty)
    | Ebinop o e1 e2 ty =>
        do te1 <- transl_expr e1;
        do te2 <- transl_expr e2;
        OK (Clight.Ebinop o te1 te2 ty)
    | Ecast e ty =>
        do te <- transl_expr e;
        OK (Clight.Ecast te ty)
    | Efield e f ty =>
        do te <- transl_expr e;
        OK (Clight.Efield te f ty)
    | Esizeof t ty => OK (Clight.Esizeof t ty)
    | Ealignof t ty => OK (Clight.Ealignof t ty)
    | Epvar i ty =>
        OK (Clight.Ederef (Clight.Evar i ty) ty)
    | Eaccess e (inr f) ty =>
        do te <- transl_lvalue e;
        OK (Clight.Ederef (Clight.Efield te f ty) ty)
    | Eaccess e (inl i) ty =>
        do te <- transl_lvalue e;
        OK (Clight.Ederef
              (Clight.Ebinop Oadd te
                             (Clight.Econst_int (Int.repr i) (Tint I32 Unsigned noattr))
                             (Tpointer ty noattr)) ty)
    end.

  Fixpoint transl_arglist (xs: list expr): res (list Clight.expr).
  Admitted.

  Fixpoint transl_statement (s: statement) : res Clight.statement :=
    match s with
    | Sskip => OK Clight.Sskip
    | Sassign b c =>
        do tb <- transl_expr b;
        do tc <- transl_expr c;
        OK (Clight.Sassign tb tc)
    | Sset x b =>
        do tb <- transl_expr b;
        OK (Clight.Sset x tb)
    | Scall x b cl =>
        do tb <- transl_expr b;
        do tcl <- transl_arglist cl;
        OK (Clight.Scall x tb tcl)
    | Sbuiltin x ef tyargs bl =>
        do tbl <- transl_arglist bl;
        OK (Clight.Sbuiltin x ef tyargs tbl)
    | Ssequence s1 s2 =>
        do ts1 <- transl_statement s1;
        do ts2 <- transl_statement s2;
        OK (Clight.Ssequence ts1 ts2)
    | Sifthenelse e s1 s2 =>
        do te <- transl_expr e;
        do ts1 <- transl_statement s1;
        do ts2 <- transl_statement s2;
        OK (Clight.Sifthenelse te ts1 ts2)
    | Sloop s1 s2 =>
        do ts1 <- transl_statement s1;
        do ts2 <- transl_statement s2;
        OK (Clight.Sloop ts1 ts2)
    | Sbreak => OK (Clight.Sbreak)
    | Scontinue => OK (Clight.Scontinue)
    | Sreturn (Some e) =>
        do te <- transl_expr e;
        OK (Clight.Sreturn (Some te))
    | Sreturn None => OK (Clight.Sreturn None)
    | Sswitch a sl =>
        do ta <- transl_expr a;
        do tsl <- transl_lbl_stmt sl;
        OK (Clight.Sswitch ta tsl)
    | Slabel lbl s =>
        do ts <- transl_statement s;
        OK (Clight.Slabel lbl ts)
    | Sgoto lbl => OK (Clight.Sgoto lbl)
    | Supdate b c =>
        do tb <- transl_lvalue b;
        do tc <- transl_expr c;
        OK (Clight.Sassign tb tc)
    end
  with transl_lbl_stmt (sl: labeled_statements) :=
         match sl with
         | LSnil => OK Clight.LSnil
         | LScons n s sl' =>
             do ts <- transl_statement s;
             do tsl' <- transl_lbl_stmt sl';
             OK (Clight.LScons n ts tsl')
         end.

  Definition transl_function (f: function) : res Clight.function :=
    do tbody <- transl_statement (fn_body f);
    OK ({|
           Clight.fn_return := fn_return f;
           Clight.fn_callconv := fn_callconv f;
           Clight.fn_params := fn_params f;
           Clight.fn_vars := fn_vars f;
           Clight.fn_temps := fn_temps f;
           Clight.fn_body := tbody
        |}).

  Definition transl_fundef (id: ident) (f: fundef) : res Clight.fundef :=
    match f with
    | Internal g =>
        do tg <- transl_function g;
        OK (Internal tg)
    | External ef args res cconv => OK (External ef args res cconv)
    end.

  Definition transl_globvar (id: ident) (ty: type) := OK ty.

  Definition val_init_data (v: val) : res (list init_data).
  Admitted.

  Definition transl_privvar {V} (v: privvar V) :=
    do x <- val_init_data (pvar_init _ v);
    OK {|
        gvar_info := pvar_info _ v;
        gvar_init := x;
        gvar_volatile := false;
        gvar_readonly := false;
      |}.

  Fixpoint transl_privvars {F V} (l: list (ident * privvar V)) :=
    match l with
    | nil => OK nil
    | (id, pv) :: l' =>
        do gv <- transl_privvar pv;
        do gv' <- transl_privvars l';
        OK ((id, Gvar (F:=F) gv) :: gv')
    end.

  Definition transl_program (p: program) : res Clight.program :=
    do tgl <- transf_globdefs transl_fundef transl_globvar p.(prog_defs);
    do tgv <- transl_privvars (prog_private p);
    OK ({|
           Ctypes.prog_defs := tgl ++ tgv;
           Ctypes.prog_public := prog_public p;
           Ctypes.prog_main := prog_main p;
           Ctypes.prog_types := prog_types p;
           Ctypes.prog_comp_env := prog_comp_env p;
           Ctypes.prog_comp_env_eq := prog_comp_env_eq p |}).

End TRANSF.

Section ClightM.

  Variable ge: Clight.genv.

  Section EXPR.

    Variable e: env.
    Variable le: temp_env.
    Variable m: mem.
    (* For now, we assume that the persistent memory does not contain pointers *)
    Variable pm: mem.

    Inductive eval_expr: expr -> val -> Prop :=
    | eval_Econst_int:   forall i ty,
        eval_expr (Econst_int i ty) (Vint i)
    | eval_Econst_float:   forall f ty,
        eval_expr (Econst_float f ty) (Vfloat f)
    | eval_Econst_single:   forall f ty,
        eval_expr (Econst_single f ty) (Vsingle f)
    | eval_Econst_long:   forall i ty,
        eval_expr (Econst_long i ty) (Vlong i)
    | eval_Etempvar:  forall id ty v,
        le!id = Some v ->
        eval_expr (Etempvar id ty) v
    | eval_Eaddrof: forall a ty loc ofs,
        eval_lvalue a loc ofs Full ->
        eval_expr (Eaddrof a ty) (Vptr loc ofs)
    | eval_Eunop:  forall op a ty v1 v,
        eval_expr a v1 ->
        sem_unary_operation op v1 (typeof a) m = Some v \/
        sem_unary_operation op v1 (typeof a) pm = Some v ->
        eval_expr (Eunop op a ty) v
    | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
        eval_expr a1 v1 ->
        eval_expr a2 v2 ->
        sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m = Some v \/
        sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) pm = Some v ->
        eval_expr (Ebinop op a1 a2 ty) v
    | eval_Ecast:   forall a ty v1 v,
        eval_expr a v1 ->
        sem_cast v1 (typeof a) ty m = Some v \/
        sem_cast v1 (typeof a) ty pm = Some v ->
        eval_expr (Ecast a ty) v
    | eval_Esizeof: forall ty1 ty,
        eval_expr (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
    | eval_Ealignof: forall ty1 ty,
        eval_expr (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof ge ty1)))
    | eval_Elvalue: forall a loc bf ofs v,
        eval_lvalue a loc ofs bf ->
        deref_loc (typeof a) m loc ofs bf v ->
        eval_expr a v
    | eval_Elvalue_pm: forall a loc bf ofs v,
        eval_lvalue a loc ofs bf ->
        deref_loc (typeof a) pm loc ofs bf v ->
        eval_expr a v
    with eval_lvalue: expr -> block -> ptrofs -> bitfield -> Prop :=
    | eval_Evar_local:   forall id l ty,
        e!id = Some(l, ty) ->
        eval_lvalue (Evar id ty) l Ptrofs.zero Full
    | eval_Evar_global: forall id l ty,
        e!id = None ->
        Genv.find_symbol ge id = Some l ->
        eval_lvalue (Evar id ty) l Ptrofs.zero Full
    | eval_Ederef: forall a ty l ofs,
        eval_expr a (Vptr l ofs) ->
        eval_lvalue (Ederef a ty) l ofs Full
    | eval_Efield_struct:   forall a i ty l ofs id co att delta bf,
        eval_expr a (Vptr l ofs) ->
        typeof a = Tstruct id att ->
        ge.(genv_cenv)!id = Some co ->
        field_offset ge i (co_members co) = OK (delta, bf) ->
        eval_lvalue (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf
    | eval_Efield_union:   forall a i ty l ofs id co att delta bf,
        eval_expr a (Vptr l ofs) ->
        typeof a = Tunion id att ->
        ge.(genv_cenv)!id = Some co ->
        union_field_offset ge i (co_members co) = OK (delta, bf) ->
        eval_lvalue (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf.

    Scheme eval_expr_ind2 := Minimality for eval_expr Sort Prop
        with eval_lvalue_ind2 := Minimality for eval_lvalue Sort Prop.
    Combined Scheme eval_expr_lvalue_ind from eval_expr_ind2, eval_lvalue_ind2.

    Inductive eval_exprlist: list expr -> typelist -> list val -> Prop :=
    | eval_Enil:
      eval_exprlist nil Tnil nil
    | eval_Econs:   forall a bl ty tyl v1 v2 vl,
        eval_expr a v1 ->
        sem_cast v1 (typeof a) ty m = Some v2 \/
        sem_cast v1 (typeof a) ty pm = Some v2 ->
        eval_exprlist bl tyl vl ->
        eval_exprlist (a :: bl) (Tcons ty tyl) (v2 :: vl).

  End EXPR.

  Variable function_entry: function -> list val -> mem -> env -> temp_env -> mem -> Prop.

  Inductive step: Clight.state * mem -> trace -> Clight.state * mem -> Prop :=

  | step_assign:   forall f a1 a2 k e le m pm loc ofs bf v2 v m',
      eval_lvalue e le m pm a1 loc ofs bf ->
      eval_expr e le m pm a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v \/
      sem_cast v2 (typeof a2) (typeof a1) pm = Some v ->
      assign_loc ge (typeof a1) m loc ofs bf v m' ->
      step (State f (Sassign a1 a2) k e le m, pm)
           E0 (State f Sskip k e le m', pm)

  | step_assign_pm:   forall f a1 a2 k e le m pm loc ofs bf v2 v pm',
      eval_lvalue e le m pm a1 loc ofs bf ->
      eval_expr e le m pm a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v \/
      sem_cast v2 (typeof a2) (typeof a1) pm = Some v ->
      assign_loc ge (typeof a1) pm loc ofs bf v pm' ->
      step (State f (Sassign a1 a2) k e le m, pm)
           E0 (State f Sskip k e le m, pm')

  | step_set:   forall f id a k e le m pm v,
      eval_expr e le m pm a v ->
      step (State f (Sset id a) k e le m, pm)
           E0 (State f Sskip k e (PTree.set id v le) m, pm)

  | step_call:   forall f optid a al k e le m pm tyargs tyres cconv vf vargs fd,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr e le m pm a vf ->
      eval_exprlist e le m pm al tyargs vargs ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction tyargs tyres cconv ->
      step (State f (Scall optid a al) k e le m, pm)
           E0 (Callstate vf vargs (Kcall optid f e le k) m, pm)

  | step_builtin:   forall f optid ef tyargs al k e le m pm vargs t vres m',
      eval_exprlist e le m pm al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      step (State f (Sbuiltin optid ef tyargs al) k e le m, pm)
           t (State f Sskip k e (set_opttemp optid vres le) m', pm)

  | step_seq:  forall f s1 s2 k e le m pm,
      step (State f (Ssequence s1 s2) k e le m, pm)
           E0 (State f s1 (Kseq s2 k) e le m, pm)
  | step_skip_seq: forall f s k e le m pm,
      step (State f Sskip (Kseq s k) e le m, pm)
           E0 (State f s k e le m, pm)
  | step_continue_seq: forall f s k e le m pm,
      step (State f Scontinue (Kseq s k) e le m, pm)
           E0 (State f Scontinue k e le m, pm)
  | step_break_seq: forall f s k e le m pm,
      step (State f Sbreak (Kseq s k) e le m, pm)
           E0 (State f Sbreak k e le m, pm)

  | step_ifthenelse:  forall f a s1 s2 k e le m pm v1 b,
      eval_expr e le m pm a v1 ->
      bool_val v1 (typeof a) m = Some b \/
      bool_val v1 (typeof a) pm = Some b ->
      step (State f (Sifthenelse a s1 s2) k e le m, pm)
           E0 (State f (if b then s1 else s2) k e le m, pm)

  | step_loop: forall f s1 s2 k e le m pm,
      step (State f (Sloop s1 s2) k e le m, pm)
           E0 (State f s1 (Kloop1 s1 s2 k) e le m, pm)
  | step_skip_or_continue_loop1:  forall f s1 s2 k e le m pm x,
      x = Sskip \/ x = Scontinue ->
      step (State f x (Kloop1 s1 s2 k) e le m, pm)
           E0 (State f s2 (Kloop2 s1 s2 k) e le m, pm)
  | step_break_loop1:  forall f s1 s2 k e le m pm,
      step (State f Sbreak (Kloop1 s1 s2 k) e le m, pm)
           E0 (State f Sskip k e le m, pm)
  | step_skip_loop2: forall f s1 s2 k e le m pm,
      step (State f Sskip (Kloop2 s1 s2 k) e le m, pm)
           E0 (State f (Sloop s1 s2) k e le m, pm)
  | step_break_loop2: forall f s1 s2 k e le m pm,
      step (State f Sbreak (Kloop2 s1 s2 k) e le m, pm)
           E0 (State f Sskip k e le m, pm)

  | step_return_0: forall f k e le m m' pm,
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      step (State f (Sreturn None) k e le m, pm)
           E0 (Returnstate Vundef (call_cont k) m', pm)
  | step_return_1: forall f a k e le m v v' m' pm,
      eval_expr e le m pm a v ->
      sem_cast v (typeof a) f.(fn_return) m = Some v' \/
      sem_cast v (typeof a) f.(fn_return) pm = Some v' ->
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      step (State f (Sreturn (Some a)) k e le m, pm)
           E0 (Returnstate v' (call_cont k) m', pm)
  | step_skip_call: forall f k e le m m' pm,
      is_call_cont k ->
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      step (State f Sskip k e le m, pm)
           E0 (Returnstate Vundef k m', pm)

  | step_switch: forall f a sl k e le m pm v n,
      eval_expr e le m pm a v ->
      sem_switch_arg v (typeof a) = Some n ->
      step (State f (Sswitch a sl) k e le m, pm)
           E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m, pm)
  | step_skip_break_switch: forall f x k e le m pm,
      x = Sskip \/ x = Sbreak ->
      step (State f x (Kswitch k) e le m, pm)
           E0 (State f Sskip k e le m, pm)
  | step_continue_switch: forall f k e le m pm,
      step (State f Scontinue (Kswitch k) e le m, pm)
           E0 (State f Scontinue k e le m, pm)

  | step_label: forall f lbl s k e le m pm,
      step (State f (Slabel lbl s) k e le m, pm)
           E0 (State f s k e le m, pm)

  | step_goto: forall f lbl k e le m pm s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
      step (State f (Sgoto lbl) k e le m, pm)
           E0 (State f s' k' e le m, pm)

  | step_internal_function: forall vf f vargs k m pm e le m1,
    forall FIND: Genv.find_funct ge vf = Some (Internal f),
      function_entry f vargs m e le m1 ->
      step (Callstate vf vargs k m, pm)
           E0 (State f f.(fn_body) k e le m1, pm)

  | step_external_function: forall vf ef targs tres cconv vargs k m pm vres t m',
    forall FIND: Genv.find_funct ge vf = Some (External ef targs tres cconv),
      external_call ef ge vargs m t vres m' ->
      step (Callstate vf vargs k m, pm)
           t (Returnstate vres k m', pm)

  | step_returnstate: forall v optid f e le k pm m,
      step (Returnstate v (Kcall optid f e le k) m, pm)
           E0 (State f Sskip k e (set_opttemp optid v le) m, pm).

  Inductive initial_state: c_query * mem -> Clight.state * mem -> Prop :=
  | initial_state_intro: forall vf f targs tres tcc vargs m pm,
      Genv.find_funct ge vf = Some (Internal f) ->
      type_of_function f = Tfunction targs tres tcc ->
      val_casted_list vargs targs ->
      Sup.sup_include (Genv.genv_sup ge) (Mem.support m) ->
      initial_state
        (cq vf (signature_of_type targs tres tcc) vargs m, pm)
        (Callstate vf vargs Kstop m, pm).

  Inductive at_external: Clight.state * mem -> c_query * mem -> Prop :=
  | at_external_intro name sg targs tres cconv vf vargs k m pm:
      let f := External (EF_external name sg) targs tres cconv in
      Genv.find_funct ge vf = Some f ->
      at_external
        (Callstate vf vargs k m, pm)
        (cq vf sg vargs m, pm).

  (** Re-entrant calls are possible *)
  Inductive after_external: Clight.state * mem -> c_reply * mem -> Clight.state * mem -> Prop :=
  | after_external_intro vf vargs k m pm vres m' pm':
      after_external
        (Callstate vf vargs k m, pm)
        (cr vres m', pm')
        (Returnstate vres k m', pm').

  Inductive final_state: Clight.state * mem -> c_reply * mem -> Prop :=
  | final_state_intro: forall r m pm,
      final_state
        (Returnstate r Kstop m, pm)
        (cr r m, pm).

End ClightM.

Definition estep1 (ge: genv) := step ge (function_entry1 ge).
Definition estep2 (ge: genv) := step ge (function_entry2 ge).

Program Definition eclight1 (p: program) :=
  {|
    init_pstate := Mem.empty;
    esem := Semantics_gen estep1
                         initial_state
                         at_external
                         (fun _ => after_external)
                         (fun _ => final_state)
                         globalenv p
  |}.

Program Definition eclight2 (p: program) :=
  {|
    init_pstate := Mem.empty;
    esem := Semantics_gen estep2
                         initial_state
                         at_external
                         (fun _ => after_external)
                         (fun _ => final_state)
                         globalenv p
  |}.
