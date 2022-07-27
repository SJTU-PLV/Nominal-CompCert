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
(* embed a regular type into a pointed set *)
Definition pset_embed (T: Type) :=
  {|
    pset_type := option T;
    pset_init := None;
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
    (* internal steps are free to modify the state *)
    w_int_step := {| rel s t := True; |};
    (* external steps maintain the state *)
    w_ext_step := {| rel := eq |};
  |}.

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

(* Generate a world that corresponds to the world in vanilla simulation
   conventions, where the replies are matched at the same world as in the
   queries and the environment is free to choose a new world to match queries *)
Program Definition world_embed (T: Type) :=
  {|
    w_type := pset_embed T;
    w_int_step := {| rel := eq |};
    w_ext_step := {| rel s t := True |};
  |}.

Program Definition world_symtbl :=
  {|
    w_type := pset_embed Genv.symtbl;
    w_int_step := {| rel := eq |};
    w_ext_step := {| rel := eq |};
  |}.

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

Definition semantics_fbk {K: PSet} {liA liB} (L: liA +-> liB@K) : liA +-> liB :=
  {|
    pstate := pstate L * K;
    esem := $L
  |}.

Instance li_func_unit {liA}: LiFunc liA (liA@unit).
Proof. split; intros; apply X. Defined.

Definition semantics_embed {liA liB} (L: semantics liA liB) : liA +-> liB :=
  {|
    pstate := pset_unit;
    esem := $L;
  |}.

(** ** Simulations *)
Set Implicit Arguments.
Require Import Relation_Operators.

Module ST.

  Record callconv  {li1 li2} :=
    mk_callconv {
      ccworld : world;
      (* match_senv : ccworld -> Genv.symtbl -> Genv.symtbl -> Type; *)
      match_query : ccworld -> query li1 -> query li2 -> Prop;
      match_reply : ccworld -> reply li1 -> reply li2 -> Prop;
    }.
  Arguments callconv: clear implicits.

  Program Definition callconv_lift {li1 li2}
          (cc: callconv li1 li2) (U V: PSet) : callconv (li1@U) (li2@V) :=
    {|
      ccworld := (ccworld cc * (pset_world U) * (pset_world V))%world;
      (* match_senv '(w, u, v) se1 se2 := match_senv cc w se1 se2; *)
      match_query '(w, u, v) '(q1, uq) '(q2, vq) :=
        match_query cc w q1 q2 /\ u = uq /\ v = vq;
      match_reply '(w, u, v) '(q1, uq) '(q2, vq) :=
        match_reply cc w q1 q2 /\ u = uq /\ v = vq;
    |}.

  Program Definition cc_compose {li1 li2 li3}
          (cc12: callconv li1 li2) (cc23: callconv li2 li3) :=
    {|
      ccworld := ccworld cc12 * ccworld cc23;
      (* match_senv '(w12, w23) se1 se3 := *)
      (*   { se2 & (match_senv cc12 w12 se1 se2 * match_senv cc23 w23 se2 se3)%type }; *)
      match_query '(w12, w23) q1 q3 :=
      exists q2,
        match_query cc12 w12 q1 q2 /\
        match_query cc23 w23 q2 q3;
      match_reply '(w12, w23) r1 r3 :=
      exists r2,
        match_reply cc12 w12 r1 r2 /\
        match_reply cc23 w23 r2 r3;
    |}.

  (** Stateful Simulation *)
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
    Arguments fsim_properties : clear implicits.

    Lemma fsim_simulation':
      forall L1 L2 index order match_states, fsim_properties L1 L2 index order match_states ->
      forall i s1 t s1', Step L1 s1 t s1' ->
      forall wA wB s2, match_states wA wB i s1 s2 ->
      exists i' wA' wB', wA :-> wA' /\ wB *-> wB' /\
      ((exists s2', Plus L2 s2 t s2' /\ match_states wA' wB' i' s1' s2')
      \/ (order i' i /\ t = E0 /\ match_states wA' wB' i' s1' s2)).
    Proof.
      intros. exploit @fsim_simulation; eauto.
      intros (i' & s2' & A & wai & wbi & Hai & Hbi & B).
      exists i', wai, wbi. repeat split; eauto.
      destruct A.
      left; exists s2'; auto.
      destruct H2. inv H2.
      right; eauto.
      left; exists s2'; split; auto. econstructor; eauto.
    Qed.

    Section SIMULATION_SEQUENCES.

      Context L1 L2 index order match_states
              (S: fsim_properties L1 L2 index order match_states).

      Lemma simulation_star:
        forall s1 t s1', Star L1 s1 t s1' ->
        forall wA wB i s2, match_states wA wB i s1 s2 ->
        exists wA' wB' i', exists s2', Star L2 s2 t s2' /\
        wA :-> wA' /\ wB *-> wB' /\ match_states wA' wB' i' s1' s2'.
      Proof.
        induction 1; intros.
        eexists _, _, i; exists s2; repeat split; auto. apply star_refl.
        reflexivity. reflexivity. assumption.
        exploit fsim_simulation; eauto.
        intros (i' & s2' & A & wai & wbi & Hai & Hbi & B).
        exploit IHstar; eauto.
        intros (waj & wbj & i'' & s2'' & Hx & Haj & Hbj & C).
        exists waj, wbj, i''; exists s2''; repeat split; auto.
        eapply star_trans; eauto.
        intuition auto. apply plus_star; auto.
        all: etransitivity; eauto.
      Qed.

      Lemma simulation_plus:
        forall s1 t s1', Plus L1 s1 t s1' ->
        forall wA wB i s2, match_states wA wB i s1 s2 ->
        exists wA' wB' i', wA :-> wA' /\ wB *-> wB' /\
        ((exists s2', Plus L2 s2 t s2' /\ match_states wA' wB' i' s1' s2') \/
        clos_trans _ order i' i /\ t = E0 /\ match_states wA' wB' i' s1' s2).
      Proof.
        induction 1 using plus_ind2; intros.
        (* base case *)
        - exploit fsim_simulation'; eauto.
          intros (i' & wai & wbi & Hai & Hbi & A).
          exists wai, wbi, i'. repeat split; eauto.
          destruct A.
          left; auto.
          right; intuition.
        (* inductive case *)
        - exploit fsim_simulation'; eauto.
          intros (i' & wai & wbi & Hai & Hbi & A).
          destruct A as [[s2' [A B]] | [A [B C]]].
          + exploit simulation_star. apply plus_star; eauto. eauto.
            intros (waj & wbj & i'' & s2'' & P & Haj & Hbj & Q).
            exists waj, wbj, i''. repeat split. 1-2: etransitivity; eauto.
            left; exists s2''; split; auto. eapply plus_star_trans; eauto.

          + exploit IHplus; eauto.
            intros (waj & wbj & i'' & Haj & Hbj & P).
            destruct P as [[s2'' [P Q]] | [P [Q R]]].
            * subst. simpl.
              exists waj, wbj, i''. repeat split. 1-2: etransitivity; eauto.
              left; exists s2''; auto.
            * subst. simpl.
              exists waj, wbj, i''. repeat split. 1-2: etransitivity; eauto.
              right; intuition auto.
              eapply t_trans; eauto. eapply t_step; eauto.
      Qed.

    End SIMULATION_SEQUENCES.
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
        fsim_lts wA wB se:
          fsim_invariant wA wB ->
          fsim_properties ccA ccB wA wB fsim_invariant (activate L1 se) (activate L2 se)
                          fsim_index fsim_order (fsim_match_states se);
        fsim_order_wf:
          well_founded fsim_order;
      }.
  Arguments Forward_simulation {_ _ ccA _ _ ccB L1 L2 fsim_index}.

  Definition forward_simulation {liA1 liA2} ccA {liB1 liB2} ccB L1 L2 :=
    inhabited (@fsim_components liA1 liA2 ccA liB1 liB2 ccB L1 L2).

End ST.

(** Simulations between components with encapsulated states *)
Module E.

  Definition forward_simulation {liA1 liA2} (ccA: ST.callconv liA1 liA2)
             {liB1 liB2} (ccB: ST.callconv liB1 liB2)
             (L1: liA1 +-> liB1) (L2: liA2 +-> liB2) :=
    ST.forward_simulation ccA (ST.callconv_lift ccB (pstate L1) (pstate L2))
                       (esem L1) (esem L2).

End E.

(** ** Properties *)

(** *** Embedding Stateless Simulations *)

Definition callconv_embed {liA liB} (cc: callconv liA liB): ST.callconv liA liB :=
  {|
    ST.ccworld := world_embed (ccworld cc);
    ST.match_query ow q1 q2 :=
      match ow with
      | Some w => match_query cc w q1 q2
      | None => False
      end;
    ST.match_reply ow r1 r2 :=
      match ow with
      | Some w => match_reply cc w r1 r2
      | None => False
      end;
  |}.

Generalizable All Variables.

(* TODO: we cannot prove this property until we figure out the problem about
   symbol tables *)
Lemma fsim_embed `(ccA: callconv liA1 liA2) `(ccB: callconv liB1 liB2) L1 L2:
  forward_simulation ccA ccB L1 L2 ->
  E.forward_simulation (callconv_embed ccA) (callconv_embed ccB)
                       (semantics_embed L1) (semantics_embed L2).
Proof.
Admitted.

(** *** Lifting Simulations with Additional States *)

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
      (fun se '(wa, k1a, k2a) '(wb, k1b, k2b) i '(s1, k1) '(s2, k2) =>
         ST.fsim_match_states X se wa wb i s1 s2 /\
           k1a = k1 /\ k1b = k1 /\ k2a = k2 /\ k2b = k2)
      (fun '(wa, k1a, k2a) '(wb, k1b, k2b) => ST.fsim_invariant X wa wb /\ k1a = k1b /\ k2a = k2b).
    - intros [[wa k1a] k2a] [[wb k1b] k2b] (INV & -> & ->) [[wb' k1b'] k2b'] W.
      destruct W as [[W U] V]. inv U. inv V. repeat split; eauto.
      eapply ST.fsim_invariant_env_step; eauto.
    - apply X.
    - cbn. repeat split; eauto. apply X.
    - intros i. cbn. apply X.
    - intros [[wa k1a] k2a] [[wb k1b] k2b] se (I & -> & ->). split; cbn.
      + intros. prod_crush. subst.
        pose proof (ST.fsim_lts X _ _ se I).
        edestruct @ST.fsim_match_initial_states as (idx & s' & Hs' & Hs); eauto.
        destruct Hs as (wa' & wb'' & W1 & W2 & HS).
        eexists idx, (s', _). repeat split; eauto.
        eexists (wa', _, _), (wb'', _, _). repeat split; eauto.
      + intros. prod_crush. subst.
        pose proof (ST.fsim_lts X _ _ se I).
        edestruct @ST.fsim_match_final_states as (r' & H' & Hr'); eauto.
        destruct Hr' as (wb' & W & Hr' & INV).
        eexists (r', _). repeat split; eauto.
        eexists (wb', _, _). repeat split; eauto.
      + intros. prod_crush. subst.
        pose proof (ST.fsim_lts X _ _ se I).
        edestruct @ST.fsim_match_external as (q' & H' & wa' & WA & Hq' & HH); eauto.
        eexists (q', _). repeat split; eauto.
        eexists (wa', _, _). repeat split; eauto.
        intros. prod_crush. subst.
        edestruct HH as (i' & s2' & Haft & Hs); eauto.
        destruct Hs as (wa'' & wb' & WA' & WB & HS).
        eexists i', (s2', _). repeat split; eauto.
        eexists (wa'', _, _), (wb', _, _). repeat split; eauto.
      + intros. prod_crush. subst.
        pose proof (ST.fsim_lts X _ _ se I).
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
  ST.forward_simulation (ST.callconv_lift ccA K1 K2)
                        (ST.callconv_lift ccB K1 K2)
                        (L1@K1) (L2@K2).
Proof.
  intros [H]. apply st_fsim_lift'. apply H.
Qed.

(** *** Composition of Stateful Simulations *)

Section FSIM.
  Context `(ccA: ST.callconv liA1 liA2)
          `(ccB: ST.callconv liB1 liB2)
          `(ccC: ST.callconv liC1 liC2)
          (L1s: semantics liB1 liC1) (L2s: semantics liA1 liB1)
          (L1t: semantics liB2 liC2) (L2t: semantics liA2 liB2).
  Context (HL1: ST.fsim_components ccB ccC L1s L1t)
          (HL2: ST.fsim_components ccA ccB L2s L2t)
          (wA : ST.ccworld ccA) (wC: ST.ccworld ccC)
          (se: Genv.symtbl).

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
    ST.fsim_match_states HL1 se wb wc i1 s1 s1' ->
    ST.fsim_invariant HL2 wa wb ->
    match_states wa wc (index1 i1) (st1 L1s L2s s1) (st1 L1t L2t s1')
  | match_st2 wa wb wc i1 i2 s1 t1 s2 t2 :
    ST.fsim_match_states HL2 se wa wb i2 s2 t2 ->
    (forall r1 r2 (s1' : state L1s) wb',
        wb *-> wb' ->
        ST.match_reply ccB wb' r1 r2 ->
        after_external (L1s se) s1 r1 s1' ->
        exists (i' : ST.fsim_index HL1) (t1' : state L1t),
          after_external (L1t se) t1 r2 t1' /\
            exists wb'' wc', wb' :-> wb'' /\ wc *-> wc' /\
            ST.fsim_match_states HL1 se wb'' wc' i' s1' t1') ->
    match_states wa wc (index2 i1 i2) (st2 L1s L2s s1 s2) (st2 L1t L2t t1 t2).

  Definition inv : ST.ccworld ccA -> ST.ccworld ccC -> Prop :=
    fun wa wc => exists wb, ST.fsim_invariant HL1 wb wc /\ ST.fsim_invariant HL2 wa wb.

  Lemma st_fsim_comp' sk sk':
    inv wA wC ->
    ST.fsim_properties ccA ccC wA wC inv
                       (comp_semantics' L1s L2s sk se)
                       (comp_semantics' L1t L2t sk' se)
                       index order match_states.
  Proof.
    intros (wB & INV1 & INV2). split; cbn.
    - intros q1 q2 s1 wC' WC Hq H. inv H.
      pose proof (ST.fsim_lts HL1 _ _ se INV1).
      edestruct @ST.fsim_match_initial_states as (idx & s' & Hs' & Hs); eauto.
      destruct Hs as (wB' & wC'' & W1 & W2 & HS).
      exists (index1 idx), (st1 L1t L2t s').
      split. econstructor; eauto.
      exists wA, wC''. repeat split; eauto. reflexivity.
      econstructor. apply HS. eapply ST.fsim_invariant_env_step; eauto.
    - intros wa wb i s1 s2 r1 Hs Hf. inv Hf. inv Hs.
      rename wb into wc. rename wb0 into wb.
      pose proof (ST.fsim_lts HL1 _ _ se INV1).
      edestruct @ST.fsim_match_final_states as (r' & H' & Hr'); eauto.
      destruct Hr' as (wc' & W & Hr' & INV).
      exists r'. split. econstructor; eauto.
      exists wc'. repeat split; eauto.
      exists wb. split; eauto.
    - intros wa wc i s1 s2 q1 Hs H. inv H. inv Hs.
      pose proof (ST.fsim_lts HL2 _ _ se INV2).
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
      + pose proof (ST.fsim_lts HL1 _ _ se INV1).
        edestruct @ST.fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto.
        destruct Hs' as (wb' & wc' & WB & WC & HS).
        exists (index1 idx'), (st1 L1t L2t s2'). split.
        * destruct Hs2'; [ left | right ].
          apply plus_internal1. auto.
          split. apply star_internal1. apply H2. constructor; apply H2.
        * exists wa, wc'. repeat split; eauto. reflexivity.
          econstructor; eauto. eapply @ST.fsim_invariant_env_step; eauto.
      + pose proof (ST.fsim_lts HL2 _ _ se INV2).
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
      + pose proof (ST.fsim_lts HL1 _ _ se INV1).
        edestruct @ST.fsim_match_external as (q' & H' & wb' & WB & Hq' & HH); eauto.
        pose proof (ST.fsim_lts HL2 _ _ se H6).
        edestruct @ST.fsim_match_initial_states as (i2 & s' & Hs' & Hs); eauto.
        destruct Hs as (wa' & wb'' & WA & WB' & Hs).
        exists (index2 i1 i2), (st2 L1t L2t s1' s'). split.
        * left. apply plus_one. eapply step_push; eauto.
        * exists wa', wc. repeat split; eauto. reflexivity.
          econstructor; eauto.
          intros r1 r2 sr wb''' WB'' HR Haft.
          specialize (HH r1 r2 sr wb'''). apply HH. etransitivity; eauto.
          exact HR. exact Haft.
      + pose proof (ST.fsim_lts HL2 _ _ se INV2).
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
    - intros wa wc se INV. eapply st_fsim_comp'; eauto.
    - clear - Ha Hb. intros [|].
      + induction (ST.fsim_order_wf Ha f). constructor.
        intros. inv H1. apply H0. auto.
      + induction (ST.fsim_order_wf Hb f0). constructor.
        intros. inv H1. apply H0. auto.
  Qed.

End COMP.

(** *** Composition of Components with Encapsulated States *)
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
    unfold E.forward_simulation in *. unfold comp_esem in *.
    apply st_fsim_lift with (K1:=pstate L2s) (K2:=pstate L2t) in HL1.
    exploit @st_fsim_comp. exact HL1. exact HL2.
  Admitted.
End COMP.

(** *** Composition of Stateful Simulation Conventions *)

Section COMP_FSIM.

  Context `(ccA1: ST.callconv liAs liAn) `(ccA2: ST.callconv liAn liAf)
          `(ccB1: ST.callconv liBs liBn) `(ccB2: ST.callconv liBn liBf)
          (Ls: semantics liAs liBs) (Ln: semantics liAn liBn) (Lf: semantics liAf liBf).
  Context (H1: ST.fsim_components ccA1 ccB1 Ls Ln)
          (H2: ST.fsim_components ccA2 ccB2 Ln Lf).

  Inductive compose_fsim_match_states: Genv.symtbl ->
    ST.ccworld (ST.cc_compose ccA1 ccA2) ->
    ST.ccworld (ST.cc_compose ccB1 ccB2) ->
    (ST.fsim_index H2 * ST.fsim_index H1) ->
    state Ls -> state Lf -> Prop :=
  | compose_match_states_intro se s1 s2 s3 i1 i2 wa1 wa2 wb1 wb2:
    ST.fsim_match_states H1 se wa1 wb1 i1 s1 s2 ->
    ST.fsim_match_states H2 se wa2 wb2 i2 s2 s3 ->
    compose_fsim_match_states se (wa1, wa2) (wb1, wb2) (i2, i1) s1 s3.

  Inductive compose_fsim_inv:
    ST.ccworld (ST.cc_compose ccA1 ccA2) ->
    ST.ccworld (ST.cc_compose ccB1 ccB2) -> Prop :=
  | compose_fsim_inv_intro wa1 wa2 wb1 wb2:
    ST.fsim_invariant H1 wa1 wb1 -> ST.fsim_invariant H2 wa2 wb2 ->
    compose_fsim_inv (wa1, wa2) (wb1, wb2).

  Lemma st_compose_fsim_components:
    ST.fsim_components (ST.cc_compose ccA1 ccA2)
                       (ST.cc_compose ccB1 ccB2)
                       Ls Lf.
  Proof.
    (* destruct H1 as [ index1 order1 match_states1 inv1 A1 B1 C1 D1 E1 F1 ]. *)
    (* destruct H2 as [ index2 order2 match_states2 inv2 A2 B2 C2 D2 E2 F2 ]. *)
    (* set (ff_index := (index2 * index1)%type). *)
    set (ff_order := lex_ord (Relation_Operators.clos_trans
                                _ (ST.fsim_order H2)) (ST.fsim_order H1)).
    (* set (ff_match_states := *)
    (*        fun se1 se3 '(ose, wa1, wa2) '(o, wb1, wb2) '(i2, i1) s1 s3 => *)
    (*          match ose with *)
    (*          | Some se2 => *)
    (*              exists s2, match_states1 se1 se2 wa1 wb1 i1 s1 s2 /\ *)
    (*                      match_states2 se2 se3 wa2 wb2 i2 s2 s3 *)
    (*          | None => False *)
    (*          end). *)

    (* set (ff_inv := fun '(x, wa1, wa2) '(y, wb1, wb2) => inv1 wa1 wb1 /\ inv2 wa2 wb2). *)

    (* replace (ST.fsim_index H2 * ST.fsim_index H1)%type *)
    (*   with ff_index in ff_match_states. *)
    (* 2: { subst ff_index. rewrite X1. rewrite X2. reflexivity. } *)
    (* clear X1 X2. *)
    apply ST.Forward_simulation with ff_order compose_fsim_match_states compose_fsim_inv.
    - intros [wa1 wa2] [wb1 wb2] I [wb1' wb2'] [X1 X2].
      inv I. econstructor.
      eapply (ST.fsim_invariant_env_step H1); eauto.
      eapply (ST.fsim_invariant_env_step H2); eauto.
    - rewrite (ST.fsim_skel H1); apply (ST.fsim_skel H2).
    - econstructor. apply (ST.fsim_initial_world H1).
      apply (ST.fsim_initial_world).
    - intros i. rewrite (ST.fsim_footprint H1). apply (ST.fsim_footprint H2).
    - intros [wa1 wa2] [wb1 wb2] se I. inv I.
      pose proof (ST.fsim_lts H1 wa1 wb1 se H4) as X1.
      pose proof (ST.fsim_lts H2 wa2 wb2 se H6) as X2.
      constructor.
      + intros q1 q3 s1 (wb1' & wb2') (WB1 & WB2) (q2 & Hq12 & Hq23) Hi.
        edestruct (@ST.fsim_match_initial_states liAs) as (i & s2 & A & B); eauto.
        edestruct (@ST.fsim_match_initial_states liAn) as (i' & s3 & C & D); eauto.
        destruct B as (wa1' & wb1'' & WA1 & WB1' & B).
        destruct D as (wa2' & wb2'' & WA2 & WB2' & D).
        eexists (i', i), s3. split; eauto.
        eexists (wa1', wa2'), (wb1'', wb2''). repeat split; eauto.
        econstructor; eauto.
      + intros (wa1' & wa2') (wb1' & wb2') (i2, i1) s1 s3 r1 Hs H.
        inv Hs.
        edestruct (@ST.fsim_match_final_states liAs) as (r2 & Hr2 & A); eauto.
        edestruct (@ST.fsim_match_final_states liAn) as (r3 & Hr3 & B); eauto.
        destruct A as (wb1'' & WB1' & R1 & I1).
        destruct B as (wb2'' & WB2' & R2 & I2).
        exists r3. repeat split; eauto.
        exists (wb1'', wb2''). repeat split; eauto.
        econstructor; eauto.
      + intros (wa1' & wa2') (wb1' & wb2') (i2, i1) s1 s3 q1 Hs H.
        inv Hs.
        edestruct (@ST.fsim_match_external liAs) as (q2 & Hq2 & wax & Hwx & Hq12 & Hk12); eauto.
        edestruct (@ST.fsim_match_external liAn) as (q3 & Hq3 & way & Hwy & Hq23 & Hk23); eauto.
        exists q3. repeat split; eauto. exists (wax, way). repeat split; eauto.
        econstructor; eauto.
        intros r1 r3 s1' (wai, waj) (Hwi & Hwj) (r2 & Hr12 & Hr23) HH.
        edestruct Hk12 as (i2' & s2' & Hs2' & wam & wbm & Ham & Hbm & Hm); eauto.
        edestruct Hk23 as (i1' & s3' & Hs3' & wan & wbn & Han & Hbn & Hn); eauto.
        eexists (_, _), _. repeat split; eauto.
        eexists (_, _), (_, _). repeat split; eauto.
        econstructor; eauto.
      + intros s1 t s1' Hstep (wai & waj) (wbi & wbj) (i2, i1) s3 Hs.
        inv Hs.
        edestruct (@ST.fsim_simulation' liAs) as (i1' & waii & wbii & Hai & Hbi & Hx); eauto.
        destruct Hx as [[s2' [A B]] | [A [B C]]].
        * (* L2 makes one or several steps. *)
          edestruct (@ST.simulation_plus liAn) as (wak & wbk & i2' & Hak & Hbk & X); eauto.
          destruct X as [[s3' [P Q]] | [P [Q R]]].
          -- (* L3 makes one or several steps *)
            exists (i2', i1'); exists s3'; split.
            left; eauto.
            eexists (_, _), (_, _). repeat split; eauto.
            econstructor; eauto.
          -- (* L3 makes no step *)
            exists (i2', i1'); exists s3; split.
            right; split. subst t; apply star_refl. red. left. auto.
            eexists (_, _), (_, _). repeat split; eauto.
            econstructor; eauto.
        * (* L2 makes no step *)
          exists (i2, i1'); exists s3; split.
          right; split. subst t; apply star_refl. red. right. auto.
            eexists (_, _), (_, _). repeat split; eauto. 1-2: reflexivity.
            econstructor; eauto.
    - unfold ff_order.
      apply wf_lex_ord. apply Transitive_Closure.wf_clos_trans.
      eapply (ST.fsim_order_wf H2). eapply (ST.fsim_order_wf H1).
  Qed.

End COMP_FSIM.
