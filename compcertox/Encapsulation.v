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
    w_int_step := {| rel := OptionRel.option_le (fun _ _ => True) |};
    w_ext_step := {| rel := OptionRel.option_le eq |};
  |}.

Program Definition world_symtbl :=
  {|
    w_type := pset_embed Genv.symtbl;
    w_int_step := {| rel := eq |};
    w_ext_step := {| rel := OptionRel.option_le eq |};
  |}.

(** ** Semantics with Encapsulation *)
Record esemantics {liA liB} := {
    pstate : PSet;              (** persistent state *)
    esem :> semantics liA (liB @ pstate)
  }.
Arguments esemantics : clear implicits.

Infix "+->" := esemantics (at level 70).

(** *** Composition *)

Definition comp_esem' {liA liB liC} (L1: liB +-> liC) (L2: liA +-> liB) sk : liA +-> liC :=
  {|
    pstate := pstate L1 * pstate L2;
    esem := $(comp_semantics' (L1 @ pstate L2) L2 sk);
  |}.

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
    pstate := K * pstate L;
    esem := $L
  |}.

Instance li_func_unit {liA}: LiFunc liA (liA@unit).
Proof. split; intros; apply X. Defined.

Definition semantics_embed {liA liB} (L: semantics liA liB) : liA +-> liB :=
  {|
    pstate := pset_unit;
    esem := $L;
  |}.

(** ** Stateful Simulation Convention and Simulation *)
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

(** Normalized Stateful Simulation *)
Module STCAT.
  Definition forward_simulation {liA1 liA2} (ccA: ST.callconv liA1 liA2)
             {liB1 liB2} (ccB: ST.callconv liB1 liB2) L1 L2 :=
    ST.forward_simulation ccA ccB (normalize_sem L1) (normalize_sem L2).
End STCAT.

(** Simulations between components with encapsulated states *)
Module E.
  Definition forward_simulation {liA1 liA2} (ccA: ST.callconv liA1 liA2)
             {liB1 liB2} (ccB: ST.callconv liB1 liB2)
             (L1: liA1 +-> liB1) (L2: liA2 +-> liB2) :=
    STCAT.forward_simulation ccA (ST.callconv_lift ccB (pstate L1) (pstate L2)) L1 L2.
End E.

(** * Properties about Stateful Simulations *)

(** ** Embedding Stateless Simulations *)

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
Notation "& cc" := (callconv_embed cc) (at level 0).

Generalizable All Variables.

(* TODO: we cannot prove this property until we figure out the problem about
   symbol tables *)
(** Lemma 3.8 *)
Lemma fsim_embed `(ccA: callconv liA1 liA2) `(ccB: callconv liB1 liB2) L1 L2:
  forward_simulation ccA ccB L1 L2 ->
  ST.forward_simulation &ccA &ccB L1 L2.
Proof.
Admitted.

(** ** Lifting Simulations with Additional States *)

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

(** ** Composition of Stateful Simulations *)

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

  Lemma st_fsim_lcomp' sk sk':
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

  (** Lemma 3.9 *)
  Lemma st_fsim_lcomp : ST.forward_simulation ccA ccC Ls Lt.
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
    - intros wa wc se INV. eapply st_fsim_lcomp'; eauto.
    - clear - Ha Hb. intros [|].
      + induction (ST.fsim_order_wf Ha f). constructor.
        intros. inv H1. apply H0. auto.
      + induction (ST.fsim_order_wf Hb f0). constructor.
        intros. inv H1. apply H0. auto.
  Qed.

  (* TODO: clean up the copy-paste *)
  Lemma st_fsim_lcomp_sk sk:
    Linking.linkorder (skel L1s) sk ->
    Linking.linkorder (skel L2s) sk ->
    ST.forward_simulation ccA ccC (comp_semantics' L1s L2s sk) (comp_semantics' L1t L2t sk).
  Proof.
    intros H1 H2.
    destruct HL1 as [Ha]. destruct HL2 as [Hb].
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
    - intros wa wc se INV. eapply st_fsim_lcomp'; eauto.
    - clear - Ha Hb. intros [|].
      + induction (ST.fsim_order_wf Ha f). constructor.
        intros. inv H1. apply H0. auto.
      + induction (ST.fsim_order_wf Hb f0). constructor.
        intros. inv H1. apply H0. auto.
  Qed.
End COMP.

(** ** Composition of Stateful Simulation Conventions *)

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

  Lemma st_fsim_vcomp':
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

Lemma st_fsim_vcomp
  `(ccA1: ST.callconv liAs liAn) `(ccA2: ST.callconv liAn liAf)
  `(ccB1: ST.callconv liBs liBn) `(ccB2: ST.callconv liBn liBf)
  (Ls: semantics liAs liBs) (Ln: semantics liAn liBn) (Lf: semantics liAf liBf):
  ST.forward_simulation ccA1 ccB1 Ls Ln ->
  ST.forward_simulation ccA2 ccB2 Ln Lf ->
  ST.forward_simulation (ST.cc_compose ccA1 ccA2) (ST.cc_compose ccB1 ccB2) Ls Lf.
Proof.
  intros [X] [Y]. constructor. eapply st_fsim_vcomp'; eauto.
Qed.

(** ** Left and Right Unit Laws *)

Section ID_FSIM.

  Context `(cc: ST.callconv liA liB) (sk: AST.program unit unit).
  Inductive sf_ms: ST.ccworld cc ->  ST.ccworld cc ->
                   @state liA _ (id_semantics sk) ->
                   @state liB _ (id_semantics sk) -> Prop :=
  | sf_ms_q w q1 q2:
    ST.match_query cc w q1 q2 -> sf_ms w w (st_q q1) (st_q q2)
  | sf_ms_r w r1 r2:
    ST.match_reply cc w r1 r2 -> sf_ms w w (st_r r1) (st_r r2).

  Lemma id_self_fsim :
    ST.forward_simulation cc cc (id_semantics sk) (id_semantics sk).
  Proof.
    constructor.
    eapply ST.Forward_simulation with (ltof _ (fun (_:unit) => 0))
                                      (fun _ wa wb _ s1 s2 => sf_ms wa wb s1 s2)
                                      (fun w1 w2 => w1 :-> w2); try reflexivity.
    - intros. etransitivity; eauto.
    - intros wa wb se Hw. constructor.
      + intros q1 q2 s1 wb1 Hb Hq H. inv H. exists tt.
        eexists. split. constructor.
        exists wb1, wb1. repeat split; try easy.
        etransitivity; eauto. now constructor.
      + intros wa1 wb1 [] s1 s2 r1 Hs H. inv H. inv Hs.
        eexists. split. constructor.
        exists wb1. repeat split; easy.
      + intros wa1 wb1 [] s1 s2 q1 Hs H. inv H. inv Hs.
        eexists. split. constructor.
        exists wb1. split. reflexivity. split. apply H2.
        intros r1 r2 s1' wb2 Hb Hr H. inv H.
        eexists tt, _. split. constructor.
        exists wb2, wb2. repeat split; eauto. reflexivity.
        now constructor.
      + intros. easy.
    - apply well_founded_ltof.
  Qed.

End ID_FSIM.

Section CAT_SIM.

  Lemma st_normalize_fsim `(ccA: ST.callconv liA1 liA2)
        `(ccB: ST.callconv liB1 liB2) L1 L2:
    ST.forward_simulation ccA ccB L1 L2 ->
    STCAT.forward_simulation ccA ccB L1 L2.
  Proof.
    intros H. unfold STCAT.forward_simulation, normalize_sem.
    assert (Hsk: skel L1 = skel L2).
    { destruct H. apply (ST.fsim_skel X). }
    unfold left_comp_id, right_comp_id. rewrite Hsk.
    eapply st_fsim_lcomp_sk.
    - apply id_self_fsim.
    - eapply st_fsim_lcomp_sk.
      + exact H.
      + apply id_self_fsim.
      + rewrite Hsk. apply Linking.linkorder_refl.
      + rewrite <- Hsk. apply CategoricalComp.id_skel_order.
    - apply CategoricalComp.id_skel_order.
    - apply Linking.linkorder_refl.
  Qed.

  Lemma st_fsim_left_unit1 `(L: semantics liA liB):
    STCAT.forward_simulation &1 &1 L (1 o L).
  Proof. apply fsim_embed. apply CAT.left_unit_1. Qed.

  Lemma st_fsim_left_unit2 `(L: semantics liA liB):
    STCAT.forward_simulation &1 &1 (1 o L) L.
  Proof. apply fsim_embed. apply CAT.left_unit_2. Qed.

  Lemma st_fsim_right_unit1 `(L: semantics liA liB):
    STCAT.forward_simulation &1 &1 L (L o 1).
  Proof. apply fsim_embed. apply CAT.right_unit_1. Qed.

  Lemma st_fsim_right_unit2 `(L: semantics liA liB):
    STCAT.forward_simulation &1 &1 (L o 1) L.
  Proof. apply fsim_embed. apply CAT.right_unit_2. Qed.

  Lemma st_cat_fsim_lcomp_sk
        `(ccA: ST.callconv liA1 liA2)
        `(ccB: ST.callconv liB1 liB2)
        `(ccC: ST.callconv liC1 liC2)
        L1s L2s L1t L2t sk:
    STCAT.forward_simulation ccB ccC L1s L1t ->
    STCAT.forward_simulation ccA ccB L2s L2t ->
    Linking.linkorder (skel L1s) sk ->
    Linking.linkorder (skel L2s) sk ->
    STCAT.forward_simulation ccA ccC
                             (comp_semantics' L1s L2s sk)
                             (comp_semantics' L1t L2t sk).
  Proof.
    intros X Y HSK1 HSK2. exploit @st_fsim_lcomp_sk.
    apply X. apply Y. apply HSK1. apply HSK2. intros Z. clear X Y.
    unfold STCAT.forward_simulation.
    assert (HX: ST.forward_simulation
                &1 &1 (normalize_sem (comp_semantics' L1s L2s sk))
                      (comp_semantics' (normalize_sem L1s) (normalize_sem L2s) sk)).
    { apply fsim_embed. apply normalize_comp_fsim_sk1. }
    assert (HY: ST.forward_simulation
                &1 &1 (comp_semantics' (normalize_sem L1t) (normalize_sem L2t) sk)
                      (normalize_sem (comp_semantics' L1t L2t sk))).
    { apply fsim_embed. apply normalize_comp_fsim_sk2. }
    exploit @st_fsim_vcomp. apply HX. apply Z. intros HZ. clear HX Z.
    exploit @st_fsim_vcomp. apply HZ. apply HY. intros H. clear HZ HY.
  Admitted.

End CAT_SIM.

(** ** Refinement between Stateful Simulation Conventions *)

Definition st_ccref {li1 li2} (cc1 cc2: ST.callconv li1 li2) : Prop :=
  STCAT.forward_simulation cc2 cc1 1 1.

(** A simplified condition for sim. conv. refinement given the situation that
    their states are isomorphic *)
Section CCREF.

  Context {li1 li2} (ccA ccB: ST.callconv li1 li2).

  Variable F: ST.ccworld ccA -> ST.ccworld ccB.
  Variable G: ST.ccworld ccB -> ST.ccworld ccA.
  Hypothesis F_init: F (pset_init (ST.ccworld ccA)) = pset_init (ST.ccworld ccB).
  Hypothesis F_ext_step: forall x y, F x :-> F y -> x :-> y.
  Hypothesis F_int_step: forall x y, x *-> y -> F x *-> F y.
  Hypothesis FG_cancel: forall x, F (G x) = x.
  Hypothesis F_mq:
    forall wa q1 q2, ST.match_query ccB (F wa) q1 q2 -> ST.match_query ccA wa q1 q2.
  Hypothesis F_mr:
    forall wa r1 r2, ST.match_reply ccA wa r1 r2 -> ST.match_reply ccB (F wa) r1 r2.

  Inductive cc_inv: ST.ccworld ccA -> ST.ccworld ccB -> Prop :=
  | cc_inv_intro wa wb: F wa :-> wb -> cc_inv wa wb.
  Inductive cc_ms: ST.ccworld ccA -> ST.ccworld ccB -> @state li1 li1 1 -> @state li2 li2 1 -> Prop :=
  | cc_ms_q q1 q2 wa wb:
    F wa = wb -> ST.match_query ccB wb q1 q2 -> cc_ms wa wb (st_q q1) (st_q q2)
  | cc_ms_r r1 r2 wa wb:
    F wa = wb -> ST.match_reply ccB wb r1 r2 -> cc_ms wa wb (st_r r1) (st_r r2).

  Lemma st_ccref_intro: st_ccref ccB ccA.
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun _ wa wb _ => cc_ms wa wb)
      (fun wa wb => cc_inv wa wb); try easy.
    - intros. inv H. constructor. etransitivity; eauto.
    - constructor. rewrite F_init. reflexivity.
    - intros wa wb se I. inv I.
      constructor.
      + intros q1 q2 s1 wb1 Hb Hq Hx. exists tt. inv Hx. exists (st_q q2).
        split. constructor.
        exists (G wb1), wb1. repeat split; try easy.
        * apply F_ext_step. rewrite FG_cancel.
          etransitivity; eauto.
        * constructor. apply FG_cancel. apply Hq.
      + intros wa1 wb1 [] s1 s2 r1 Hs Hx. inv Hx.
        inv Hs. exists r2. split. constructor.
        exists (F wa1). repeat split; easy.
      + intros wa1 wb1 [] s1 s2 q1 Hs Hx. inv Hx. inv Hs.
        exists q2. split. constructor.
        exists wa1. split. reflexivity. split. eauto.
        intros r1 r2 s1' wa2 Ha2 Hr Hy.
        inv Hy. eexists tt, _. split. constructor.
        eexists wa2, (F wa2). repeat split; try easy.
        apply F_int_step. assumption.
        constructor; eauto.
      + intros. easy.
  Qed.

End CCREF.

(** ** Left and Right Unit Laws for Sim. Conv. *)

Section CC_UNIT.

  Context `(cc: ST.callconv liA liB).

  Inductive lu_inv: ST.ccworld cc -> ST.ccworld cc -> Prop :=
  | lu_inv_intro wa wb:
    wa :-> wb -> lu_inv wa wb.
  Inductive lu_ms: ST.ccworld cc -> ST.ccworld cc -> @state liA liA 1 -> @state liB liB 1 -> Prop :=
  | lu_ms_q w q1 q2:
    ST.match_query cc w q1 q2 -> lu_ms w w (st_q q1) (st_q q2)
  | lu_ms_r w r1 r2:
    ST.match_reply cc w r1 r2 -> lu_ms w w (st_r r1) (st_r r2).

  Lemma ccref_left_unit1:
    st_ccref cc (ST.cc_compose &1 cc).
  Proof.
    unfold st_ccref. apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun _ '(_, w1) w2 _ => lu_ms w1 w2)
      (fun '(_, w1) w2 => lu_inv w1 w2); try easy.
    - intros [? wa] wb I wb1 Hb. inv I.
      constructor. etransitivity; eauto.
    - intros [? wa] wb se I. constructor.
      + intros q1 q2 s1 wb1 Hb Hq H. inv H. exists tt, (st_q q2).
        split. constructor.
        exists (p, wb1), wb1. repeat split; try easy.
        inv I. etransitivity; eauto.
        constructor. eauto.
      + intros [? wa1] wb1 [] s1 s2 r1 Hs H. inv H. inv Hs.
        exists r2. split. constructor.
        exists wb1. repeat split; easy.
      + intros [? wa1] wb1 [] s1 s2 q1 Hs H. inv H. inv Hs.
        exists q2. split. constructor.
        exists (Some tt, wb1). repeat split; try easy.
        destruct p0; constructor. destruct c. easy.
        eexists. split; eauto. reflexivity.
        intros r1 r2 s1' [? wa2] [? Ha] Hr HX.
        destruct Hr as (x & HR1 & HR2).
        destruct p1; inv HR1. inv HX.
        exists tt, (st_r r2). repeat split.
        exists (Some tt, wa2), wa2.
        repeat split; eauto. destruct c. reflexivity. reflexivity.
        constructor. assumption.
      + intros. easy.
  Qed.

  Lemma ccref_left_unit2:
    st_ccref (ST.cc_compose &1 cc) cc.
  Proof.
    unfold st_ccref. apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun _ w1 '(_, w2) _ => lu_ms w1 w2)
      (fun w1 '(_, w2) => lu_inv w1 w2); try easy.
    - intros wa [? wb] I [? wb1] [? Hb]. inv I.
      constructor. etransitivity; eauto.
    - intros wa [? wb] se I. constructor.
      + intros q1 q2 s1 [? wb1] [_ Hb] Hq H. inv H. exists tt, (st_q q2).
        split. constructor.
        destruct Hq as (x & HQ1 & HQ2).
        destruct p0; inv HQ1.
        eexists wb1, (Some tt, wb1). repeat split; try easy.
        inv I. etransitivity; eauto.
        1-2: constructor; eauto.
      + intros wa1 [? wb1] [] s1 s2 r1 Hs H. inv H. inv Hs.
        exists r2. split. constructor.
        eexists (Some tt, wb1). repeat split; try easy.
        destruct p0; constructor; easy.
        eexists; split; eauto. reflexivity.
      + intros wa1 [? wb1] [] s1 s2 q1 Hs H. inv H. inv Hs.
        exists q2. split. constructor.
        exists wb1. repeat split; try easy.
        intros r1 r2 s1' wa2 Ha Hr HX. inv HX.
        exists tt, (st_r r2). repeat split.
        exists wa2, (Some tt, wa2).
        repeat split; eauto. reflexivity.
        destruct p0; now constructor.
        constructor. assumption.
      + intros. easy.
  Qed.

  Lemma ccref_right_unit1:
    st_ccref cc (ST.cc_compose cc &1).
  Proof.
  Proof.
    unfold st_ccref. apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun _ '(w1, _) w2 _ => lu_ms w1 w2)
      (fun '(w1, _) w2 => lu_inv w1 w2); try easy.
    - intros [wa _] wb I wb1 Hb. inv I.
      constructor. etransitivity; eauto.
    - intros [wa ?] wb se I. constructor.
      + intros q1 q2 s1 wb1 Hb Hq H. inv H. exists tt, (st_q q2).
        split. constructor.
        exists (wb1, p), wb1. repeat split; try easy.
        inv I. etransitivity; eauto.
        constructor. eauto.
      + intros [wa1 ?] wb1 [] s1 s2 r1 Hs H. inv H. inv Hs.
        exists r2. split. constructor.
        exists wb1. repeat split; easy.
      + intros [wa1 ?] wb1 [] s1 s2 q1 Hs H. inv H. inv Hs.
        exists q2. split. constructor.
        exists (wb1, Some tt). repeat split; try easy.
        destruct p0; constructor. destruct c. easy.
        eexists. split; eauto. reflexivity.
        intros r1 r2 s1' [wa2 ?] [Ha ?] Hr HX.
        destruct Hr as (x & HR1 & HR2).
        destruct p1; inv HR2. inv HX.
        exists tt, (st_r r2). repeat split.
        exists (wa2, Some tt), wa2.
        repeat split; eauto. reflexivity. destruct c. reflexivity.
        constructor. assumption.
      + intros. easy.
  Qed.

  Lemma ccref_right_unit2:
    st_ccref (ST.cc_compose cc &1) cc.
  Proof.
    unfold st_ccref. apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun _ w1 '(w2, _) _ => lu_ms w1 w2)
      (fun w1 '(w2, _) => lu_inv w1 w2); try easy.
    - intros wa [wb ?] I [wb1 ?] [Hb ?]. inv I.
      constructor. etransitivity; eauto.
    - intros wa [wb ?] se I. constructor.
      + intros q1 q2 s1 [wb1 ?] [Hb _] Hq H. inv H. exists tt, (st_q q2).
        split. constructor.
        destruct Hq as (x & HQ1 & HQ2).
        destruct p0; inv HQ2.
        eexists wb1, (wb1, Some tt). repeat split; try easy.
        inv I. etransitivity; eauto.
        all: constructor; eauto.
      + intros wa1 [wb1 ?] [] s1 s2 r1 Hs H. inv H. inv Hs.
        exists r2. split. constructor.
        eexists (wb1, Some tt). repeat split; try easy.
        destruct p0; now constructor.
        eexists; split; eauto. reflexivity.
      + intros wa1 [wb1 ?] [] s1 s2 q1 Hs H. inv H. inv Hs.
        exists q2. split. constructor.
        exists wb1. repeat split; try easy.
        intros r1 r2 s1' wa2 Ha Hr HX. inv HX.
        exists tt, (st_r r2). repeat split.
        exists wa2, (wa2, Some tt).
        repeat split; eauto. reflexivity.
        destruct p0; now constructor.
        constructor. assumption.
      + intros. easy.
  Qed.

End CC_UNIT.

(** ** Monotonicity of Sim. Conv. *)

Section CC_COMP.

  Context `(ccA: ST.callconv liA1 liA2)
          `(ccB: ST.callconv liB1 liB2)
          (L1: semantics liA1 liB1) (L2: semantics liA2 liB2)
          (HL: ST.fsim_components (ST.cc_compose ccA &1) (ST.cc_compose ccB &1) L1 L2).

  Inductive cc_comp_inv: ST.ccworld ccA -> ST.ccworld ccB -> Prop :=
  | cc_comp_inv_intro wa wb x y:
    ST.fsim_invariant HL (wa, x) (wb, y) ->
    cc_comp_inv wa wb.
  Inductive cc_comp_ms: Genv.symtbl -> ST.ccworld ccA -> ST.ccworld ccB ->
                        ST.fsim_index HL -> state L1 -> state L2 -> Prop :=
  | cc_comp_ms_intro se wa wb x y i s1 s2:
    ST.fsim_match_states HL se (wa, x) (wb, y) i s1 s2 ->
    cc_comp_ms se wa wb i s1 s2.

  Lemma fsim_cc_comp_right_unit': ST.fsim_components ccA ccB L1 L2.
  Proof.
    eapply ST.Forward_simulation with (ST.fsim_order HL) cc_comp_ms cc_comp_inv.
    - intros. inv H.
      econstructor. eapply (ST.fsim_invariant_env_step HL); eauto.
      split; eauto. reflexivity.
    - apply (ST.fsim_skel HL).
    - econstructor. apply (ST.fsim_initial_world HL).
    - apply (ST.fsim_footprint HL).
    - intros. inv H. exploit (ST.fsim_lts HL); eauto. intros X.
      constructor.
      + intros.
        edestruct (@ST.fsim_match_initial_states)
          as (? & ? & ? & ? & ? & ? & ? & ?); eauto.
        instantiate (1 := (_, Some tt)). split; eauto.
        destruct y. constructor. destruct c. reflexivity. constructor.
        econstructor. split; eauto. reflexivity.
        cbn in *. prod_crush. eexists _, _. split; eauto.
        eexists _, _. repeat split; eauto.
        econstructor. eauto.
      + intros. inv H.
        edestruct (@ST.fsim_match_final_states)
          as (? & ? & ? & ? & ? & ?); eauto.
        destruct x2. destruct H4. destruct H4. destruct p0; inv H6.
        destruct H3. eexists. split; eauto.
        eexists; repeat split; eauto. econstructor; eauto.
      + intros. inv H.
        edestruct (@ST.fsim_match_external)
          as (? & ? & ? & ? & ? & ?); eauto.
        destruct x2. destruct H3. destruct H4 as (? & ? & ?).
        destruct p0; inv H7.
        eexists; split; eauto. eexists; repeat split; eauto.
        intros.
        edestruct H5 as (? & ? & ? & ? & ? & ? & ? & ?); eauto.
        instantiate (1 := (_, Some tt)). split; eauto. constructor; easy.
        eexists; split; eauto. reflexivity.
        eexists _, _. split; eauto.
        destruct x4, x5. destruct H11. destruct H12.
        eexists _, _. repeat split; eauto. econstructor; eauto.
      + intros. inv H1.
        edestruct (@ST.fsim_simulation) as (? & ? & ? & ? & ? & ? & ? & ?); eauto.
        destruct x3, x4. destruct H3. destruct H4.
        eexists _, _. split; eauto.
        eexists _, _. repeat split; eauto. econstructor. eauto.
    - apply (ST.fsim_order_wf HL).
  Qed.

  Context (LH: ST.fsim_components (ST.cc_compose &1 ccA) (ST.cc_compose &1 ccB) L1 L2).

  Inductive cc_pmoc_inv: ST.ccworld ccA -> ST.ccworld ccB -> Prop :=
  | cc_pmoc_inv_intro wa wb x y:
    ST.fsim_invariant LH (x, wa) (y, wb) ->
    cc_pmoc_inv wa wb.
  Inductive cc_pmoc_ms: Genv.symtbl -> ST.ccworld ccA -> ST.ccworld ccB ->
                        ST.fsim_index LH -> state L1 -> state L2 -> Prop :=
  | cc_pmoc_ms_intro se wa wb x y i s1 s2:
    ST.fsim_match_states LH se (x, wa) (y, wb) i s1 s2 ->
    cc_pmoc_ms se wa wb i s1 s2.

  Lemma fsim_cc_comp_left_unit': ST.fsim_components ccA ccB L1 L2.
  Proof.
    eapply ST.Forward_simulation with (ST.fsim_order LH) cc_pmoc_ms cc_pmoc_inv.
    - intros. inv H.
      econstructor. eapply (ST.fsim_invariant_env_step LH); eauto.
      split; eauto. reflexivity.
    - apply (ST.fsim_skel LH).
    - econstructor. apply (ST.fsim_initial_world LH).
    - apply (ST.fsim_footprint LH).
    - intros. inv H. exploit (ST.fsim_lts LH); eauto. intros X.
      constructor.
      + intros.
        edestruct (@ST.fsim_match_initial_states)
          as (? & ? & ? & ? & ? & ? & ? & ?); eauto.
        instantiate (1 := (Some tt, _)). split; eauto.
        destruct y. constructor. destruct c. reflexivity. constructor.
        econstructor. split; eauto. reflexivity.
        cbn in *. prod_crush. eexists _, _. split; eauto.
        eexists _, _. repeat split; eauto.
        econstructor. eauto.
      + intros. inv H.
        edestruct (@ST.fsim_match_final_states)
          as (? & ? & ? & ? & ? & ?); eauto.
        destruct x2. destruct H4. destruct H4. destruct p; inv H4.
        destruct H3. eexists. split; eauto.
        eexists; repeat split; eauto. econstructor; eauto.
      + intros. inv H.
        edestruct (@ST.fsim_match_external)
          as (? & ? & ? & ? & ? & ?); eauto.
        destruct x2. destruct H3. destruct H4 as (? & ? & ?).
        destruct p; inv H4.
        eexists; split; eauto. eexists; repeat split; eauto.
        intros.
        edestruct H5 as (? & ? & ? & ? & ? & ? & ? & ?); eauto.
        instantiate (1 := (Some tt, _)). split; eauto. now constructor.
        eexists; split; eauto. reflexivity.
        eexists _, _. split; eauto.
        destruct x5, x6. destruct H11. destruct H12.
        eexists _, _. repeat split; eauto. econstructor; eauto.
      + intros. inv H1.
        edestruct (@ST.fsim_simulation) as (? & ? & ? & ? & ? & ? & ? & ?); eauto.
        destruct x3, x4. destruct H3. destruct H4.
        eexists _, _. split; eauto.
        eexists _, _. repeat split; eauto. econstructor. eauto.
    - apply (ST.fsim_order_wf LH).
  Qed.

End CC_COMP.

Lemma fsim_cc_comp_right_unit `(ccA: ST.callconv liA1 liA2)
      `(ccB: ST.callconv liB1 liB2) L1 L2:
  ST.forward_simulation (ST.cc_compose ccA &1) (ST.cc_compose ccB &1) L1 L2 ->
  ST.forward_simulation ccA ccB L1 L2.
Proof.
  intros [X]. constructor.
  eapply fsim_cc_comp_right_unit'. apply X.
Qed.

Lemma fsim_cc_comp_left_unit `(ccA: ST.callconv liA1 liA2)
      `(ccB: ST.callconv liB1 liB2) L1 L2:
  ST.forward_simulation (ST.cc_compose &1 ccA) (ST.cc_compose &1 ccB) L1 L2 ->
  ST.forward_simulation ccA ccB L1 L2.
Proof.
  intros [X]. constructor.
  eapply fsim_cc_comp_left_unit'. apply X.
Qed.

Require Import LogicalRelations.

Instance st_fsim_preo {li1 li2}:
  PreOrder (ST.forward_simulation &(@cc_id li1) &(@cc_id li2)).
Proof.
  split.
  - intros L. apply fsim_embed. reflexivity.
  - intros L1 L2 L3 H12 H23.
    exploit @st_fsim_vcomp. apply H12. apply H23.
    intros H. apply fsim_cc_comp_right_unit. apply H.
Qed.

Instance st_fsim_proper `(ccA: ST.callconv liA1 liA2) `(ccB: ST.callconv liB1 liB2):
  Proper ((ST.forward_simulation &1 &1) --> (ST.forward_simulation &1 &1) ++> impl)
         (ST.forward_simulation ccA ccB).
Proof.
  intros X Y HXY A B HAB HL.
  exploit @st_fsim_vcomp. exact HXY. exact HL. intros HL'.
  exploit @st_fsim_vcomp. exact HL'. exact HAB. intros HL''.
  apply (fsim_cc_comp_left_unit (fsim_cc_comp_right_unit HL'')).
Qed.

Global Instance ccref_preo li1 li2:
  PreOrder (@st_ccref li1 li2).
Proof.
  split.
  - intros cc. eapply st_ccref_intro with id id; try easy.
  - intros cc1 cc2 cc3 H12 H23.
    unfold st_ccref in *.
    exploit @st_fsim_lcomp_sk. apply H12. apply H23.
    1-2: apply Linking.linkorder_refl. cbn. intros X.
    match type of X with
    | ST.forward_simulation _ _ ?x ?y =>
        set (LX := x); set (LY := y)
    end.
    assert (Y: forward_simulation 1 1 (normalize_sem 1) LX).
    {
      subst LX.
      etransitivity. 2: apply assoc1.
      etransitivity. apply CAT.right_unit_1.
      etransitivity. apply CAT.right_unit_1.
      etransitivity. apply CAT.right_unit_1.
      eapply categorical_compose_simulation'. reflexivity.
      etransitivity. 2: apply assoc2.
      etransitivity. 2: apply assoc2.
      eapply categorical_compose_simulation'. 2: reflexivity.
      eapply categorical_compose_simulation'. 2: reflexivity.
      eapply categorical_compose_simulation'. 1-2: reflexivity.
      all: apply Linking.linkorder_refl.
    }
    assert (Z: forward_simulation 1 1 LY (normalize_sem 1)).
    {
      subst LY.
      etransitivity. 2: apply CAT.right_unit_2.
      etransitivity. 2: apply CAT.right_unit_2.
      etransitivity. 2: apply CAT.right_unit_2.
      etransitivity. apply assoc2.
      eapply categorical_compose_simulation'. reflexivity.
      etransitivity. apply assoc1.
      etransitivity. apply assoc1.
      eapply categorical_compose_simulation'. 2: reflexivity.
      eapply categorical_compose_simulation'. 2: reflexivity.
      eapply categorical_compose_simulation'. 1-2: reflexivity.
      all: apply Linking.linkorder_refl.
    }
    unfold STCAT.forward_simulation.
    rewrite -> (fsim_embed Y). rewrite <- (fsim_embed Z). apply X.
Qed.

Global Instance st_fsim_ccref:
  Monotonic
    (@STCAT.forward_simulation)
    (forallr - @ liA1, forallr - @ liA2, st_ccref ++>
     forallr - @ liB1, forallr - @ liB2, st_ccref -->
     subrel).
Proof.
  intros liA1 liA2 ccA1 ccA2 HA
         liB1 liB2 ccB1 ccB2 HB L1 L2 H.
  assert (Hsk: skel L1 = skel L2).
  { destruct H. apply X. }
  unfold flip, st_ccref in *.
  exploit @st_cat_fsim_lcomp_sk. exact H. exact HA.
  apply Linking.linkorder_refl. apply CategoricalComp.id_skel_order.
  intros HC.
  exploit @st_cat_fsim_lcomp_sk. exact HB. exact HC.
  apply CategoricalComp.id_skel_order. apply Linking.linkorder_refl.
  cbn. intros X. rewrite Hsk in X at 3 4. clear -X.
  assert (Y: STCAT.forward_simulation &1 &1 L1 (1 o L1 o 1)).
  {
    exploit @st_fsim_vcomp.
    apply st_fsim_right_unit1. apply st_fsim_left_unit1.
    apply fsim_cc_comp_left_unit.
  }
  assert (Z: STCAT.forward_simulation &1 &1 (1 o L2 o 1) L2).
  {
    exploit @st_fsim_vcomp.
    apply st_fsim_left_unit2. apply st_fsim_right_unit2.
    apply fsim_cc_comp_left_unit.
  }
  exploit @st_fsim_vcomp. exact Y. exact X. clear Y X. intros W.
  exploit @st_fsim_vcomp. exact W. exact Z. clear W Z. intros X.
  apply (fsim_cc_comp_left_unit (fsim_cc_comp_right_unit X)).
Qed.

(** * Encapsulation Properties *)

(** ** Composition of Components with Encapsulated States *)

Ltac eprod_crush :=
  repeat
    (match goal with
     | [ H: ?a * ?b |- _ ] => destruct H;cbn [fst snd] in *; subst
     | [ H: (?a, ?b) = (?c, ?d) |- _ ] => inv H
     | [ H: (?x * ?y)%rel _ _ |- _] => destruct H; cbn [fst snd] in *; subst
     | [ H: ?x /\ ?y |- _] => destruct H
     | [ H: (exists _, _) |- _] => destruct H
  end).

Section LI_FUNC.

  Program Definition callconv_map `(F1: LiFunc liA1 liX1) `(G1: LiFunc liB1 liY1) cc : ST.callconv liX1 liY1 :=
    {|
      ST.ccworld := ST.ccworld cc;
      ST.match_query w q1 q2 := ST.match_query cc w (query_func F1 q1) (query_func G1 q2);
      ST.match_reply w r1 r2 := ST.match_reply cc w (reply_func F1 r1) (reply_func G1 r2);
    |}.

  Context `(F1: LiFunc liA1 liX1) `(G1: LiFunc liB1 liY1) (cc1: ST.callconv liA1 liB1)
          `(F2: LiFunc liA2 liX2) `(G2: LiFunc liB2 liY2) (cc2: ST.callconv liA2 liB2)
          `(HG1: !LiSurjective G1) `(HG2: !LiSurjective G2).
  Lemma map_monotonicity_cc L1 L2:
    ST.forward_simulation cc1 cc2 L1 L2 ->
    ST.forward_simulation (callconv_map F1 G1 cc1) (callconv_map F2 G2 cc2)
                          (semantics_map L1 F1 F2) (semantics_map L2 G1 G2).
  Proof.
    intros [[]]. constructor. econstructor; eauto.
    instantiate (1 := fsim_match_states).
    intros. exploit fsim_lts; eauto. clear.
    intros HL. constructor.
    - intros. cbn in H1, H2.
      exploit @ST.fsim_match_initial_states; eauto.
    - intros. cbn in *.
      exploit @ST.fsim_match_final_states; eauto.
      intros X. eprod_crush.
      destruct ((proj2 HG2) x) as [? ?]. subst.
      eexists. repeat split; eauto.
    - intros. cbn in *.
      exploit @ST.fsim_match_external; eauto.
      intros. eprod_crush.
      destruct ((proj1 HG1) x) as [? ?]. subst.
      eexists. repeat split; eauto.
    - intros. exploit @ST.fsim_simulation; eauto.
  Qed.

End LI_FUNC.

Require Import FinFun.
Class LiInjective {liA liB} (F: li_func liA liB) :=
  LiInj: Injective (query_func F) /\ Injective (reply_func F).

(* TODO: move to somewhere else *)
Section MAP_NORMALIZE.

  Context `(F: LiFunc liA1 liA2) `(G: LiFunc liB1 liB2)
          (L : semantics liA1 liB1).

  Inductive mn_ms: state (normalize_sem (semantics_map L F G)) ->
                   state (semantics_map (normalize_sem L) F G) -> Prop :=
  | mn_ms1 q1 q2:
    query_func G q1 = q2 -> mn_ms (st1 1 _ (st_q q1)) (st1 1 _ (st_q q2))
  | mn_ms2 q1 q2 s:
    query_func G q1 = q2 ->
    mn_ms (st2 1 ((semantics_map L F G) o 1) (st_q q1) (st1 (semantics_map L F G) _ s))
          (st2 1 (L o 1) (st_q q2) (st1 L _ s))
  | mn_ms3 q1 q2 s q3 q4:
    query_func G q1 = q2 -> query_func F q3 = q4 ->
    mn_ms (st2 1 ((semantics_map L F G) o 1) (st_q q1) (st2 (semantics_map L F G) 1 s (st_q q3)))
          (st2 1 (L o 1) (st_q q2) (st2 L 1 s (st_q q4)))
  | mn_ms4 q1 q2 s r1 r2:
    query_func G q1 = q2 -> reply_func F r1 = r2 ->
    mn_ms (st2 1 ((semantics_map L F G) o 1) (st_q q1) (st2 (semantics_map L F G) 1 s (st_r r1)))
          (st2 1 (L o 1) (st_q q2) (st2 L 1 s (st_r r2)))
  | mn_ms5 r1 r2:
    reply_func G r1 = r2 -> mn_ms (st1 1 _ (st_r r1)) (st1 1 _ (st_r r2)).

  Lemma map_normalize1:
    forward_simulation 1 1 (normalize_sem (semantics_map L F G))
                       (semantics_map (normalize_sem L) F G).
  Proof.
    constructor. econstructor.
    reflexivity. firstorder.
    intros. inv H.
    eapply forward_simulation_step with (match_states := mn_ms).
    - intros q ? s1 [] H. inv H. inv H1.
      eexists. split; repeat constructor.
    - intros s1 s2 r1 Hs H. inv H. inv H1. inv Hs.
      eexists. split; repeat constructor.
    - intros s1 s2 q1 Hs H. exists tt. inv H. inv H1. inv H. inv Hs.
      eexists. repeat split.
      intros r ? s1' [] H. inv H. inv H5. inv H4.
      eexists. repeat split. constructor; reflexivity.
    - intros * HSTEP * HS. inv HS.
      + inv HSTEP. inv H1. inv H1. inv H2.
        eexists; split.
        eapply step_push; constructor; eauto. apply H.
        constructor; reflexivity.
      + inv HSTEP. inv H4.
        * eexists; split.
          apply step2. apply step1. apply H1.
          constructor; reflexivity.
        * inv H2. eexists; split.
          eapply step2. eapply step_push. apply H1. constructor.
          constructor; easy.
        * inv H2. inv H5. eexists; split.
          eapply step_pop; constructor. apply H1.
          constructor; easy.
      + inv HSTEP. inv H4. inv H5. inv H2. inv H2.
      + inv HSTEP. inv H4. inv H5. 2: inv H2. inv H2.
        eexists. split.
        apply step2. eapply step_pop. constructor. apply H6.
        constructor; easy.
      + inv HSTEP. inv H1. inv H1.
    - apply well_founded_ltof.
  Qed.

  Context {HG1: LiInjective G} {HF1: LiInjective F}
          {HG2: LiSurjective G} {HF2: LiSurjective F}.
  Lemma map_normalize2:
    forward_simulation 1 1 (semantics_map (normalize_sem L) F G)
                       (normalize_sem (semantics_map L F G)).
  Proof.
    constructor. econstructor.
    reflexivity. firstorder.
    intros. inv H.
    eapply forward_simulation_step with (match_states := flip mn_ms).
    - intros q ? s1 [] H. inv H. inv H1.
      eexists. split; repeat constructor.
    - intros s1 s2 r1 Hs H. inv H. inv H1. inv Hs.
      apply (proj2 HG1) in H2. subst.
      eexists. split; repeat constructor.
    - intros s1 s2 q1 Hs H. exists tt. inv H. inv H1. inv H. inv Hs.
      apply (proj1 HF1) in H5. subst.
      eexists. repeat split.
      intros r ? s1' [] H. inv H. inv H5. inv H4.
      eexists. repeat split. constructor; reflexivity.
    - intros * HSTEP * HS. inv HS.
      + inv HSTEP. inv H1. inv H1. inv H2.
        eexists; split.
        eapply step_push; constructor; eauto. apply H.
        constructor; reflexivity.
      + inv HSTEP. inv H4.
        * eexists; split.
          apply step2. apply step1. apply H1.
          constructor; reflexivity.
        * inv H2. destruct (proj1 HF2 q). subst.
          eexists; split.
          eapply step2. eapply step_push.
          apply H1. constructor.
          constructor; easy.
        * inv H2. inv H5. destruct (proj2 HG2 r). subst.
          eexists; split.
          eapply step_pop; constructor. apply H1.
          constructor; easy.
      + inv HSTEP. inv H4. inv H5. inv H2. inv H2.
      + inv HSTEP. inv H4. inv H5. 2: inv H2. inv H2.
        eexists. split.
        apply step2. eapply step_pop. constructor. apply H6.
        constructor; easy.
      + inv HSTEP. inv H1. inv H1.
    - apply well_founded_ltof.
  Qed.

  Lemma st_map_normalize2:
    ST.forward_simulation &1 &1 (semantics_map (normalize_sem L) F G)
                                (normalize_sem (semantics_map L F G)).
  Proof.
    apply fsim_embed. apply map_normalize2.
  Qed.

End MAP_NORMALIZE.

Lemma cc_map_id `(cc: ST.callconv liA liB):
  callconv_map id_li_func id_li_func cc = cc.
Proof.
  destruct cc. unfold callconv_map. cbn. reflexivity.
Qed.

Instance li_func_id_surj {li}: LiSurjective (@id_li_func li).
Proof. split; intros x; exists x; reflexivity. Qed.

Lemma cc_lift_twice {S1 S2 T1 T2} `(cc: ST.callconv liA liB):
  st_ccref (ST.callconv_lift cc (S1 * S2) (T1 * T2))
           (callconv_map lf lf (ST.callconv_lift (ST.callconv_lift cc S1 T1) S2 T2)).
Proof.
  match goal with
  | |- st_ccref ?x ?y => set (w1 := ST.ccworld x); set (w2 := ST.ccworld y)
  end.
  set (F := fun '(((a, b, c), d, e): w2) => (a, (b, d), (c, e))).
  set (G := fun '((a, (b, d), (c, e)): w1) => ((a, b, c), d, e)).
  eapply st_ccref_intro with F G.
  - reflexivity.
  - intros x y Hxy. cbn in *. prod_crush. cbn in *.
    prod_crush. repeat split; easy.
  - intros x y Hyx. cbn in *. prod_crush. cbn in *.
    repeat split; easy.
  - intros. cbn in *. prod_crush. reflexivity.
  - intros. cbn in *. prod_crush. cbn in *.
    prod_crush. repeat split; easy.
  - intros. cbn in *. prod_crush. cbn in *.
    prod_crush. subst. repeat split; easy.
Qed.

Section LIFT_UNIT.

  Context {li: language_interface} {S: Type}.
  Inductive su_ms: @state (li@S) _ 1 ->
                   @state (li@S) _ (1@S) -> Prop :=
  | su_ms_q q s:
    su_ms (@st_q (li@S) (q,s)) ((st_q q), s)
  | su_ms_r r s:
    su_ms (@st_r (li@S) (r,s)) ((st_r r), s).
  Hint Constructors su_ms.
  Lemma lift_unit1: forward_simulation (@cc_id (li@S)) 1 1 (1 @ S).
  Proof.
    constructor. econstructor.
    reflexivity. firstorder.
    intros. inv H.
    apply forward_simulation_step with (match_states := su_ms).
    - intros. inv H. inv H1. cbn in *. prod_crush.
      eexists (_, _). repeat split; eauto.
    - intros. inv H1. inv H.
      eexists (_, _). repeat split.
    - intros. inv H1. inv H.
      eexists tt, (_, _). repeat split.
      intros. inv H. inv H1. cbn in *. prod_crush.
      eexists (_, _). repeat split; eauto.
    - easy.
    - apply well_founded_ltof.
  Qed.

  Lemma lift_unit2: forward_simulation (@cc_id (li@S)) 1 (1 @ S) 1.
    constructor. econstructor.
    reflexivity. firstorder.
    intros. inv H.
    apply forward_simulation_step with (match_states := flip su_ms).
    - intros. inv H. inv H1. inv H. cbn in *. prod_crush.
      eexists. repeat split; eauto. constructor.
    - intros. inv H1. inv H. inv H2. inv H2. cbn in *. prod_crush.
      eexists. repeat split.
    - intros. inv H1. inv H. inv H2. cbn in *.  prod_crush.
      eexists tt, _. repeat split.
      intros. inv H. inv H1. inv H. cbn in *. prod_crush.
      eexists. repeat split; eauto. constructor. inv H2.
    - intros. cbn in *. prod_crush. inv H.
    - apply well_founded_ltof.
  Qed.

End LIFT_UNIT.

Lemma fsim_lift_normalize1 {S} `(L: semantics liA liB):
  forward_simulation 1 1 (normalize_sem (L @ S)) (normalize_sem L @ S).
Proof.
  setoid_rewrite <- lift_categorical_comp2.
  eapply categorical_compose_simulation'.
  apply lift_unit1.
  setoid_rewrite <- lift_categorical_comp2.
  eapply categorical_compose_simulation'.
  reflexivity.
  apply lift_unit1.
  all: cbn; (apply Linking.linkorder_refl || apply CategoricalComp.id_skel_order).
Qed.

Lemma fsim_lift_normalize2 {S} `(L: semantics liA liB):
  forward_simulation 1 1 (normalize_sem L @ S) (normalize_sem (L @ S)).
Proof.
  setoid_rewrite lift_categorical_comp1.
  eapply categorical_compose_simulation'.
  apply lift_unit2.
  setoid_rewrite -> lift_categorical_comp1.
  eapply categorical_compose_simulation'.
  reflexivity.
  apply lift_unit2.
  all: cbn; (apply Linking.linkorder_refl || apply CategoricalComp.id_skel_order).
Qed.

Instance li_inj_k {li K1 K2}:
  LiInjective (@li_func_k li K1 K2).
Proof. split; intros x y Hxy; cbn in *; prod_crush; easy. Qed.

Instance li_inj_id {li}:
  LiInjective (@id_li_func li).
Proof. split; intros x y Hxy; cbn in *; prod_crush; easy. Qed.

Section COMP.
  Context `(ccA: ST.callconv liA1 liA2)
          `(ccB: ST.callconv liB1 liB2)
          `(ccC: ST.callconv liC1 liC2)
          (L1s: liB1 +-> liC1) (L2s: liA1 +-> liB1)
          (L1t: liB2 +-> liC2) (L2t: liA2 +-> liB2).
  Context (HL1: E.forward_simulation ccB ccC L1s L1t)
          (HL2: E.forward_simulation ccA ccB L2s L2t)
          sk (Hsk1: Linking.linkorder (skel L1s) sk)
          (Hsk2: Linking.linkorder (skel L2s) sk).

  (** Lemma 3.14 *)
  Lemma encap_fsim_lcomp_sk:
    E.forward_simulation ccA ccC (comp_esem' L1s L2s sk) (comp_esem' L1t L2t sk).
  Proof.
    unfold E.forward_simulation in *. unfold comp_esem in *.
    apply st_fsim_lift with (K1:=pstate L2s) (K2:=pstate L2t) in HL1.
    exploit @st_fsim_lcomp_sk. exact HL1. exact HL2. 1-2: eauto.
    intros X. cbn. rewrite cc_lift_twice.
    unfold STCAT.forward_simulation.
    rewrite (fsim_embed (map_normalize1 _ _ _)).
    rewrite <- st_map_normalize2. 2-5: typeclasses eauto.
    rewrite <- (cc_map_id ccA).
    eapply map_monotonicity_cc.
    1-2: typeclasses eauto.
    rewrite (fsim_embed (normalize_comp_fsim_sk1 _ _ sk)).
    rewrite <- (fsim_embed (normalize_comp_fsim_sk2 _ _ sk)).
    assert (H1: ST.forward_simulation
                &1 &1 (comp_semantics' (normalize_sem (L1s @ pstate L2s)) (normalize_sem L2s) sk)
                      (comp_semantics' (normalize_sem L1s @ pstate L2s) (normalize_sem L2s) sk)).
    {
      eapply st_fsim_lcomp_sk.
      apply fsim_embed. apply fsim_lift_normalize1.
      reflexivity. all: easy.
    }
    rewrite H1. clear H1.
    assert (H2: ST.forward_simulation
                &1 &1 (comp_semantics' (normalize_sem L1t @ pstate L2t) (normalize_sem L2t) sk)
                      (comp_semantics' (normalize_sem (L1t @ pstate L2t)) (normalize_sem L2t) sk)).
    {
      assert (skel L2t = skel L2s). destruct HL2. destruct X0. easy.
      assert (skel L1t = skel L1s). destruct HL1. destruct X0. easy.
      eapply st_fsim_lcomp_sk.
      apply fsim_embed. apply fsim_lift_normalize2.
      reflexivity.
      cbn. rewrite H0. easy.
      cbn. rewrite H. easy.
    }
    rewrite <- H2. apply X.
  Qed.

End COMP.

(** A simplified condition for ccB ⊑ ccA, where the wB is a substructure of
    wA. Additional invariant is required on wA to constrain the redundant
    information *)
Section CCREF.

  Context {li1 li2} (ccA ccB: ST.callconv li1 li2).

  Variable F: ST.ccworld ccA -> ST.ccworld ccB.
  Variable I: ST.ccworld ccA -> Prop.
  Hypothesis F_init: F (pset_init (ST.ccworld ccA)) = pset_init (ST.ccworld ccB).
  Hypothesis I_init: I (pset_init (ST.ccworld ccA)).
  Hypothesis I_ext_step: forall wa wa1, I wa -> wa :-> wa1 -> I wa1.
  Hypothesis F_int_step: forall wa1 wa2, wa1 *-> wa2 -> F wa1 *-> F wa2.
  Hypothesis F_ext_step:
    forall wa wb1, F wa :-> wb1 -> exists wa1, wa :-> wa1 /\ F wa1 = wb1.
  Hypothesis F_mq:
    forall wa q1 q2, I wa -> ST.match_query ccB (F wa) q1 q2 -> ST.match_query ccA wa q1 q2.
  Hypothesis F_mr:
    forall wa r1 r2, ST.match_reply ccA wa r1 r2 -> ST.match_reply ccB (F wa) r1 r2 /\ I wa.

  Inductive sub_inv: ST.ccworld ccA -> ST.ccworld ccB -> Prop :=
  | sub_inv_intro wa wb: I wa -> F wa :-> wb -> sub_inv wa wb.
  Inductive sub_ms: ST.ccworld ccA -> ST.ccworld ccB -> @state li1 li1 1 -> @state li2 li2 1 -> Prop :=
  | sub_ms_q q1 q2 wa wb:
    I wa -> F wa = wb -> ST.match_query ccB wb q1 q2 ->
    sub_ms wa wb (st_q q1) (st_q q2)
  | sub_ms_r r1 r2 wa wb:
    I wa -> F wa = wb -> ST.match_reply ccB wb r1 r2 ->
    sub_ms wa wb (st_r r1) (st_r r2).

  Lemma st_ccref_sub: st_ccref ccB ccA.
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun _ wa wb _ => sub_ms wa wb)
      (fun wa wb => sub_inv wa wb); try easy.
    - intros. inv H. constructor; eauto. etransitivity; eauto.
    - constructor; eauto. rewrite F_init. reflexivity.
    - intros wa wb se HI. inv HI.
      constructor.
      + intros q1 q2 s1 wb1 Hb Hq Hx. exists tt. inv Hx. exists (st_q q2).
        split. constructor.
        edestruct F_ext_step as (wa1 & Ha1 & Ha2).
        etransitivity; eauto. subst.
        exists wa1, (F wa1). repeat split; try easy.
        constructor; eauto.
      + intros wa1 wb1 [] s1 s2 r1 Hs Hx. inv Hx.
        inv Hs. exists r2. split. constructor.
        exists (F wa1). repeat split; easy.
      + intros wa1 wb1 [] s1 s2 q1 Hs Hx. inv Hx. inv Hs.
        exists q2. split. constructor.
        exists wa1. split. reflexivity. split. apply F_mq; auto.
        intros r1 r2 s1' wa2 Ha2 Hr Hy.
        inv Hy. eexists tt, _. split. constructor.
        eexists wa2, (F wa2). repeat split; eauto. easy.
        constructor; eapply F_mr in Hr; easy.
      + intros. easy.
  Qed.

End CCREF.

Lemma lift_comp_ccref {S1 S2 S3} `(cc1: ST.callconv liA liB) `(cc2: ST.callconv liB liC):
  st_ccref (ST.callconv_lift (ST.cc_compose cc1 cc2) S1 S3)
           (ST.cc_compose (ST.callconv_lift cc1 S1 S2) (ST.callconv_lift cc2 S2 S3)).
Proof.
  match goal with
  | |- st_ccref ?x ?y => set (w1 := ST.ccworld x); set (w2 := ST.ccworld y)
  end.
  cbn in *.
  set (F := fun '((w1, s1, _, (w2, _, s3)):w2) => (w1, w2, s1, s3)).
  set (I := fun '((_, _, s2, (_, s2', _)):w2) => s2 = s2').
  eapply st_ccref_sub with F I; intros; cbn in *; prod_crush; subst; try easy.
  - cbn in *. prod_crush. subst. eexists (_, _, _, (_, _, _)). cbn.
    repeat split; eauto.
  - cbn in *. eprod_crush. subst.
    eexists (_, _). repeat split; eauto.
  - cbn in *. eprod_crush. subst.
    repeat split; eauto.
Qed.

Section ENCAP_COMP_FSIM.

  Context `(ccA1: ST.callconv liAs liAn) `(ccA2: ST.callconv liAn liAf)
          `(ccB1: ST.callconv liBs liBn) `(ccB2: ST.callconv liBn liBf)
          (Ls: liAs +-> liBs) (Ln: liAn +-> liBn) (Lf: liAf +-> liBf).
  Context (H1: E.forward_simulation ccA1 ccB1 Ls Ln)
          (H2: E.forward_simulation ccA2 ccB2 Ln Lf).

  (** Lemma 3.11 *)
  Lemma encap_fsim_vcomp:
    E.forward_simulation (ST.cc_compose ccA1 ccA2)
                         (ST.cc_compose ccB1 ccB2) Ls Lf.
  Proof.
    unfold E.forward_simulation in *.
    exploit @st_fsim_vcomp. exact H1. exact H2. clear.
    intros X.
    rewrite @lift_comp_ccref. apply X.
  Qed.
End ENCAP_COMP_FSIM.

Lemma cc_lift_unit `(cc: ST.callconv liA liB):
  st_ccref (ST.callconv_lift cc pset_unit pset_unit)
           (callconv_map lf lf cc).
Proof.
  match goal with
  | |- st_ccref ?x ?y => set (w1 := ST.ccworld x); set (w2 := ST.ccworld y)
  end.
  cbn in *.
  set (F := fun '((w, _, _):w1) => w).
  set (G := fun (w:w2) => (w, tt, tt)).
  eapply st_ccref_intro with G F;
    intros; cbn in *; prod_crush; cbn; try easy.
  - destruct u0, u. reflexivity.
  - destruct u0, u. repeat split; easy.
Qed.

(** Lemma 3.15 *)
Instance li_unit_inj {li}:
  LiInjective (@li_func_unit li).
Proof. split; intros x y Hxy; cbn in *; prod_crush; destruct u, u0; easy. Qed.

Instance li_unit_surj {li}:
  LiSurjective (@li_func_unit li).
Proof. split; intros x; exists (x, tt); reflexivity. Qed.

Lemma fsim_normalize `(ccA: callconv liA1 liA2) `(ccB: callconv liB1 liB2) L1 L2:
  forward_simulation ccA ccB L1 L2 ->
  CAT.forward_simulation ccA ccB L1 L2.
Proof.
  intros HL. assert (Hsk: skel L1 = skel L2).
  destruct HL. apply (fsim_skel X).
  unfold CAT.forward_simulation, normalize_sem, left_comp_id, right_comp_id.
  rewrite Hsk.
  eapply categorical_compose_simulation'.
  apply ccref_to_fsim. reflexivity.
  eapply categorical_compose_simulation'.
  apply HL. apply ccref_to_fsim. reflexivity.
  rewrite Hsk.  all: cbn; (apply Linking.linkorder_refl || apply CategoricalComp.id_skel_order).
Qed.

Lemma encap_fsim_embed `(ccA: callconv liA1 liA2) `(ccB: callconv liB1 liB2) L1 L2:
  forward_simulation ccA ccB L1 L2 ->
  E.forward_simulation &ccA &ccB
                       (semantics_embed L1) (semantics_embed L2).
Proof.
  intros. unfold E.forward_simulation, semantics_embed. cbn.
  rewrite cc_lift_unit. rewrite <- (cc_map_id &ccA).
  unfold STCAT.forward_simulation.
  rewrite (fsim_embed (map_normalize1 _ _ _)).
  rewrite <- st_map_normalize2. 2-5: typeclasses eauto.
  apply map_monotonicity_cc.
  1-2: typeclasses eauto.
  apply fsim_embed. apply fsim_normalize. apply H.
Qed.

(** ** Simulation Convention FBK *)
Definition callconv_fbk {K1 K2: PSet}
        `(cc: ST.callconv (li1@K1) (li2@K2)): ST.callconv li1 li2 :=
  {|
    ST.ccworld := (ST.ccworld cc * pset_world K1 * pset_world K2)%world;
    ST.match_query '(w, k1, k2) q1 q2 := ST.match_query cc w (q1, k1) (q2, k2);
    ST.match_reply '(w, k1, k2) r1 r2 := ST.match_reply cc w (r1, k1) (r2, k2);
  |}.

Lemma ccref_lift {K1 K2} {li1 li2} (ccA ccB: ST.callconv li1 li2):
  st_ccref ccA ccB -> st_ccref (ST.callconv_lift ccA K1 K2) (ST.callconv_lift ccB K1 K2).
Proof.
  unfold st_ccref. intros H. unfold STCAT.forward_simulation.
  assert (X: forward_simulation 1 1 (@normalize_sem (li1@K1) _ 1) (normalize_sem 1 @ K1)).
  {
    etransitivity. 2: apply lift_categorical_comp2.
    eapply categorical_compose_simulation'. apply lift_unit1.
    etransitivity. 2: apply lift_categorical_comp2.
    eapply categorical_compose_simulation'. 1-2: apply lift_unit1.
    all: apply Linking.linkorder_refl.
  }
  assert (Y: forward_simulation 1 1 (@normalize_sem li2 _ 1 @ K2) (normalize_sem 1)).
  {
    etransitivity. apply lift_categorical_comp1.
    eapply categorical_compose_simulation'. apply lift_unit2.
    etransitivity. apply lift_categorical_comp1.
    eapply categorical_compose_simulation'. 1-2: apply lift_unit2.
    all: apply Linking.linkorder_refl.
  }
  rewrite (fsim_embed X). rewrite <- (fsim_embed Y).
  apply st_fsim_lift. apply H.
Qed.

(** ** FBK vs LIFT *)

(** A simplified condition for ccB ⊑ ccA, where wA is a substructure of wB *)
Section CCREF.

  Context {li1 li2} (ccA ccB: ST.callconv li1 li2).

  Variable F: ST.ccworld ccB -> ST.ccworld ccA.
  Variable I: ST.ccworld ccB -> Prop.
  Hypothesis F_init: F (pset_init (ST.ccworld ccB)) = pset_init (ST.ccworld ccA).
  Hypothesis F_ext_step: forall x y, x :-> y -> F x :-> F y.
  Hypothesis F_int_step:
    forall wb1 wa2, F wb1 *-> wa2 -> exists wb2, wa2 = F wb2 /\ wb1 *-> wb2 /\ (I wb1 -> I wb2).
  Hypothesis F_mq:
    forall wb q1 q2, ST.match_query ccB wb q1 q2 -> ST.match_query ccA (F wb) q1 q2 /\ I wb.
  Hypothesis F_mr:
    forall wb r1 r2, I wb -> ST.match_reply ccA (F wb) r1 r2 -> ST.match_reply ccB wb r1 r2.

  Inductive super_inv: ST.ccworld ccA -> ST.ccworld ccB -> Prop :=
  | super_inv_intro wa wb: wa :-> F wb -> super_inv wa wb.
  Inductive super_ms: ST.ccworld ccA -> ST.ccworld ccB -> @state li1 li1 1 -> @state li2 li2 1 -> Prop :=
  | super_ms_q q1 q2 wa wb:
    I wb -> wa = F wb -> ST.match_query ccB wb q1 q2 ->
    super_ms wa wb (st_q q1) (st_q q2)
  | super_ms_r r1 r2 wa wb:
    I wb -> wa = F wb -> ST.match_reply ccB wb r1 r2 ->
    super_ms wa wb (st_r r1) (st_r r2).

  Lemma st_ccref_super: st_ccref ccB ccA.
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun _ wa wb _ => super_ms wa wb)
      (fun wa wb => super_inv wa wb); try easy.
    - intros. inv H. constructor. etransitivity; eauto.
    - constructor. rewrite F_init. reflexivity.
    - intros wa wb se Hi. inv Hi.
      constructor.
      + intros q1 q2 s1 wb1 Hb Hq Hx. exists tt. inv Hx. exists (st_q q2).
        split. constructor.
        exists (F wb1), wb1. repeat split; try easy.
        * etransitivity; eauto.
        * constructor; eauto. apply F_mq in Hq. apply Hq.
      + intros wa1 wb1 [] s1 s2 r1 Hs Hx. inv Hx.
        inv Hs. exists r2. split. constructor.
        exists wb1. repeat split; easy.
      + intros wa1 wb1 [] s1 s2 q1 Hs Hx. inv Hx. inv Hs.
        exists q2. split. constructor.
        exists (F wb1). split. reflexivity. split. apply F_mq; auto.
        intros r1 r2 s1' wa2 Ha2 Hr Hy.
        inv Hy. eexists tt, _. split. constructor.
        destruct (F_int_step _ _ Ha2) as (wb2 & Hb1 & Hb2 & Hb3).
        eexists wa2, wb2. repeat split; try easy.
        constructor; eauto.
        apply F_mr; subst; eauto.
      + intros. easy.
  Qed.

End CCREF.

Lemma cc_fbk_lift1 {K1 K2: PSet} `(cc: ST.callconv li1 li2):
  st_ccref (callconv_fbk (ST.callconv_lift cc K1 K2)) cc.
Proof.
  match goal with
  | |- st_ccref ?x ?y => set (w1 := ST.ccworld x); set (w2 := ST.ccworld y)
  end.
  cbn in *.
  set (F := fun '((w, _, _, _, _):w1) => w).
  set (I := fun '((_, k1, k2, k1', k2'):w1) => k1 = k1' /\ k2 = k2').
  eapply st_ccref_super with F I;
    intros; cbn in *; prod_crush; subst; try easy.
  eexists (_, _, _, _, _). repeat split. eauto.
  Unshelve. all: eauto.
Qed.

Lemma cc_fbk_lift2 {K1 K2: PSet} `(cc: ST.callconv li1 li2):
  st_ccref cc (callconv_fbk (ST.callconv_lift cc K1 K2)).
Proof.
  match goal with
  | |- st_ccref ?x ?y => set (w1 := ST.ccworld x); set (w2 := ST.ccworld y)
  end.
  cbn in *.
  set (F := fun '((w, _, _, _, _):w2) => w).
  set (I := fun '((_, k1, k2, k1', k2'):w2) => k1 = k1' /\ k2 = k2').
  eapply st_ccref_sub with F I;
    intros; cbn in *; prod_crush; subst; try easy.
  eexists (_, _, _, _, _). repeat split. easy.
Qed.

(** A simplified condition for ccB ⊑ ccA, where wA is a substructure of wB *)
Section CCREF.

  Context {li1 li2} (ccA ccB: ST.callconv li1 li2).

  Variable F: ST.ccworld ccB -> ST.ccworld ccA.
  Variable I: ST.ccworld ccB -> Prop.
  Hypothesis F_init: pset_init (ST.ccworld ccA) :-> F (pset_init (ST.ccworld ccB)).
  (* F (pset_init (ST.ccworld ccB)) = pset_init (ST.ccworld ccA). *)
  Hypothesis I_init: I (pset_init (ST.ccworld ccB)).
  Hypothesis I_ext_step: forall wb wb1, I wb -> wb :-> wb1 -> I wb1.
  Hypothesis F_ext_step: forall x y, x :-> y -> F x :-> F y.
  Hypothesis F_int_step:
    forall wb1 wa2, F wb1 *-> wa2 ->
               forall r1 r2, exists wb2, wa2 = F wb2 /\ wb1 *-> wb2
                               /\ (I wb1 -> I wb2)
                               /\ (ST.match_reply ccA wa2 r1 r2 ->
                                  ST.match_reply ccB wb2 r1 r2).
  Hypothesis F_mq:
    forall wb q1 q2, I wb -> ST.match_query ccB wb q1 q2 -> ST.match_query ccA (F wb) q1 q2.

  Inductive fbk1_inv: ST.ccworld ccA -> ST.ccworld ccB -> Prop :=
  | fbk1_inv_intro wa wb: I wb -> wa :-> F wb -> fbk1_inv wa wb.
  Inductive fbk1_ms: ST.ccworld ccA -> ST.ccworld ccB -> @state li1 li1 1 -> @state li2 li2 1 -> Prop :=
  | fbk1_ms_q q1 q2 wa wb:
    I wb -> wa = F wb -> ST.match_query ccB wb q1 q2 ->
    fbk1_ms wa wb (st_q q1) (st_q q2)
  | fbk1_ms_r r1 r2 wa wb:
    I wb -> wa = F wb -> ST.match_reply ccB wb r1 r2 ->
    fbk1_ms wa wb (st_r r1) (st_r r2).

  Lemma st_ccref_fbk1: st_ccref ccB ccA.
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun _ wa wb _ => fbk1_ms wa wb)
      (fun wa wb => fbk1_inv wa wb); try easy.
    - intros. inv H. constructor; eauto. etransitivity; eauto.
    - intros wa wb se Hi. inv Hi.
      constructor.
      + intros q1 q2 s1 wb1 Hb Hq Hx. exists tt. inv Hx. exists (st_q q2).
        split. constructor.
        exists (F wb1), wb1. repeat split; try easy.
        * etransitivity; eauto.
        * constructor; eauto.
      + intros wa1 wb1 [] s1 s2 r1 Hs Hx. inv Hx.
        inv Hs. exists r2. split. constructor.
        exists wb1. repeat split; easy.
      + intros wa1 wb1 [] s1 s2 q1 Hs Hx. inv Hx. inv Hs.
        exists q2. split. constructor.
        exists (F wb1). split. reflexivity. split. apply F_mq; auto.
        intros r1 r2 s1' wa2 Ha2 Hr Hy.
        inv Hy. eexists tt, _. split. constructor.
        destruct (F_int_step _ _ Ha2 r1 r2) as (wb2 & Hb1 & Hb2 & Hb3 & HR).
        eexists wa2, wb2. repeat split; try easy.
        constructor; eauto.
      + intros. easy.
  Qed.

End CCREF.

Lemma cc_lift_fbk1 {K1 K2: PSet} `(cc: ST.callconv (li1@K1) (li2@K2)):
  st_ccref (ST.callconv_lift (callconv_fbk cc) K1 K2) cc.
Proof.
  match goal with
  | |- st_ccref ?x ?y => set (w1 := ST.ccworld x); set (w2 := ST.ccworld y)
  end.
  cbn in *.
  set (F := fun '((w, _, _, _, _):w1) => w).
  set (I := fun '((_, k1, k2, k1', k2'):w1) => k1 = k1' /\ k2 = k2').
  eapply st_ccref_fbk1 with F I;
    intros; cbn in *; prod_crush; subst; try easy.
  eexists (_, _, _, _, _). repeat split. eauto.
  intros; cbn in *. prod_crush. repeat split; eauto.
  cbn in *. prod_crush. subst; eauto.
Qed.

Lemma cc_lift_fbk2 {K1 K2: PSet} `(cc: ST.callconv (li1@K1) (li2@K2)):
  st_ccref cc (ST.callconv_lift (callconv_fbk cc) K1 K2).
Proof.
  match goal with
  | |- st_ccref ?x ?y => set (w1 := ST.ccworld x); set (w2 := ST.ccworld y)
  end.
  cbn in *.
  set (F := fun '((w, _, _, _, _):w2) => w).
  set (I := fun '((_, k1, k2, k1', k2'):w2) => k1 = k1' /\ k2 = k2').
  eapply st_ccref_sub with F I;
    intros; cbn in *; prod_crush; subst; try easy.
  eexists (_, _, _, _, _). repeat split. easy.
  cbn in *. admit.
  cbn in *.
Abort.

(** Lemma 3.17 *)
Lemma encap_fsim_fbk {K1 K2: PSet}
      `(ccA: ST.callconv liA1 liA2) `(ccB: ST.callconv (liB1@K1) (liB2@K2)) L1 L2:
  E.forward_simulation ccA ccB L1 L2 ->
  E.forward_simulation ccA (callconv_fbk ccB) (semantics_fbk L1) (semantics_fbk L2).
Proof.
  unfold E.forward_simulation. cbn. intros HL.
  rewrite cc_lift_twice.
  unfold STCAT.forward_simulation.
  rewrite (fsim_embed (map_normalize1 _ _ _)).
  rewrite <- st_map_normalize2. 2-5: typeclasses eauto.
  rewrite <- (cc_map_id ccA).
  eapply map_monotonicity_cc.
  1-2: typeclasses eauto.
  pose proof (@ccref_lift (pstate L1) (pstate L2)  _ _ _ _ (cc_lift_fbk1 ccB)) as Hcc.
  assert (X: STCAT.forward_simulation ccA (ST.callconv_lift (ST.callconv_lift (callconv_fbk ccB) K1 K2) (pstate L1) (pstate L2)) L1 L2).
  {
    rewrite Hcc. apply HL.
  }
  apply X.
Qed.

(** ** REVEAL Simulation Convention *)

Program Definition cc_reveal {K: PSet} {li} : ST.callconv li (li@K) :=
  {|
    ST.ccworld := pset_world K;
    ST.match_query k q1 '(q2, kq) := q1 = q2 /\ k = kq;
    ST.match_reply k r1 '(r2, kr) := r1 = r2 /\ k = kr;
  |}.

Lemma cc_lift_reveal {li} {K1 K2: PSet}:
  st_ccref
    (ST.callconv_lift (cc_reveal (li:=li)) (K2 * K1) K1) (callconv_map li_func_k lf &1).
Proof.
  match goal with
  | |- st_ccref ?x ?y => set (w1 := ST.ccworld x); set (w2 := ST.ccworld y)
  end.
  cbn in *.
  set (F := fun _:w1 => Some tt).
  set (I := fun '((k2, (kk2, k1), kk1):w1) => k1 = kk1 /\ k2 = kk2).
  eapply st_ccref_fbk1 with F I.
  all: intros; cbn in *; prod_crush; subst; try easy.
  - constructor.
  - inv H. destruct y.
    eexists (_, (_, _), _). cbn in *. repeat split; inv H; easy.
  - inv H. reflexivity.
Qed.

Section REVEAL.

  Lemma sem_map_id `(L: semantics liA liB):
    L = semantics_map L lf lf.
  Proof.
    unfold semantics_map. destruct L. cbn. f_equal.
    apply Axioms.functional_extensionality. intros se.
    unfold lts_map. destruct (activate se).
    cbn. f_equal.
  Qed.

  (** Lemma 3.18 *)
  Lemma fsim_reveal {K: PSet} {liA liB} (L: liA +-> liB@K):
    E.forward_simulation &1 cc_reveal (semantics_fbk L) L.
  Proof.
    unfold E.forward_simulation. cbn. rewrite cc_lift_reveal.
    unfold STCAT.forward_simulation.
    rewrite (fsim_embed (map_normalize1 _ _ _)).
    rewrite <- (cc_map_id &1).
    rewrite (sem_map_id (normalize_sem L)) at 2.
    eapply map_monotonicity_cc.
    1-2: typeclasses eauto.
    reflexivity.
  Qed.

End REVEAL.

(** ** Basics *)

(** Lemma 3.4 *)
Definition encap_equiv_simulation {liA liB} (L1 L2: liA +-> liB) :=
  E.forward_simulation &1 &1 L1 L2 /\ E.forward_simulation &1 &1 L2 L1.

Lemma comp_embed `(L1: semantics liB liC) `(L2: semantics liA liB) L eL:
  comp_esem (semantics_embed L1) (semantics_embed L2) = Some eL ->
  comp_semantics L1 L2 = Some L ->
  encap_equiv_simulation (semantics_embed L) eL.
Admitted.

Definition esem_lift {K: PSet} `(L: liA +-> liB) : liA@K +-> liB@K.
Admitted.

Definition esem_assoc `(L: liA +-> (liB @ K1) @ K2) : liA +-> (liB @ (K1 * K2)).
Admitted.

Lemma comp_fbk {K1 K2: PSet} `(L1: liB +-> liC@K1) `(L2: liA +-> liB@K2) La Lb:
  comp_esem (semantics_fbk L1) (semantics_fbk L2) = Some La ->
  comp_esem (esem_lift L1) L2 = Some Lb ->
  encap_equiv_simulation La (semantics_fbk (K:=K1*K2) (esem_assoc Lb)).
Admitted.

(** A simplified condition for sim. conv. refinement given the world of ccA is a
    substructure of ccB *)
Section CCREF.

  Context {li1 li2} (ccA ccB: ST.callconv li1 li2).

  Variable F: ST.ccworld ccB -> ST.ccworld ccA.
  Hypothesis F_init: F (pset_init (ST.ccworld ccB)) = pset_init (ST.ccworld ccA).
  Hypothesis F_ext_step: forall x y, x :-> y -> F x :-> F y.
  (* Hypothesis F_int_step: forall x y, x *-> y -> F x *-> F y. *)
  Hypothesis F_mq:
    forall wb q1 q2, ST.match_query ccB wb q1 q2 -> ST.match_query ccA (F wb) q1 q2.
  Hypothesis F_int_step:
    forall wb1 wa2, F wb1 *-> wa2 -> exists wb2, wa2 = F wb2 /\ wb1 *-> wb2.
  Hypothesis F_mr:
    forall wb r1 r2, ST.match_reply ccA (F wb) r1 r2 -> ST.match_reply ccB wb r1 r2.

  Inductive sub_inv: ST.ccworld ccA -> ST.ccworld ccB -> Prop :=
  | sub_inv_intro wa wb: wa :-> F wb -> sub_inv wa wb.
  Inductive sub_ms: ST.ccworld ccA -> ST.ccworld ccB -> @state li1 li1 1 -> @state li2 li2 1 -> Prop :=
  | sub_ms_q q1 q2 wa wb:
    wa = F wb -> ST.match_query ccB wb q1 q2 ->
    sub_ms wa wb (st_q q1) (st_q q2)
  | sub_ms_r r1 r2 wa wb:
    wa = F wb -> ST.match_reply ccB wb r1 r2 ->
    sub_ms wa wb (st_r r1) (st_r r2).

  Lemma st_ccref_sub: st_ccref ccB ccA.
  Proof.
    apply st_normalize_fsim. constructor.
    eapply ST.Forward_simulation with
      (ltof _ (fun (_: unit) => 0)) (fun _ wa wb _ => sub_ms wa wb)
      (fun wa wb => sub_inv wa wb); try easy.
    - intros. inv H. constructor. etransitivity; eauto.
    - constructor. rewrite F_init. reflexivity.
    - intros wa wb se I. inv I.
      constructor.
      + intros q1 q2 s1 wb1 Hb Hq Hx. exists tt. inv Hx. exists (st_q q2).
        split. constructor.
        exists (F wb1), wb1. repeat split; try easy.
        * etransitivity; eauto.
        * constructor; eauto.
      + intros wa1 wb1 [] s1 s2 r1 Hs Hx. inv Hx.
        inv Hs. exists r2. split. constructor.
        exists wb1. repeat split; easy.
      + intros wa1 wb1 [] s1 s2 q1 Hs Hx. inv Hx. inv Hs.
        exists q2. split. constructor.
        exists (F wb1). split. reflexivity. split. apply F_mq; auto.
        intros r1 r2 s1' wa2 Ha2 Hr Hy.
        inv Hy. eexists tt, _. split. constructor.
        destruct (F_int_step _ _ Ha2) as (wb2 & Hb1 & Hb2).
        eexists wa2, wb2. repeat split; try easy.
        constructor; eauto. apply F_mr; subst; eauto.
      + intros. easy.
  Qed.

End CCREF.
