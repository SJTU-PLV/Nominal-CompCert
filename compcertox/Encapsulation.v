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

Variable id_skel: AST.program unit unit.
Hypothesis id_skel_order: forall sk, Linking.linkorder id_skel sk.

Section ID_SEM.

  Context {liA liB} (L: semantics liA liB).

  (*
  Definition id_skel: AST.program unit unit :=
    {|
      prog_defs := nil;
      prog_public := nil;
      prog_main := prog_main (skel L);
    |}.
  Lemma id_skel_order: Linking.linkorder id_skel (skel L).
  Proof.
    constructor. reflexivity.
    repeat split. easy.
    intros. inv H.
  Qed.
  *)

  Definition left_comp_id :=
    comp_semantics' (id_semantics id_skel) L (skel L).
  Definition right_comp_id :=
    comp_semantics' L (id_semantics id_skel) (skel L).

End ID_SEM.

Notation "L 'o' 1" := (right_comp_id L) (at level 15).
Notation "1 'o' L" := (left_comp_id L) (at level 20).
(* Notation "1 [ L ]" := (id_semantics (id_skel L)). *)
Notation "1" := (id_semantics id_skel) : lts_scope.
Definition normalize_sem {liA liB} (L: semantics liA liB) := 1 o L o 1.

(* TODO: maybe we need to use CAT.fsim to define E.fsim *)

Ltac inv_comp :=
  match goal with
  | [ H : at_external ((_ (comp_semantics' _ _ _)) _) _ _ |- _ ] => inv H
  | [ H : after_external ((_ (comp_semantics' _ _ _)) _) _ _ _ |- _ ] => inv H
  | [ H : initial_state ((_ (comp_semantics' _ _ _)) _) _ _ |- _ ] => inv H
  | [ H : final_state ((_ (comp_semantics' _ _ _)) _) _ _ |- _ ] => inv H
  | [ H : step ((_ (comp_semantics' _ _ _)) _) _ _ _ _ |- _ ] => inv H
  end.
Ltac inv_id :=
  match goal with
  | [ H : at_external ((_ (id_semantics _)) _) _ _ |- _ ] => inv H
  | [ H : after_external ((_ (id_semantics _)) _) _ _ _ |- _ ] => inv H
  | [ H : initial_state ((_ (id_semantics _)) _) _ _ |- _ ] => inv H
  | [ H : final_state ((_ (id_semantics _)) _) _ _ |- _ ] => inv H
  | [ H : step ((_ (id_semantics _)) _) _ _ _ _ |- _ ] => inv H
  end.
Ltac ese := eexists; repeat split; eauto.

Module CAT.

  Definition forward_simulation
             {liA1 liA2} (ccA: callconv liA1 liA2)
             {liB1 liB2} (ccB: callconv liB1 liB2) L1 L2 :=
    forward_simulation ccA ccB (normalize_sem L1) (normalize_sem L2).

  Section ID_PROPS.

    Context {liA liB} (L: semantics liA liB).

    (* TODO: notations like (st4 _ _ _ _ s1 s2 s3 s4) *)
    Inductive lu_ms: state (1 o L o 1) -> state (1 o (1 o L o 1)) -> Prop :=
    | lu_ms1 q:
      lu_ms (st1 1 _ (st_q q)) (st1 1 _ (st_q q))
    | lu_ms2 q s:
      lu_ms (st2 1 (L o 1) (st_q q) (st1 L _ s))
            (st2 1 (1 o L o 1) (st_q q) (st2 1 (L o 1) (st_q q) (st1 L _ s)))
    | lu_ms3 qi s qo:
      lu_ms (st2 1 (L o 1) (st_q qi) (st2 L 1 s (st_q qo)))
            (st2 1 (1 o L o 1) (st_q qi) (st2 1 (L o 1) (st_q qi) (st2 L 1 s (st_q qo))))
    | lu_ms4 qi s ro:
      lu_ms (st2 1 (L o 1) (st_q qi) (st2 L 1 s (st_r ro)))
            (st2 1 (1 o L o 1) (st_q qi) (st2 1 (L o 1) (st_q qi) (st2 L 1 s (st_r ro))))
    | lu_ms5 r:
      lu_ms (st1 1 _ (st_r r)) (st1 1 _ (st_r r)).

    Hint Constructors lu_ms.

    Lemma left_unit_1: forward_simulation 1 1 L (left_comp_id L).
    Proof.
      unfold forward_simulation, normalize_sem.
      etransitivity. instantiate (1 := 1 o (1 o L o 1)).
      2: {
        eapply categorical_compose_simulation'.
        reflexivity. apply assoc1.
        eapply Linking.linkorder_trans. apply id_skel_order.
        1-2: apply Linking.linkorder_refl.
      }
      constructor.
      eapply Forward_simulation
        with (fsim_order := (ltof _ (fun _ => O)))
             (fsim_match_states := fun _ _ _ x s1 s2 => x = s1 /\ lu_ms s1 s2).
      reflexivity. firstorder. 2: apply well_founded_ltof.
      intros se ? [] [] Hse. clear Hse.
      apply forward_simulation_plus;
        unfold left_comp_id, right_comp_id in *.
      - intros. inv H. repeat (inv_comp || inv_id). ese.
      - intros. repeat (inv_comp || inv_id). inv H. ese.
      - intros. repeat (inv_comp || inv_id). exists tt.
        inv H. ese.
        intros. repeat (inv_comp || inv_id). inv H. ese.
      - intros * HSTEP s2 HS. inv HS.
        + inv HSTEP; repeat (inv_comp || inv_id). ese.
          eapply plus_two. eapply step_push; repeat constructor.
          eapply step2. eapply step_push; repeat constructor; eauto.
          reflexivity.
        + inv HSTEP; repeat (inv_comp || inv_id).
          * ese. apply plus_one.
            apply step2. apply step2. apply step1; eassumption.
          * ese. apply plus_one. apply step2. apply step2.
            eapply step_push; try constructor; eauto.
          * ese. eapply plus_two.
            apply step2. eapply step_pop; constructor; eauto.
            eapply step_pop; repeat constructor; eauto.
            reflexivity.
        + inv HSTEP; repeat (inv_comp || inv_id).
        + inv HSTEP; repeat (inv_comp || inv_id).
          ese. apply plus_one. apply step2. apply step2.
          eapply step_pop; repeat constructor; eauto.
        + inv HSTEP; repeat (inv_comp || inv_id).
    Qed.

    Definition ul_measure (s: state (1 o (1 o L o 1))) :=
      match s with
      | st1 _ _ (st_q _) => 1%nat
      | st2 _ _ (st_q _) (st1 _ _ (st_q _)) => 0%nat
      | st2 _ _ (st_q _) (st1 _ _ (st_r _)) => 1%nat
      | st1 _ _ (st_r _) => 0%nat
      | _ => 0%nat
      end.
    Inductive ul_ms: state (1 o (1 o L o 1)) -> state (1 o L o 1) -> Prop :=
    | ul_ms1 q:
      ul_ms (st1 1 _ (st_q q)) (st1 1 _ (st_q q))
    | ul_ms1' q:
      ul_ms (st2 1 (1 o L o 1) (st_q q) (st1 1 _ (st_q q))) (st1 1 _ (st_q q))
    | ul_ms2 q s:
      ul_ms (st2 1 (1 o L o 1) (st_q q) (st2 1 (L o 1) (st_q q) (st1 L _ s)))
            (st2 1 (L o 1) (st_q q) (st1 L _ s))
    | ul_ms3 qi s qo:
      ul_ms (st2 1 (1 o L o 1) (st_q qi) (st2 1 (L o 1) (st_q qi) (st2 L 1 s (st_q qo))))
             (st2 1 (L o 1) (st_q qi) (st2 L 1 s (st_q qo)))
    | ul_ms4 qi s ro:
      ul_ms (st2 1 (1 o L o 1) (st_q qi) (st2 1 (L o 1) (st_q qi) (st2 L 1 s (st_r ro))))
            (st2 1 (L o 1) (st_q qi) (st2 L 1 s (st_r ro)))
    | ul_ms5 r:
      ul_ms (st1 1 _ (st_r r)) (st1 1 _ (st_r r))
    | ul_ms5' q r:
      ul_ms (st2 1 (1 o L o 1) (st_q q) (st1 1 _ (st_r r))) (st1 1 _ (st_r r)).
    Hint Constructors ul_ms.

    Lemma left_unit_2: forward_simulation 1 1 (left_comp_id L) L.
    Proof.
      unfold forward_simulation, normalize_sem.
      etransitivity. instantiate (1 := 1 o (1 o L o 1)).
      {
        eapply categorical_compose_simulation'.
        reflexivity. apply assoc2.
        eapply Linking.linkorder_trans. apply id_skel_order.
        1-2: apply Linking.linkorder_refl.
      }
      constructor.
      eapply Forward_simulation
        with (fsim_order := (ltof _ ul_measure))
             (fsim_match_states := fun _ _ _ i s1 s2 => i = s1 /\ ul_ms s1 s2).
      reflexivity. firstorder. 2: apply well_founded_ltof.
      intros se ? [] [] Hse.
      eapply forward_simulation_opt;
        unfold left_comp_id, right_comp_id in *.
      - intros. inv H. repeat (inv_comp || inv_id). ese.
      - intros. repeat (inv_comp || inv_id). inv H. ese.
      - intros. repeat (inv_comp || inv_id). inv H. exists tt. ese.
        intros. repeat (inv_comp || inv_id). inv H. ese.
      - intros * HSTEP s HS. inv HS.
        + inv HSTEP; repeat (inv_comp || inv_id).
          right. repeat split; eauto.
        + inv HSTEP; repeat (inv_comp || inv_id).
          left. ese. eapply step_push; constructor; eauto.
        + inv HSTEP; repeat (inv_comp || inv_id).
          * left. ese. apply step2. apply step1. assumption.
          * left. ese. apply step2.
            eapply step_push; repeat constructor; eauto.
          * left. ese.
            eapply step_pop; repeat constructor; eauto.
        + inv HSTEP; repeat (inv_comp || inv_id).
        + inv HSTEP; repeat (inv_comp || inv_id).
          left. ese.
          apply step2. eapply step_pop; repeat constructor; eauto.
        + inv HSTEP; repeat (inv_comp || inv_id).
        + inv HSTEP; repeat (inv_comp || inv_id).
          right. cbn. repeat split; eauto.
    Qed.

    Inductive ru_ms: state (1 o L o 1) -> state (1 o (L o 1) o 1) -> Prop :=
    | ru_ms1 q:
      ru_ms (st1 1 _ (st_q q)) (st1 1 _ (st_q q))
    | ru_ms2 q s:
      ru_ms (st2 1 (L o 1) (st_q q) (st1 L _ s))
            (st2 1 ((L o 1) o 1) (st_q q) (st1 (L o 1) _ (st1 L _ s)))
    | ru_ms3 qi s qo:
      ru_ms (st2 1 (L o 1) (st_q qi) (st2 L 1 s (st_q qo)))
            (st2 1 ((L o 1) o 1) (st_q qi) (st2 (L o 1) 1 (st2 L 1 s (st_q qo)) (st_q qo)))
    | ru_ms4 qi s qo ro:
      ru_ms (st2 1 (L o 1) (st_q qi) (st2 L 1 s (st_r ro)))
            (st2 1 ((L o 1) o 1) (st_q qi) (st2 (L o 1) 1 (st2 L 1 s (st_q qo)) (st_r ro)))
    | ru_ms5 r:
      ru_ms (st1 1 _ (st_r r)) (st1 1 _ (st_r r)).
    Hint Constructors ru_ms.

    Lemma right_unit_1: forward_simulation 1 1 L (right_comp_id L).
    Proof.
      unfold forward_simulation, normalize_sem.
      constructor.
      eapply Forward_simulation with (ltof _ (fun _ => O))
                                     (fun _ _ _ x s1 s2 => x = s1 /\ ru_ms s1 s2).
      reflexivity. firstorder. 2: apply well_founded_ltof.
      intros se ? [] [] Hse. clear Hse.
      apply forward_simulation_plus;
        unfold left_comp_id, right_comp_id in *.
      - intros. inv H. repeat (inv_comp || inv_id). ese.
      - intros. repeat (inv_comp || inv_id). inv H. ese.
      - intros. repeat (inv_comp || inv_id). inv H. exists tt. ese.
        intros. repeat (inv_comp || inv_id). inv H. ese.
      - intros * HSTEP s HS. inv HS.
        + inv HSTEP; repeat (inv_comp || inv_id). ese.
          apply plus_one. eapply step_push; repeat constructor; eauto.
        + inv HSTEP; repeat (inv_comp || inv_id).
          * ese. apply plus_one.
            apply step2. apply step1. apply step1. assumption.
          * ese. eapply plus_two.
            apply step2. apply step1. eapply step_push; eauto. constructor.
            apply step2. eapply step_push; repeat constructor.
            reflexivity.
          * ese. apply plus_one.
            eapply step_pop; repeat constructor. assumption.
        + inv HSTEP; repeat (inv_comp || inv_id).
        + inv HSTEP; repeat (inv_comp || inv_id).
          ese. eapply plus_two.
          apply step2. eapply step_pop; repeat constructor.
          apply step2. apply step1. eapply step_pop; try constructor; eauto.
          reflexivity.
        + inv HSTEP; repeat (inv_comp || inv_id).
    Qed.

    Definition ur_measure (s: state (1 o (L o 1) o 1)) :=
      match s with
      | st2 _ _ (st_q qi) (st1 _ _ (st2 _ _ s (st_q qo))) => 1%nat
      | st2 _ _ (st_q qi) (st2 _ _ (st2 _ _ s (st_q qo)) (st_r ro)) => 1%nat
      | _ => 0%nat
      end.
    Inductive ur_ms: state (1 o (L o 1) o 1) -> state (1 o L o 1) -> Prop :=
    | ur_ms1 q:
      ur_ms (st1 1 _ (st_q q)) (st1 1 _ (st_q q))
    | ur_ms2 q s:
      ur_ms (st2 1 ((L o 1) o 1) (st_q q) (st1 (L o 1) _ (st1 L _ s)))
            (st2 1 (L o 1) (st_q q) (st1 L _ s))
    | ur_ms3 qi s qo:
      ur_ms (st2 1 ((L o 1) o 1) (st_q qi) (st2 (L o 1) 1 (st2 L 1 s (st_q qo)) (st_q qo)))
            (st2 1 (L o 1) (st_q qi) (st2 L 1 s (st_q qo)))
    | ur_ms3' qi s qo:
      ur_ms (st2 1 ((L o 1) o 1) (st_q qi) (st1 (L o 1) _ (st2 L 1 s (st_q qo))))
            (st2 1 (L o 1) (st_q qi) (st2 L 1 s (st_q qo)))
    | ur_ms4 qi s qo ro:
      ur_ms (st2 1 ((L o 1) o 1) (st_q qi) (st2 (L o 1) 1 (st2 L 1 s (st_q qo)) (st_r ro)))
            (st2 1 (L o 1) (st_q qi) (st2 L 1 s (st_r ro)))
    | ur_ms4' qi s ro:
      ur_ms (st2 1 ((L o 1) o 1) (st_q qi) (st1 (L o 1) _ (st2 L 1 s (st_r ro))))
            (st2 1 (L o 1) (st_q qi) (st2 L 1 s (st_r ro)))
    | ur_ms5 r:
      ur_ms (st1 1 _ (st_r r)) (st1 1 _ (st_r r)).
    Hint Constructors ur_ms.

    Lemma right_unit_2: forward_simulation 1 1 (right_comp_id L) L.
    Proof.
      constructor.
      eapply Forward_simulation
        with (fsim_order := (ltof _ ur_measure))
             (fsim_match_states := fun _ _ _ i s1 s2 => i = s1 /\ ur_ms s1 s2).
      reflexivity. firstorder. 2: apply well_founded_ltof.
      intros se ? [] [] Hse. clear Hse.
      eapply forward_simulation_opt;
        unfold left_comp_id, right_comp_id in *.
      - intros. inv H. repeat (inv_comp || inv_id). ese.
      - intros. repeat (inv_comp || inv_id). inv H. ese.
      - intros. repeat (inv_comp || inv_id). inv H. exists tt. ese.
        intros. repeat (inv_comp || inv_id). inv H. ese.
      - intros * HSTEP s HS. inv HS.
        + inv HSTEP; repeat (inv_comp || inv_id).
          left. ese. eapply step_push; constructor; eauto.
        + inv HSTEP; repeat (inv_comp || inv_id).
          * left. ese. apply step2. apply step1. assumption.
          * left. ese. apply step2. eapply step_push; eauto. constructor.
          * left. ese. eapply step_pop; constructor. assumption.
        + inv HSTEP; repeat (inv_comp || inv_id).
        + inv HSTEP; repeat (inv_comp || inv_id).
          right. repeat split; eauto.
        + inv HSTEP; repeat (inv_comp || inv_id).
          right. repeat split; eauto.
        + inv HSTEP; repeat (inv_comp || inv_id).
          left. ese. apply step2. eapply step_pop; try constructor; eauto.
        + inv HSTEP; repeat (inv_comp || inv_id).
    Qed.

  End ID_PROPS.
  (* These properties are then lifted to ST.fsim *)

End CAT.


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
    w_int_step := {| rel s t := True |};
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

Section CAT_SIM.

  Lemma id_self_fsim `(cc: ST.callconv liA liB) sk:
    ST.forward_simulation cc cc (id_semantics sk) (id_semantics sk).
  Proof.
  Admitted.

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
      + rewrite <- Hsk. apply id_skel_order.
    - apply id_skel_order.
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

  (* TODO: move to CategoricalComp.v *)
  Section NORMALIZE_COMP.

    Context `(L1: semantics liB liC) `(L2: semantics liA liB).
    Variable sk: AST.program unit unit.

    Inductive nc_ms: state (comp_semantics' L1 L2 sk) ->
                     state (comp_semantics' (L1 o 1) (1 o L2) sk) -> Prop :=
    | nc_ms1 s:
      nc_ms (st1 L1 _ s)
            (st1 (L1 o 1) _ (st1 L1 _ s))
    | nc_ms2 s1 s2 q:
      nc_ms (st2 L1 L2 s1 s2)
            (st2 (L1 o 1) (1 o L2) (st2 L1 1 s1 (st_q q)) (st2 1 L2 (st_q q) s2)).
    Hint Constructors nc_ms.

    Lemma normalize_comp_fsim_sk1':
      forward_simulation 1 1 (comp_semantics' L1 L2 sk)
                         (comp_semantics' (L1 o 1) (1 o L2) sk).
    Proof.
      constructor.
      eapply Forward_simulation with
        (ltof _ (fun _ => O)) (fun _ _ _ x s1 s2 => x = s1 /\ nc_ms s1 s2).
      reflexivity. firstorder. 2: apply well_founded_ltof.
      intros se ? [] [] Hse.
      eapply forward_simulation_plus.
      - intros. inv H. inv H0.
        eexists. split; eauto.
        repeat constructor; eauto.
      - intros. inv H0. inv H.
        exists r1. split; repeat constructor; eauto.
      - intros. inv H0. inv H. exists tt.
        exists q1. repeat split; eauto.
        intros. inv H. inv H0.
        eexists. split; repeat constructor; eauto.
      - intros. inv H0.
        + inv H.
          * eexists. split; eauto.
            apply plus_one. apply step1. apply step1. assumption.
          * eexists; split; eauto.
            eapply plus_three.
            apply step1. eapply step_push; try constructor; eauto.
            eapply step_push; repeat constructor; eauto.
            apply step2. eapply step_push; try constructor; eauto.
            reflexivity. eauto.
        + inv H.
          * eexists. split; eauto.
            apply plus_one. apply step2. apply step2. eassumption.
            eauto.
          * eexists. split; eauto.
            eapply plus_three.
            apply step2. eapply step_pop; try constructor; eauto.
            eapply step_pop; repeat constructor; eauto.
            apply step1. eapply step_pop; try constructor; eauto.
            reflexivity.
    Qed.

    Lemma normalize_comp_fsim_sk1:
      forward_simulation 1 1 (normalize_sem (comp_semantics' L1 L2 sk))
                         (comp_semantics' (normalize_sem L1) (normalize_sem L2) sk).
    Proof.
      etransitivity. 2: apply assoc1.
      unfold normalize_sem. unfold left_comp_id.
      eapply categorical_compose_simulation'. reflexivity.
      etransitivity. 2: apply assoc2.
      etransitivity. 2: apply assoc2.
      eapply categorical_compose_simulation'. 2: reflexivity.
      etransitivity. 2: apply assoc1.
      apply normalize_comp_fsim_sk1'.
      all: cbn; (apply Linking.linkorder_refl || apply id_skel_order).
      Unshelve. apply sk.
    Qed.

    Definition cn_measure (s: state (comp_semantics' (L1 o 1) (1 o L2) sk)) :=
      match s with
      | st1 _ _ (st1 _ _ s) => 3%nat
      | st1 _ _ (st2 _ _ s (st_q _)) => 2%nat
      | st2 _ _ (st2 _ _ s (st_q _)) (st1 _ _ (st_q _)) => 1%nat
      | st2 _ _ (st2 _ _ _ (st_q _)) (st2 _ _ (st_q _) _) => 6%nat
      | st2 _ _ (st2 _ _ s (st_q _)) (st1 _ _ (st_r _)) => 5%nat
      | st1 _ _ (st2 _ _ s (st_r _)) => 4%nat
      | _ => 0%nat
      end.
    Inductive cn_ms se: state (comp_semantics' (L1 o 1) (1 o L2) sk) ->
                     state (comp_semantics' L1 L2 sk) -> Prop :=
    | cn_ms1 s:
      cn_ms se (st1 (L1 o 1) _ (st1 L1 _ s))
            (st1 L1 _ s)
    | cn_ms2 s1 s2 q:
      cn_ms se (st2 (L1 o 1) (1 o L2) (st2 L1 1 s1 (st_q q)) (st2 1 L2 (st_q q) s2))
            (st2 L1 L2 s1 s2)
    | cn_ms3 s q:
      at_external (L1 se) s q ->
      cn_ms se (st1 (L1 o 1) _ (st2 L1 1 s (st_q q)))
            (st1 L1 _ s)
    | cn_ms4 s q:
      at_external (L1 se) s q ->
      cn_ms se (st2 (L1 o 1) (1 o L2) (st2 L1 1 s (st_q q)) (st1 1 _ (st_q q)))
            (st1 L1 _ s)
    | cn_ms5 s1 s2 q r:
      final_state (L2 se) s2 r ->
      cn_ms se (st2 (L1 o 1) (1 o L2) (st2 L1 1 s1 (st_q q)) (st1 1 _ (st_r r)))
            (st2 L1 L2 s1 s2)
    | cn_ms6 s1 s2 r:
      final_state (L2 se) s2 r ->
      cn_ms se (st1 (L1 o 1) _ (st2 L1 1 s1 (st_r r)))
            (st2 L1 L2 s1 s2).
    Hint Constructors cn_ms.

    Lemma normalize_comp_fsim_sk2':
      forward_simulation 1 1 (comp_semantics' (L1 o 1) (1 o L2) sk)
                         (comp_semantics' L1 L2 sk).
    Proof.
      constructor.
      eapply Forward_simulation
        with (fsim_order := (ltof _ cn_measure))
             (fsim_match_states := fun _ se _ i s1 s2 =>
                                     i = s1 /\ cn_ms se s1 s2).
      reflexivity. firstorder. 2: apply well_founded_ltof.
      intros se ? [] [] Hse.
      eapply forward_simulation_opt.
      - intros. inv H. inv H0. inv H.
        eexists. split; eauto. constructor. assumption.
      - intros. inv H0. inv H1. inv H.
        eexists. split; eauto.
        constructor. eassumption. constructor.
      - intros. exists tt. inv H0. inv H1. inv H.
        eexists. repeat split; eauto.
        intros. inv H. inv H1. inv H5.
        eexists. split; eauto. constructor. assumption.
      - unfold left_comp_id, right_comp_id; intros.
        inv H0; repeat (inv_comp || inv_id).
        + left. eexists. split; eauto.
          apply step1. assumption.
        + (* 2 < 3 *)
          right. repeat split; eauto.
        + left. eexists. split; eauto.
          apply step2. assumption.
        + (* 5 < 6 *)
          right. repeat split; eauto.
        + (* 1 < 2 *)
          right. repeat split; eauto.
        + left. eexists. split; eauto.
          eapply step_push; eauto.
        + (* 4 < 5 *)
          right. repeat split; eauto.
        + left. eexists. split; eauto.
          eapply step_pop; eauto.
    Qed.

    Lemma normalize_comp_fsim_sk2:
      forward_simulation 1 1 (comp_semantics' (normalize_sem L1) (normalize_sem L2) sk)
                         (normalize_sem (comp_semantics' L1 L2 sk)).
    Proof.
      etransitivity. apply assoc2.
      eapply categorical_compose_simulation'. reflexivity.
      etransitivity. apply assoc1.
      etransitivity. apply assoc1.
      eapply categorical_compose_simulation'. 2: reflexivity.
      etransitivity. apply assoc2.
      apply normalize_comp_fsim_sk2'.
      all: cbn; (apply Linking.linkorder_refl || apply id_skel_order).
      Unshelve. apply sk.
    Qed.

  End NORMALIZE_COMP.

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

Lemma ccref_left_unit1 `(cc: ST.callconv liA liB):
  st_ccref cc (ST.cc_compose &1 cc).
Proof.
Admitted.

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
        instantiate (1 := (_, _)). split; eauto. constructor.
        eexists; split; eauto. instantiate (2 := Some tt). reflexivity.
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
        instantiate (1 := (_, _)). split; eauto. constructor.
        eexists; split; eauto. instantiate (1 := Some tt). reflexivity.
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
  apply Linking.linkorder_refl. apply id_skel_order.
  intros HC.
  exploit @st_cat_fsim_lcomp_sk. exact HB. exact HC.
  apply id_skel_order. apply Linking.linkorder_refl.
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

(** *** Encapsulation Primitives *)

(** Lemma 3.15 *)
Lemma encap_fsim_embed `(ccA: callconv liA1 liA2) `(ccB: callconv liB1 liB2) L1 L2:
  forward_simulation ccA ccB L1 L2 ->
  E.forward_simulation (callconv_embed ccA) (callconv_embed ccB)
                       (semantics_embed L1) (semantics_embed L2).
Admitted.

(** *** Simulation Convention FBK *)
Definition callconv_fbk {li1 li2 K1 K2} (cc: ST.callconv (li1@K1) (li2@K2)): ST.callconv li1 li2.
Admitted.

(** Lemma 3.17 *)
Lemma fsim_fbk {K1 K2: PSet}
      `(ccA: ST.callconv liA1 liA2) `(ccB: ST.callconv (liB1@K1) (liB2@K2)) L1 L2:
  E.forward_simulation ccA ccB L1 L2 ->
  E.forward_simulation ccA (callconv_fbk ccB) (semantics_fbk L1) (semantics_fbk L2).
Admitted.

(** *** REVEAL Simulation Convention *)
Definition cc_reveal {K: PSet} {li} : ST.callconv li (li@K).
Admitted.

(** Lemma 3.18 *)
Lemma fsim_reveal {K: PSet} {liA liB} (L: liA +-> liB@K):
  E.forward_simulation (callconv_embed cc_id) cc_reveal (semantics_fbk L) L.
Admitted.

(** *** FBK vs LIFT *)
Definition st_cceqv {li1 li2} (cc cc': ST.callconv li1 li2) :=
  st_ccref cc cc' /\ st_ccref cc' cc.

Lemma callconv_fbk_lift {K1 K2: PSet} `(cc: ST.callconv li1 li2):
  st_ccref (callconv_fbk (ST.callconv_lift cc K1 K2)) cc.
Admitted.

(** *** Basics *)

Definition st_cc_id {li} : ST.callconv li li := callconv_embed cc_id.

(** Lemma 3.4 *)
Definition encap_equiv_simulation {liA liB} (L1 L2: liA +-> liB) :=
  E.forward_simulation st_cc_id st_cc_id L1 L2 /\ E.forward_simulation st_cc_id st_cc_id L2 L1.

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

(** * Properties about Simulations for Components with Encapsulated States *)

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

  (** Lemma 3.14 *)
  Lemma encap_fsim_comp : E.forward_simulation ccA ccC Ls Lt.
  Proof.
    unfold E.forward_simulation in *. unfold comp_esem in *.
    apply st_fsim_lift with (K1:=pstate L2s) (K2:=pstate L2t) in HL1.
    exploit @st_fsim_comp. exact HL1. exact HL2.
  Admitted.
End COMP.

Section ENCAP_COMP_FSIM.

  Context `(ccA1: ST.callconv liAs liAn) `(ccA2: ST.callconv liAn liAf)
          `(ccB1: ST.callconv liBs liBn) `(ccB2: ST.callconv liBn liBf)
          (Ls: liAs +-> liBs) (Ln: liAn +-> liBn) (Lf: liAf +-> liBf).
  Context (H1: E.forward_simulation ccA1 ccB1 Ls Ln)
          (H2: E.forward_simulation ccA2 ccB2 Ln Lf).

  (** Lemma 3.11 *)
  Lemma encap_compose_forward_simulation:
    E.forward_simulation (ST.cc_compose ccA1 ccA2)
                         (ST.cc_compose ccB1 ccB2) Ls Lf.
  Admitted.

End ENCAP_COMP_FSIM.

(* This is a special property required to bootstrap *)
Section DENORMALIZE.

  Context `(ccA: ST.callconv liA1 liA2)
          `(ccB: ST.callconv liB1 liB2)
          (L1: semantics liA1 liB1)
          (L2: semantics liA2 liB2)
          (HL: ST.fsim_components ccA ccB (1 o (1 o L1 o 1) o 1)
                                 (1 o (1 o L2 o 1) o 1)).
  Inductive df_ms: Genv.symtbl -> ST.ccworld ccA -> ST.ccworld ccB ->
                   ST.fsim_index HL ->
                   state (1 o L1 o 1) -> state (1 o L2 o 1) -> Prop :=
  | df_ms1 se wa wb i q1 q2:
    ST.fsim_match_states HL se wa wb i
                         (st1 1 _ (st_q q1)) (st1 1 _ (st_q q2)) ->
    df_ms se wa wb i (st1 1 _ (st_q q1)) (st1 1 _ (st_q q2))
  | df_ms2 se wa wb i q1 q2 s1 s2:
    ST.fsim_match_states HL se wa wb i
                         (st2 1 ((1 o L1 o 1) o 1) (st_q q1)
                              (st1 (1 o L1 o 1) _
                                   (st2 1 (L1 o 1) (st_q q1) (st1 L1 _ s1))))
                         (st2 1 ((1 o L2 o 1) o 1) (st_q q2)
                              (st1 (1 o L2 o 1) _
                                   (st2 1 (L2 o 1) (st_q q2) (st1 L2 _ s2)))) ->
    df_ms se wa wb i (st2 1 (L1 o 1) (st_q q1) (st1 L1 _ s1))
          (st2 1 (L2 o 1) (st_q q2) (st1 L2 _ s2))
  | df_ms3 se wa wb i q1 q2 s1 s2 q3 q4:
    ST.fsim_match_states HL se wa wb i
                         (st2 1 ((1 o L1 o 1) o 1) (st_q q1)
                              (st2 (1 o L1 o 1) 1
                                   (st2 1 (L1 o 1) (st_q q1) (st2 L1 1 s1 (st_q q3)))
                                   (st_q q3)))
                         (st2 1 ((1 o L2 o 1) o 1) (st_q q2)
                              (st2 (1 o L2 o 1) 1
                                   (st2 1 (L2 o 1) (st_q q2) (st2 L2 1 s2 (st_q q4)))
                                   (st_q q4))) ->
    df_ms se wa wb i (st2 1 (L1 o 1) (st_q q1) (st2 L1 1 s1 (st_q q3)))
          (st2 1 (L2 o 1) (st_q q2) (st2 L2 1 s2 (st_q q4)))
  | df_ms4 se wa wb i q1 q2 s1 s2 q3 q4 r1 r2:
    ST.fsim_match_states HL se wa wb i
                         (st2 1 ((1 o L1 o 1) o 1) (st_q q1)
                              (st2 (1 o L1 o 1) 1
                                   (st2 1 (L1 o 1) (st_q q1) (st2 L1 1 s1 (st_q q3)))
                                   (st_r r1)))
                         (st2 1 ((1 o L2 o 1) o 1) (st_q q2)
                              (st2 (1 o L2 o 1) 1
                                   (st2 1 (L2 o 1) (st_q q2) (st2 L2 1 s2 (st_q q4)))
                                   (st_r r2))) ->
    df_ms se wa wb i (st2 1 (L1 o 1) (st_q q1) (st2 L1 1 s1 (st_r r1)))
          (st2 1 (L2 o 1) (st_q q2) (st2 L2 1 s2 (st_r r2)))
  | df_ms5 se wa wb i r1 r2:
    ST.fsim_match_states HL se wa wb i
                         (st1 1 _ (st_r r1)) (st1 1 _ (st_r r2)) ->
    df_ms se wa wb i (st1 1 _ (st_r r1)) (st1 1 _ (st_r r2)).

  Lemma denormalize_fsim':
    ST.fsim_components ccA ccB (1 o L1 o 1) (1 o L2 o 1).
  Proof.
    apply ST.Forward_simulation with (ST.fsim_order HL) df_ms (ST.fsim_invariant HL).
    apply ST.fsim_invariant_env_step.
    apply (ST.fsim_skel HL).
    apply ST.fsim_initial_world.
    pose proof (ST.fsim_footprint HL) as X. cbn in X |- *. firstorder.
    2: apply ST.fsim_order_wf.
    intros wa wb se INV. pose proof (ST.fsim_lts HL wa wb se INV) as X.
    constructor.
    - intros q1 q2 s1 wb' Hb Hq H. inv H. inv H0.
      edestruct (@ST.fsim_match_initial_states) as (i & s2 & A & B); eauto.
      constructor. constructor.
      destruct B as (wa' & wb'' & Ha & Hb' & H').
      inv A. inv H.
      exists i, (st1 1 _ (st_q q2)). split.
      repeat constructor.
      exists wa', wb''. repeat split; eauto.
      constructor. eauto.
    - intros wa' wb' i s1 s2 r1 Hs H. inv H. inv H0. inv Hs.
      edestruct (@ST.fsim_match_final_states) as (r2x & Hr2 & A); eauto.
      repeat constructor.
      destruct A as (wb'' & Hb' & Hr & HI).
      inv Hr2. inv H0. exists r2x. repeat split.
      exists wb''. repeat split; eauto.
    - intros wa1 wb1 i s1 s2 q1 Hs H. inv H. inv H0. inv H. inv Hs.
      edestruct (@ST.fsim_match_external) as (q2x & Hq2 & wa2 & Ha2 & Hq & Hk); eauto.
      repeat constructor.
      inv Hq2. inv H2. inv H3. exists q2x. split. repeat constructor.
      exists wa2. repeat split; eauto.
      intros r1 r2 s1' wa3 Ha3 Hr H. inv H. inv H4. inv H3.
      edestruct Hk as (i' & s2' & Hs2' & wa4 & wb2 & Ha4 & Hb2 & Hm); eauto.
      repeat constructor. inv Hs2'. inv H3. inv H4.
      exists i'. eexists. repeat split; eauto.
      exists wa4, wb2. repeat split; eauto.
      econstructor. eauto.
    - intros s1 t s1' HSTEP wa1 wb1 i s2 HS.
      inv HS.
      + inv HSTEP. inv H1. inv H1. inv H2.


  Admitted.

End DENORMALIZE.

Lemma denormalize_fsim `(ccA: ST.callconv liA1 liA2)
      `(ccB: ST.callconv liB1 liB2) L1 L2:
  ST.forward_simulation ccA ccB (1 o (1 o L1 o 1) o 1)
                        (1 o (1 o L2 o 1) o 1) ->
  ST.forward_simulation ccA ccB (1 o L1 o 1) (1 o L2 o 1).
Admitted.
