Require Import Coqlib.
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import CKLR.
Require Import LanguageInterface.
Require Import Smallstep.

Set Implicit Arguments.

Require Import RelationClasses.
Require Import Relations.


Class Lens (T A: Type) :=
  {
    get : T -> A;
    set : T -> A -> T;
    get_set : forall t a, get (set t a) = a;
    set_get : forall t, set t (get t) = t;
    set_set : forall t a1 a2, set (set t a1) a2 = set t a2;
  }.

Program Instance lens_id {T: Type} : Lens T T :=
  {
    get t := t;
    set _ t := t;
  }.

Program Instance lens_fst {U V} : Lens (U * V) U :=
  {
    get '(u, v) := u;
    set '(_, v) u := (u, v);
  }.

Program Instance lens_snd {U V} : Lens (U * V) V :=
  {
    get '(u, v) := v;
    set '(u, _) v := (u, v);
  }.

Program Instance lens_unit {T} : Lens T unit :=
  {
    get _ := tt;
    set t tt := t;
  }.
Next Obligation. intros; try easy. now destruct a. Defined.

Program Instance lens_prod {T S A B: Type} `(Lens T A) `(Lens S B) : Lens (T * S) (A * B) :=
  {
    get '(t, s) := (get t, get s);
    set '(t, s) '(a, b) := (set t a, set s b);
  }.
Next Obligation. now rewrite !get_set. Defined.
Next Obligation. now rewrite !set_get. Defined.
Next Obligation. now rewrite !set_set. Defined.

Program Instance lens_comp {U V W: Type} `(Lens U V) `(Lens V W) : Lens U W :=
  {
    get u := get (get u);
    set u w := set u (set (get u) w);
  }.
Next Obligation. now rewrite !get_set. Defined.
Next Obligation. now rewrite !set_get. Defined.
Next Obligation. rewrite !get_set. rewrite !set_set. reflexivity. Defined.


Class World (T: Type) :=
  {
    w_state : Type;
    w_lens : Lens T w_state;
    w_acci : w_state -> w_state -> Prop;
    w_acce : w_state -> w_state -> Prop;
    w_acci_trans : PreOrder w_acci;
  }.

Existing Instance w_lens.
Existing Instance w_acci_trans.
Arguments w_state {_} _.
Arguments w_acci {_ _}.
Arguments w_acce {_ _}.

Infix "*->" := w_acci (at level 60, no associativity).
Infix "o->" := w_acce (at level 55, no associativity).

Section PROD.
  Context {A: Type} {B:Type} (WA: World A) (WB: World B).

  Program Instance world_prod: World (A * B) :=
    {
      w_state := @w_state A _ * @w_state B _;
      w_lens := lens_prod w_lens w_lens;
      w_acci := Relators.prod_rel (w_acci) (w_acci) ;
      w_acce := Relators.prod_rel w_acce w_acce;
    }.

  Lemma ext_step_prod (a1 a2: w_state WA) (b1 b2: w_state WB):
    (a1, b1) o-> (a2, b2) <-> a1 o-> a2 /\ b1 o-> b2.
  Proof.
    split.
    - intros H. inv H. cbn in *. split; eauto.
    - intros [X Y]. split; eauto.
  Qed.

  Lemma int_step_prod (a1 a2: w_state WA) (b1 b2: w_state WB):
    (a1, b1) *-> (a2, b2) <-> a1 *-> a2 /\ b1 *-> b2.
  Proof.
    split.
    - intros H. inv H. cbn in *. split; eauto.
    - intros [X Y]. split; eauto.
  Qed.

End PROD.
Arguments world_prod {_} {_} _ _.

Section SYMTBL.

  Context {T: Type} {W: World T}.

  Instance symtbl_world  : World (Genv.symtbl * T) :=
    {
      w_state := @w_state T _;
      w_lens := lens_comp lens_snd w_lens;
      w_acci := w_acci;
      w_acce := w_acce;
    }.

End SYMTBL.


Module GS.

  Record callconv {li1 li2} :=
  mk_callconv {
    ccworld : Type;
    ccworld_world : World ccworld;
    match_senv: ccworld -> Genv.symtbl -> Genv.symtbl -> Prop;
    match_query: ccworld -> query li1 -> query li2 -> Prop;
    match_reply: ccworld -> reply li1 -> reply li2 -> Prop;

    match_senv_public_preserved:
      forall w se1 se2,
        match_senv w se1 se2 ->
        forall id, Genv.public_symbol se2 id = Genv.public_symbol se1 id;
    match_senv_valid_for:
      forall w se1 se2 sk,
        match_senv w se1 se2 ->
        Genv.valid_for sk se1 ->
        Genv.valid_for sk se2;
    }.

  Arguments callconv: clear implicits.
  (* Existing Instance ccworld_world | 3. *)
  
  Definition gworld {li1 li2}(cc: callconv li1 li2) := w_state (ccworld_world cc).

  Program Definition cc_compose {li1 li2 li3}
          (cc12: callconv li1 li2) (cc23: callconv li2 li3) :=
    {|
      ccworld := Genv.symtbl * (ccworld cc12 * ccworld cc23);
      ccworld_world := @symtbl_world _ (world_prod (ccworld_world cc12) (ccworld_world cc23));
      match_senv '(se2, (w12, w23)) se1 se3 :=
        match_senv cc12 w12 se1 se2 /\ match_senv cc23 w23 se2 se3;
      match_query '(se2, (w12, w23)) q1 q3 :=
      exists q2, match_query cc12 w12 q1 q2 /\ match_query cc23 w23 q2 q3;
      match_reply '(se2, (w12, w23)) r1 r3 :=
      exists r2, match_reply cc12 w12 r1 r2 /\ match_reply cc23 w23 r2 r3;
    |}.
  Next Obligation.
    etransitivity; eapply match_senv_public_preserved ; eauto.
  Qed.
  Next Obligation.
    eapply match_senv_valid_for; eauto.
    eapply match_senv_valid_for; eauto.
  Qed.

  (* Declare Scope gc_cc_scope.
  Infix "@" := cc_compose (at level 30, right associativity) : gs_cc_scope. *)
  
Section FSIM.

    Context {li1 li2} (cc: callconv li1 li2).
    Context (se1 se2: Genv.symtbl).
    Context (wb: ccworld cc).
    Context {state1 state2: Type}.

    Let gw_type := gworld cc.
    
    Record fsim_properties
           (L1: lts li1 li1 state1) (L2: lts li2 li2 state2)
           (index: Type) (order: index -> index -> Prop)
           (match_states: gw_type -> index -> state1 -> state2 -> Prop) :=
      {
        fsim_match_valid_query:
        forall q1 q2, match_query cc wb q1 q2 ->
                 valid_query L2 q2 = valid_query L1 q1;
        fsim_match_initial_states:
          forall q1 q2 s1, match_query cc wb q1 q2 -> initial_state L1 q1 s1 ->
          match_senv cc wb se1 se2 ->
          exists i, exists s2, initial_state L2 q2 s2 /\ match_states (get wb) i s1 s2;
        fsim_match_final_states:
          forall gw i s1 s2 r1, match_states gw i s1 s2 -> final_state L1 s1 r1 ->
          exists r2 gw', final_state L2 s2 r2 /\ (get wb) o-> gw' /\ gw *-> gw' /\
          match_reply cc (set wb gw') r1 r2;
        fsim_match_external:
          forall gw i s1 s2 q1, match_states gw i s1 s2 -> at_external L1 s1 q1 ->
          exists wa q2 , at_external L2 s2 q2 /\ gw *-> (get wa) /\
          match_query cc wa q1 q2 /\ match_senv cc wa se1 se2 /\
          forall r1 r2 s1' gw'', (get wa) o-> gw'' -> match_reply cc (set wa gw'') r1 r2 ->
          after_external L1 s1 r1 s1' ->
          exists i' s2', after_external L2 s2 r2 s2' /\
          match_states gw'' i' s1' s2';
          (* exists gw''' , gw'' *-> gw''' /\ match_states gw''' i' s1' s2'; (*The problem of va passes*) *)
        fsim_simulation:
          forall s1 t s1', Step L1 s1 t s1' ->
          forall gw i s2, match_states gw i s1 s2 ->
          exists i', exists s2', (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i)) /\
          match_states gw i' s1' s2';
      }.
    Arguments fsim_properties : clear implicits.

    Lemma fsim_simulation':
      forall L1 L2 index order match_states, fsim_properties L1 L2 index order match_states ->
      forall i s1 t s1', Step L1 s1 t s1' ->
      forall gw s2, match_states gw i s1 s2 ->
      exists i',
      ((exists s2', Plus L2 s2 t s2' /\ match_states gw i' s1' s2')
      \/ (order i' i /\ t = E0 /\ match_states gw i' s1' s2)).
    Proof.
      intros. exploit @fsim_simulation; eauto.
      intros (i' & s2' & A & B).
      exists i'. repeat split; eauto.
      destruct A.
      left; exists s2'; auto.
      destruct H2. inv H2.
      right; eauto.
      left; exists s2'; split; auto. econstructor; eauto.
    Qed.

    
    (** ** Forward simulation diagrams. *)

    (** Various simulation diagrams that imply forward simulation *)
    
    Section FORWARD_SIMU_DIAGRAMS.
      
      Variable L1: lts li1 li1 state1.
      Variable L2: lts li2 li2 state2.

      Variable match_states: gw_type -> state1 -> state2 -> Prop.

      Hypothesis match_valid_query:
        forall q1 q2, match_query cc wb q1 q2 ->
                 valid_query L2 q2 = valid_query L1 q1.

      Hypothesis match_initial_states:
        forall q1 q2 s1, match_query cc wb q1 q2 -> initial_state L1 q1 s1 ->
        exists s2, initial_state L2 q2 s2 /\ match_states (get wb) s1 s2.

      Hypothesis match_final_states:
        forall gw s1 s2 r1, match_states gw s1 s2 -> final_state L1 s1 r1 ->
        exists r2 gw', final_state L2 s2 r2 /\ (get wb) o-> gw' /\ gw *-> gw'  /\ match_reply cc (set wb gw') r1 r2.

      (* fsim_match_external:
          forall gw i s1 s2 q1, match_states gw i s1 s2 -> at_external L1 s1 q1 ->
          exists wa q2 , at_external L2 s2 q2 /\ gw *-> (get wa) /\
          match_query cc wa q1 q2 /\ match_senv cc wa se1 se2 /\
          forall r1 r2 s1' gw'', (get wa) o-> gw'' -> match_reply cc (set wa gw'') r1 r2 ->
          after_external L1 s1 r1 s1' ->
          exists i' s2', after_external L2 s2 r2 s2' /\
          match_states gw'' i' s1' s2';
          (* exists gw''' , gw'' *-> gw''' /\ match_states gw''' i' s1' s2'; (*The problem of va passes*) *)
        fsim_simulation:
          forall s1 t s1', Step L1 s1 t s1' ->
          forall gw i s2, match_states gw i s1 s2 ->
          exists i', exists s2', (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i)) /\
          match_states gw i' s1' s2';*)
      Hypothesis match_external:
        forall gw s1 s2 q1, match_states gw s1 s2 -> at_external L1 s1 q1 ->
            exists wA q2, at_external L2 s2 q2 /\ gw *-> (get wA) /\
                       match_query cc wA q1 q2 /\ match_senv cc wA se1 se2 /\
                       forall r1 r2 s1' gw'', (get wA) o-> gw'' -> match_reply cc (set wA gw'') r1 r2 ->
                                         after_external L1 s1 r1 s1' ->
                                         exists s2', after_external L2 s2 r2 s2' /\ match_states gw'' s1' s2'.

      Let ms gw idx s1 s2 := idx = s1 /\ match_states gw s1 s2.

(** Simulation when one transition in the first program
    corresponds to zero, one or several transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_STAR_WF.

(** [order] is a well-founded ordering associated with states
  of the first semantics.  Stuttering steps must correspond
  to states that decrease w.r.t. [order]. *)

Variable order: state1 -> state1 -> Prop.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2 gw, match_states gw s1 s2 ->
  exists s2',
  (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order s1' s1))
  /\ match_states gw s1' s2'.

Lemma forward_simulation_star_wf:
  fsim_properties L1 L2 state1 order ms.
Proof.
  subst ms;
  constructor.
- auto.
- intros. exploit match_initial_states; eauto. intros [s2 [A B]].
    exists s1; exists s2; auto.
- intros. destruct H. eapply match_final_states; eauto.
- intros. destruct H. edestruct match_external as (w & q2 & H2 & Hac & Hq & Hw & Hr); eauto.
  exists w, q2. intuition auto. edestruct Hr as (s2' & Hs2' & Hs'); eauto.
- intros. destruct H0. subst i. exploit simulation; eauto. intros [s2' [A B]].
  exists s1'; exists s2'; intuition auto.
Qed.

End SIMULATION_STAR_WF.

Section SIMULATION_STAR.

(** We now consider the case where we have a nonnegative integer measure
  associated with states of the first semantics.  It must decrease when we take
  a stuttering step. *)

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2 gw, match_states gw s1 s2 ->
  (exists s2', Plus L2 s2 t s2' /\ match_states gw s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states gw s1' s2)%nat.

Lemma forward_simulation_star:
  fsim_properties L1 L2 state1 (ltof _ measure) ms.
Proof.
  apply forward_simulation_star_wf.
  intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
  exists s2'; auto.
  exists s2; split. right; split. rewrite B. apply star_refl. auto. auto.
Qed.

End SIMULATION_STAR.

(** Simulation when one transition in the first program corresponds
    to one or several transitions in the second program. *)

Section SIMULATION_PLUS.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2 gw, match_states gw s1 s2 ->
  exists s2', Plus L2 s2 t s2' /\ match_states gw s1' s2'.

Lemma forward_simulation_plus:
  fsim_properties L1 L2 state1 (ltof _ (fun _ => O)) ms.
Proof.
  apply forward_simulation_star.
  intros. exploit simulation; eauto.
Qed.

End SIMULATION_PLUS.

(** Lock-step simulation: each transition in the first semantics
    corresponds to exactly one transition in the second semantics. *)

Section SIMULATION_STEP.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2 gw, match_states gw s1 s2 ->
  exists s2', Step L2 s2 t s2' /\ match_states gw s1' s2'.

Lemma forward_simulation_step:
  fsim_properties L1 L2 state1 (ltof _ (fun _ => O)) ms.
Proof.
  apply forward_simulation_plus.
  intros. exploit simulation; eauto. intros [s2' [A B]].
  exists s2'; split; auto. apply plus_one; auto.
Qed.

End SIMULATION_STEP.

(** Simulation when one transition in the first program
    corresponds to zero or one transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_OPT.

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2 gw, match_states gw s1 s2 ->
  (exists s2', Step L2 s2 t s2' /\ match_states gw s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states gw s1' s2)%nat.

Lemma forward_simulation_opt:
  fsim_properties L1 L2 state1 (ltof _ measure) ms.
Proof.
  apply forward_simulation_star.
  intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
  left; exists s2'; split; auto. apply plus_one; auto.
  right; auto.
Qed.

End SIMULATION_OPT.

End FORWARD_SIMU_DIAGRAMS.

    (** ** Forward simulation with the "eventually" modality *)

(** A forward simulation diagram where the first semantics can take some extra steps
    before reaching a state that restores the simulation relation. *)

Section FORWARD_SIMU_EVENTUALLY.

Variable L1: lts li1 li1 state1.
Variable L2: lts li2 li2 state2.
Variable index: Type.
Variable order: index -> index -> Prop.
Variable match_states: gw_type -> index -> state1 -> state2 -> Prop.

Hypothesis order_wf: well_founded order.

Hypothesis match_valid_query:
  forall q1 q2, match_query cc wb q1 q2 ->
  valid_query L2 q2 = valid_query L1 q1.

Hypothesis initial_states:
  forall q1 q2 s1, match_query cc wb q1 q2 -> initial_state L1 q1 s1 ->
              exists i, exists s2, initial_state L2 q2 s2 /\ match_states (get wb) i s1 s2.

Hypothesis final_states:
  forall wp i s1 s2 r1,
    match_states wp i s1 s2 -> final_state L1 s1 r1 ->
    exists r2 wp', final_state L2 s2 r2 /\ (get wb) o-> wp' /\ wp *-> wp' /\ match_reply cc (set wb wp')  r1 r2.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall wp i s2, match_states wp i s1 s2 ->
  exists n i' s2',
     (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
     /\ Eventually L1 n s1' (fun s1'' => match_states wp i' s1'' s2').

Hypothesis match_external:
  forall gw i s1 s2 q1, match_states gw i s1 s2 -> at_external L1 s1 q1 ->
  exists wA q2, at_external L2 s2 q2 /\ gw *-> (get wA) /\ match_query cc wA q1 q2 /\ match_senv cc wA se1 se2 /\
  forall r1 r2 s1' gw'', (get wA) o-> gw'' -> match_reply cc (set wA gw'') r1 r2 -> after_external L1 s1 r1 s1' ->
               exists i' s2', after_external L2 s2 r2 s2' /\ match_states gw'' i' s1' s2'.

(*Hypothesis public_preserved:
  forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id. *)

Let ms := fun gw i s1 s2 => Eventually L1 (snd i) s1 (fun s1'' => match_states gw (fst i) s1'' s2).
Let index' :=  (index * nat)%type.
Let order' := lex_ord order Nat.lt. 
Lemma forward_simulation_eventually: fsim_properties L1 L2 index' order' ms.
Proof.
  constructor.
- auto.
- intros. exploit initial_states; eauto. intros (i & s2 & A & B).
  exists (i, O), s2; split; auto using eventually_now.
  constructor. simpl. eauto.
- intros gw [i n] s1 s2 r EV FS; simpl in *. inv EV.
  + eapply final_states; eauto.
  + eelim H; eauto.
- intros gw [i n] s1 s2 q1 EV AT. simpl in *. inv EV.
  + exploit match_external; eauto. intros (wA & q2 & AT' & ACI &  MQ & MS & AFTER).
    exists wA, q2. intuition eauto. exploit AFTER; eauto.
    intros (i' & s2' & A & B).
    exists (i', O), s2'. split. eauto. constructor. simpl. eauto.
  + eelim H0; eauto.
- intros s1 t s1' ST gw [i n] s2 EV; simpl in *. inv EV.
  + exploit simulation; eauto. intros (n' & i' & s2' & A & B).
    exists (i', n'), s2'; split; auto.
    destruct A as [P | [P Q]]; auto using lex_ord_left.
    right. split. eauto. constructor. eauto.
  + apply H1 in ST. destruct ST as (A & B). subst t.
    exists (i, n0), s2; split.
    right; split. apply star_refl. 
    apply lex_ord_right. simpl in H2. lia.
    exact B.
Qed.
    
End FORWARD_SIMU_EVENTUALLY.

(** Two simplified diagrams. *)

Section FORWARD_SIMU_EVENTUALLY_SIMPL.

Variable L1: lts li1 li1 state1.
Variable L2: lts li2 li2 state2.
Variable match_states: gw_type -> state1 -> state2 -> Prop.

(*Hypothesis public_preserved:
  forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id. *)
Hypothesis match_valid_query:
  forall q1 q2, match_query cc wb q1 q2 ->
           valid_query L2 q2 = valid_query L1 q1.
Hypothesis initial_states:
  forall q1 q2 s1, match_query cc wb q1 q2 -> initial_state L1 q1 s1  ->
  exists s2, initial_state L2 q2 s2 /\ match_states (get wb) s1 s2.
Hypothesis final_states:
  forall gw s1 s2 r1,
    match_states gw s1 s2 -> final_state L1 s1 r1 ->
    exists r2 gw', final_state L2 s2 r2 /\ (get wb) o-> gw' /\ gw *-> gw' /\ match_reply cc (set wb gw') r1 r2.
Hypothesis match_external:
  forall gw s1 s2 q1, match_states gw s1 s2 -> at_external L1 s1 q1 ->
  exists wA q2, at_external L2 s2 q2 /\ gw *-> (get wA) /\ match_query cc wA q1 q2 /\ match_senv cc wA se1 se2 /\
  forall r1 r2 s1' gw'', (get wA) o-> gw'' -> match_reply cc (set wA gw'') r1 r2 -> after_external L1 s1 r1 s1' ->
  exists s2', after_external L2 s2 r2 s2' /\ match_states gw'' s1' s2'.

(** Simplified "plus" simulation diagram, when L2 always makes at least one transition. *)

Section FORWARD_SIMU_EVENTUALLY_PLUS.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall gw s2, match_states gw s1 s2 ->
  exists n s2',
     Plus L2 s2 t s2'
  /\ Eventually L1 n s1' (fun s1'' => match_states gw s1'' s2').

Let ms' := fun gw (i:nat) s1 s2 => match_states gw s1 s2.
Let ms := fun gw i s1 s2 => Eventually L1 (snd i) s1 (fun s1'' => ms' gw (fst i) s1'' s2).
Let index' :=  (nat * nat)%type.
Let order' := lex_ord lt Nat.lt. 

Lemma forward_simulation_eventually_plus: fsim_properties L1 L2 index' order' ms.
Proof.
  apply forward_simulation_eventually.
- auto.
- intros. exploit initial_states. eauto. eauto.
  intros (s2 & A & B). exists O, s2; auto.
- intros. eapply final_states; eauto.
- intros. exploit simulation; eauto. intros (n & s2' & A & B).
  exists n, O, s2'; eauto.  
- intros. exploit match_external; eauto.
  intros (wA & q2 & A & B & C & D & E). exists wA, q2. repeat apply conj.
  eauto. eauto. eauto. eauto. intros. exploit E. eauto. eauto. eauto.
  intros (s2' & A' & B'). exists O, s2'; auto.
Qed.

End FORWARD_SIMU_EVENTUALLY_PLUS.

(** Simplified "star" simulation diagram, with a decreasing, well-founded order on L1 states. *)

Section FORWARD_SIMU_EVENTUALLY_STAR_WF.

Variable order: state1 -> state1 -> Prop.
(* Hypothesis order_wf: well_founded order. *)

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall gw s2, match_states gw s1 s2 ->
     (exists s2',
        (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order s1' s1)) /\ match_states gw s1' s2')
  \/ (exists n s2',
        Plus L2 s2 t s2' /\ Eventually L1 n s1' (fun s1'' => match_states gw s1'' s2')).

Let index' := (nat * state1)%type.
Let order' := lex_ord Nat.lt order.
Let ms := fun gw i s1 s2 => snd i = s1 /\ Eventually L1 (fst i) s1 (fun s1'' => match_states gw s1'' s2).
Lemma forward_simulation_eventually_star_wf: fsim_properties L1 L2 index' order' ms.
Proof.
  constructor; intros.
- auto.
- exploit initial_states; eauto. intros (s2 & A & B).
  exists (O, s1), s2. split. auto. constructor. auto. auto using eventually_now.
- destruct i as [n s11]; destruct H as [P Q]; simpl in *; subst s11.
  inv Q.
  + eapply final_states; eauto.
  + eelim H; eauto.
- destruct i as [n s11]; destruct H as [P Q]; simpl in *; subst s11.
  inv Q.
  + exploit match_external; eauto. intros (wA & q2 & A & B & C & D & E).
    exists wA, q2. intuition eauto. exploit E; eauto.
    intros (s2' & A' & B'). exists (O, s1'). exists s2'. split. eauto.
    unfold ms. split. eauto. constructor. eauto.
  + eelim H1; eauto.
- destruct i as [n s11]; destruct H0 as [P Q]; simpl in *; subst s11.
  inv Q.
  + exploit simulation; eauto. intros [(s2' & A & B) | (n & s2' & A & B)].
    * exists (O, s1'), s2'; split. 
      destruct A as [A | [A1 A2]]. eauto. right. split; auto using lex_ord_right.
      eapply lex_ord_right. eauto. constructor; eauto using eventually_now.
    * exists (n, s1'), s2'; unfold ms; auto.
  + apply H2 in H. destruct H. subst t.
    exists (n0, s1'), s2; split.
    right; split. apply star_refl. apply lex_ord_left; lia.
    unfold ms. auto.
Qed.

End FORWARD_SIMU_EVENTUALLY_STAR_WF.

(** Simplified "star" simulation diagram, with a decreasing measure on L1 states. *)

Section FORWARD_SIMU_EVENTUALLY_STAR.

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall wp s2, match_states wp s1 s2 ->
     (exists s2',
        (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ measure s1' < measure s1))%nat
        /\ match_states wp s1' s2')
  \/ (exists n s2',
        Plus L2 s2 t s2' /\ Eventually L1 n s1' (fun s1'' => match_states wp s1'' s2')).

Let order := (ltof _ measure).
Let index' := (nat * state1)%type.
Let order' := lex_ord Nat.lt order.
Let ms := fun wp i s1 s2 => snd i = s1 /\ Eventually L1 (fst i) s1 (fun s1'' => match_states wp s1'' s2).
Lemma forward_simulation_eventually_star: fsim_properties L1 L2 index' order' ms.
Proof.
  apply forward_simulation_eventually_star_wf.
- exact simulation.
Qed.

End FORWARD_SIMU_EVENTUALLY_STAR.

End FORWARD_SIMU_EVENTUALLY_SIMPL.


Section SIMULATION_SEQUENCES.
  
  Context L1 L2 index order match_states
    (S: fsim_properties L1 L2 index order match_states).
  
  Lemma simulation_star:
    forall s1 t s1', Star L1 s1 t s1' ->
        forall gw i s2, match_states gw i s1 s2 ->
        exists i', exists s2', Star L2 s2 t s2' /\
        match_states gw i' s1' s2'.
  Proof.
    induction 1; intros.
    eexists i; exists s2; repeat split; auto. apply star_refl.
    exploit fsim_simulation; eauto.
    intros (i' & s2' & A & B).
    exploit IHstar; eauto.
    intros (i'' & s2'' & Hx& C).
    exists i''; exists s2''; repeat split; auto.
    eapply star_trans; eauto.
    intuition auto. apply plus_star; auto.
  Qed.

  Lemma simulation_plus:
    forall s1 t s1', Plus L1 s1 t s1' ->
                forall gw i s2, match_states gw i s1 s2 ->
        exists i',
          ((exists s2', Plus L2 s2 t s2' /\ match_states gw i' s1' s2') \/
             clos_trans _ order i' i /\ t = E0 /\ match_states gw i' s1' s2).
  Proof.
    induction 1 using plus_ind2; intros.
    (* base case *)
    - exploit fsim_simulation'; eauto.
      intros (i' & A).
      exists i'. repeat split; eauto.
      destruct A.
      left; auto.
      right; intuition.
    (* inductive case *)
    - exploit fsim_simulation'; eauto.
      intros (i' & A).
      destruct A as [[s2' [A B]] | [A [B C]]].
      + exploit simulation_star. apply plus_star; eauto. eauto.
        intros (i'' & s2'' & P & Q).
        exists i''. repeat split.
        left; exists s2''; split; auto. eapply plus_star_trans; eauto.
      + exploit IHplus; eauto.
        intros (i'' & P).
        destruct P as [[s2'' [P Q]] | [P [Q R]]].
        * subst.
          exists i''. repeat split.
          left; exists s2''; auto.
        * subst.
          exists i''. repeat split.
          right; intuition auto.
          eapply t_trans; eauto. eapply t_step; eauto.
  Qed.
      
    End SIMULATION_SEQUENCES.
End FSIM.

  Arguments fsim_properties  {_ _} _ _ _ _  {_ _} L1 L2 index order match_states.

  Record fsim_components {li1 li2} (cc: callconv li1 li2) L1 L2 :=
    Forward_simulation {
        fsim_index: Type;
        fsim_order: fsim_index -> fsim_index -> Prop;
        fsim_match_states: _;

        fsim_skel: skel L1 = skel L2;
        fsim_lts se1 se2 w:
          GS.match_senv cc w se1 se2 ->
          Genv.valid_for (skel L1) se1 ->
          fsim_properties cc se1 se2 w (activate L1 se1) (activate L2 se2)
            fsim_index fsim_order (fsim_match_states se1 se2 w);
        fsim_order_wf:
          well_founded fsim_order;
      }.

  Arguments Forward_simulation {_ _ cc L1 L2 fsim_index}.

  Definition forward_simulation {li1 li2} cc L1 L2 :=
    inhabited (@fsim_components li1 li2 cc L1 L2).

End GS.

(** Transform the old callconv into new callconv with [world_unit], therefore new fsim is essentially the same as old one *)

Import GS.

Local Instance world_unit {T: Type} : World T :=
  {
    w_state := unit;
    w_lens := lens_unit;
    w_acci := fun _ _ => True;
    w_acce := fun _ _ => True;
  }.

Program Definition cc_unit_world {li1 li2} (cc: LanguageInterface.callconv li1 li2) : callconv li1 li2 :=
    {|
      ccworld := LanguageInterface.ccworld cc;
      ccworld_world := world_unit;
      match_senv w := LanguageInterface.match_senv cc w;
      match_query w := LanguageInterface.match_query cc w;
      match_reply w := LanguageInterface.match_reply cc w;
    |}.
Next Obligation.
  eapply LanguageInterface.match_senv_public_preserved; eauto.
Qed.
Next Obligation.
  eapply LanguageInterface.match_senv_valid_for; eauto.
Qed.

Coercion cc_unit_world : LanguageInterface.callconv >-> callconv.

