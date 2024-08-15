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
                       forall r1 r2 s1' gw'', (get wA) o-> gw'' /\ match_reply cc (set wA gw'') r1 r2 ->
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











(** Definition of new CAinjp *)
Require Import Conventions Mach Asm.
Require Import InjectFootprint CA.

Definition get_injp := cajw_injp.

Definition set_injp (wa: cc_cainjp_world) (w : injp_world) :=
  match wa with cajw w' sig rs => cajw w sig rs end.

Program Instance lens_injp : Lens (cc_cainjp_world) injp_world :=
  {
    get := get_injp;
    set := set_injp;
  }.
Next Obligation. destruct t. reflexivity. Qed.
Next Obligation. destruct t. reflexivity. Qed.
Next Obligation. destruct t. reflexivity. Qed.

(* injp_acc *)

(** injp_acci: the internal transition: thread id remains the same, also no new threads introduced
               the private(unmapped or outofreach) memory of other threads are unchanged *)

(** free_preserved : The internal execution should keep the free operation of public memory. *)

(** Issue: the passes using [Mem.free_left_inject] *may* break this relation, we need to check them
    They are: Inliningproof, Separation, Serverproof (*should be ok*) *)

(** Note : the injp_acce as rely condition is used to protect [local] (i.e. blocks of this thread) and [private] (i.e. unmapped or outofreach) memory

    The [injp_acci] is introduced as an guarantee condition for *switch* provided by big_step internal accessibility. Therefore, it can protect only [external] memory. Such restriction applies to not only [Mem.unchanged_on], but also other properties.


 *)
(*
Definition inject_separated_external (f f' : meminj) (m1 m2: mem) :=
  forall b1 b2 delta, f b1 = None -> f' b1 = Some (b2, delta) -> fst b1 <> Mem.tid (Mem.support m1) ->
                 ~ Mem.valid_block m1 b1 /\ ~ Mem.valid_block m2 b2.

Definition inject_separated_internal (f f' : meminj) (m1 m2: mem) :=
  forall b1 b2 delta, f b1 = None -> f' b1 = Some (b2, delta) -> fst b1 = Mem.tid (Mem.support m1) ->
                 ~ Mem.valid_block m1 b1 /\ ~ Mem.valid_block m2 b2.
*)

Lemma inject_separated_imply_e: forall f f' m1 m2,
    inject_separated f f' m1 m2 -> inject_separated_external f f' m1 m2.
Proof.
  intros. red. intros. eapply H; eauto.
Qed.

Lemma inject_separated_imply_i: forall f f' m1 m2,
    inject_separated f f' m1 m2 -> inject_separated_internal f f' m1 m2.
Proof.
  intros. red. intros. eapply H; eauto.
Qed.

Hint Resolve inject_separated_imply_e : core.
Hint Resolve inject_separated_imply_i : core.

Inductive injp_acci : relation injp_world :=
    injp_acci_intro : forall (f : meminj) (m1 m2 : mem) (Hm : Mem.inject f m1 m2) (f' : meminj) 
                        (m1' m2' : mem) (Hm' : Mem.inject f' m1' m2')
                     (Hnb1: new_block_local m1 m1')
                     (Hnb2:new_block_local m2 m2'),
                     Mem.ro_unchanged m1 m1' ->
                     Mem.ro_unchanged m2 m2' ->
                     injp_max_perm_decrease m1 m1' ->
                     injp_max_perm_decrease m2 m2' ->
                     Mem.unchanged_on_i (loc_unmapped f) m1 m1' ->
                     Mem.unchanged_on_i (loc_out_of_reach f m1) m2 m2' ->
                     inject_incr f f' ->
                     inject_separated_external f f' m1 m2 ->
                     inject_separated_noglobal f f' ->
                     free_preserved f m1 m1' m2' ->
                     injp_acci (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').

(** injp_acce: the transition for external calls: when the current thread takes the control again (thread id is the same), new threads may be introduced
               the private memory of the current thread is unchanged by other threads *)
Inductive injp_acce :  relation injp_world :=
    injp_acce_intro : forall (f : meminj) (m1 m2 : mem) (Hm : Mem.inject f m1 m2) (f' : meminj) 
                       (m1' m2' : mem) (Hm' : Mem.inject f' m1' m2'),
                     Mem.ro_unchanged m1 m1' ->
                     Mem.ro_unchanged m2 m2' ->
                     injp_max_perm_decrease m1 m1' ->
                     injp_max_perm_decrease m2 m2' ->
                     Mem.unchanged_on_e (loc_unmapped f) m1 m1' ->
                     Mem.unchanged_on_e (loc_out_of_reach f m1) m2 m2' ->
                     inject_incr f f' ->
                     inject_separated_internal f f' m1 m2 ->
                     inject_separated_noglobal f f' ->
                     injp_acce (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').

Record unchanged_on_g (P : block -> Z -> Prop) (m_before m_after : mem) : Prop :=
  mk_unchanged_on_g
    { unchanged_on_thread_g : (Mem.next_tid (Mem.support m_before) <= Mem.next_tid (Mem.support m_after))%nat
                              /\ Mem.tid (Mem.support m_before) <> Mem.tid (Mem.support m_after);
      unchanged_on_g' : Mem.unchanged_on (Mem.thread_internal_P P m_before) m_before m_after }.

(** injp_accg: the transition for one thread [t] to another (usually the current running) thread,
               New threads may be introduced, the thread [t] has switched out and never runs again yet, thus its
               private memory is unchanged *)
Inductive injp_accg : relation injp_world :=
    injp_accg_intro : forall (f : meminj) (m1 m2 : mem) (Hm : Mem.inject f m1 m2) (f' : meminj) 
                       (m1' m2' : mem) (Hm' : Mem.inject f' m1' m2'),
                     Mem.ro_unchanged m1 m1' ->
                     Mem.ro_unchanged m2 m2' ->
                     injp_max_perm_decrease m1 m1' ->
                     injp_max_perm_decrease m2 m2' ->
                     unchanged_on_g (loc_unmapped f) m1 m1' ->
                     unchanged_on_g (loc_out_of_reach f m1) m2 m2' ->
                     inject_incr f f' ->
                     inject_separated_internal f f' m1 m2 ->
                     inject_separated_noglobal f f' ->
                     injp_accg (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').


Instance injp_acci_preo : PreOrder injp_acci.
Proof.
  split.
  - intros [f m1 m2].
    constructor.
    + red. intros. congruence.
    + red. intros. congruence.
    + red. eauto.
    + red. eauto.
    + red. eauto.
    + red. eauto.
    + split. eauto. apply Mem.unchanged_on_refl.
    + split. eauto. apply Mem.unchanged_on_refl.
    + apply inject_incr_refl.
    + intros b ofs. congruence.
    + red. intros. congruence.
    + red. intros. congruence.
  - intros w1 w2 w3 H12 H23.
    destruct H12 as [f m1 m2 Hm f' m1' m2' Hm' Hb1 Hb2 Hr1 Hr2 Hp1 Hp2 [S1 H1] [S2 H2] Hi Hs1 Hs2 Hf].
    inversion H23 as [? ? ? ? f'' m1'' m2'' Hm'' Hb1' Hb2' Hr1' Hr2' Hp1' Hp2' [S1' H1'] [S2' H2'] Hi' Hs1' Hs2' Hf']; subst.
    constructor.
    + red. intros. destruct (Mem.sup_dec b (Mem.support m1')).
      exploit Hb1; eauto. exploit Hb1'; eauto.
      inv S1. congruence.
    + red. intros. destruct (Mem.sup_dec b (Mem.support m2')).
      exploit Hb2; eauto. exploit Hb2'; eauto.
      inv S2. congruence.
    + red. intros. eapply Hr1; eauto. eapply Hr1'; eauto.
      inversion H1. apply unchanged_on_support; eauto.
      intros. intro. eapply H3; eauto.
    + red. intros. eapply Hr2; eauto. eapply Hr2'; eauto.
      inversion H2. apply unchanged_on_support; eauto.
      intros. intro. eapply H3; eauto.
    + intros b ofs p Hb ?.
      eapply Hp1, Hp1'; eauto using Mem.valid_block_unchanged_on.
    + intros b ofs p Hb ?.
      eapply Hp2, Hp2'; eauto using Mem.valid_block_unchanged_on.
    + split. eauto.
      eapply mem_unchanged_on_trans_implies_valid; eauto.
      unfold loc_unmapped, Mem.thread_external_P. simpl.
      intros b1 _ [Hb Hb0'] Hb1''. split.
      destruct (f' b1) as [[b2 delta] | ] eqn:Hb'; eauto.
      edestruct Hs1; eauto. contradiction. auto.
      inv S1. congruence.
    + split. eauto.
      eapply mem_unchanged_on_trans_implies_valid; eauto.
      unfold loc_out_of_reach, Mem.thread_external_P. simpl.
      intros b2 ofs2 [Hbb2 Hbb2'] Hv. split. intros b1 delta Hb'.
      destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
            by (eapply Hi in Hb; split; congruence); subst.
        specialize (Hbb2 b1 delta Hb). intro. apply Hbb2.
        eapply Hp1; eauto. eapply Mem.valid_block_inject_1; eauto.
      * edestruct Hs1; eauto.
        inv Hm. inv mi_thread. inv Hms. rewrite H0.
        inversion Hm'. inv mi_thread. erewrite Hjs0; eauto.
      * inv S2. congruence.
    + eapply inject_incr_trans; eauto.
    + intros b1 b2 delta Hb Hb'' Htid.
      destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply Hi' in Hb'; split; congruence); subst.
        eapply Hs1; eauto.
      * edestruct Hs1'; eauto. inv S1. congruence.
        intuition eauto using Mem.valid_block_unchanged_on.
    + intros b1 b2 delta Hb Hb''.
      destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply Hi' in Hb'; split; congruence); subst.
        eapply Hs2; eauto.
      * edestruct Hs2'; eauto.
    + red. intros.
      destruct (Mem.perm_dec m1' b1 ofs1 Max Nonempty).
      * eapply Hf'; eauto. inv S1. congruence.
      * red in Hp2'. intro. apply Hp2' in H5.
        eapply Hf; eauto. inv H2. apply unchanged_on_support.
        eapply Mem.valid_block_inject_2; eauto.
Qed.

Instance injp_acce_preo : PreOrder injp_acce.
Proof.
  split.
  - intros [f m1 m2].
    constructor.
    + red. intros. congruence.
    + red. intros. congruence.
    + red. eauto.
    + red. eauto.
    + split. split; eauto. apply Mem.unchanged_on_refl.
    + split. split; eauto. apply Mem.unchanged_on_refl.
    + apply inject_incr_refl.
    + intros b ofs. congruence.
    + red. intros. congruence.
  - intros w1 w2 w3 H12 H23.
    destruct H12 as [f m1 m2 Hm f' m1' m2' Hm' Hr1 Hr2 Hp1 Hp2 [S1 H1] [S2 H2] Hi Hs1 Hs2].
    inversion H23 as [? ? ? ? f'' m1'' m2'' Hm'' Hr1' Hr2' Hp1' Hp2' [S1' H1'] [S2' H2'] Hi' Hs1' Hs2']; subst.
    constructor.
    + red. intros. eapply Hr1; eauto. eapply Hr1'; eauto.
      inversion H1. apply unchanged_on_support; eauto.
      intros. intro. eapply H3; eauto.
    + red. intros. eapply Hr2; eauto. eapply Hr2'; eauto.
      inversion H2. apply unchanged_on_support; eauto.
      intros. intro. eapply H3; eauto.
    + intros b ofs p Hb ?.
      eapply Hp1, Hp1'; eauto using Mem.valid_block_unchanged_on.
    + intros b ofs p Hb ?.
      eapply Hp2, Hp2'; eauto using Mem.valid_block_unchanged_on.
    + split. inv S1. inv S1'. split. lia. congruence.
      eapply mem_unchanged_on_trans_implies_valid; eauto.
      unfold loc_unmapped, Mem.thread_internal_P. simpl.
      intros b1 _ [Hb Hb0'] Hb1''. split.
      destruct (f' b1) as [[b2 delta] | ] eqn:Hb'; eauto.
      edestruct Hs1; eauto. contradiction. auto.
      inv S1. congruence.
    + split. inv S2. inv S2'. split. lia. congruence.
      eapply mem_unchanged_on_trans_implies_valid; eauto.
      unfold loc_out_of_reach, Mem.thread_external_P. simpl.
      intros b2 ofs2 [Hbb2 Hbb2'] Hv. split. intros b1 delta Hb'.
      destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
            by (eapply Hi in Hb; split; congruence); subst.
        specialize (Hbb2 b1 delta Hb). intro. apply Hbb2.
        eapply Hp1; eauto. eapply Mem.valid_block_inject_1; eauto.
      * edestruct Hs1; eauto.
        inv Hm. inv mi_thread. inv Hms. rewrite H0.
        inversion Hm'. inv mi_thread. erewrite Hjs0; eauto.
      * inv S2. congruence.
    + eapply inject_incr_trans; eauto.
    + intros b1 b2 delta Hb Hb'' HT.
      destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply Hi' in Hb'; split; congruence); subst.
        eapply Hs1; eauto.
      * edestruct Hs1'; eauto. inv S1. congruence.
        intuition eauto using Mem.valid_block_unchanged_on.
    + intros b1 b2 delta Hb Hb''.
      destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply Hi' in Hb'; split; congruence); subst.
        eapply Hs2; eauto.
      * edestruct Hs2'; eauto.
Qed.

(*
Instance injp_accg_refl : Reflexive injp_accg.
Proof.
  intros [f m1 m2].
    constructor; auto.
    + red. eauto.
    + red. eauto.
    + split. auto. apply Mem.unchanged_on_refl.
    + apply Mem.unchanged_on_refl.
    + intros b ofs. congruence.
Qed.
*)

Program Instance CAworld : World cc_cainjp_world :=
    {
      w_state := injp_world;
      w_lens := lens_injp;
      w_acci := injp_acci;
      w_acce := injp_acce;
      w_acci_trans := injp_acci_preo;
    }.
     
Inductive cc_c_asm_injp_mr : cc_cainjp_world -> c_reply -> reply li_asm -> Prop :=
  cc_c_asm_injp_mr_intro sg res  j' m' tm' Hm' (rs rs' :regset) :
     let tres := rs_getpair (map_rpair preg_of (loc_result sg)) rs' in
     Val.inject j' res tres ->
     (forall r, is_callee_save r = true -> rs' (preg_of r) = rs (preg_of r)) ->
     (*(forall b ofs, loc_init_args (size_arguments sg) tsp b ofs ->
              loc_out_of_reach j m b ofs) -> *)
     rs'#SP = rs#SP -> rs'#PC = rs#RA ->
     cc_c_asm_injp_mr
       (cajw (injpw j' m' tm' Hm') sg rs)
       (cr res m')
       (rs', tm').

Program Definition cc_c_asm_injp_new : GS.callconv li_c li_asm :=
  {|
    GS.ccworld := cc_cainjp_world;
    GS.ccworld_world := CAworld;
    GS.match_senv w := match_stbls injp (cajw_injp w);
    GS.match_query := cc_c_asm_injp_mq;
    GS.match_reply := cc_c_asm_injp_mr
  |}.
Next Obligation.
  inv H. inv H1. eauto.
Qed.
Next Obligation.
  inv H.
  eapply Genv.valid_for_match in H2.
  apply H2. eauto.
Qed.


(** The properties about the preservation of injp accessibility
    by corresponding memory operations on related memories. *)

Lemma unchanged_on_tl_i : forall m P m',
    Mem.unchanged_on_tl P m m' ->
    Mem.unchanged_on_i P m m'.
Proof.
  intros. inv H. split. auto. eapply Mem.unchanged_on_implies; eauto.
  intros. apply H.
Qed.

Lemma unchanged_on_tl_e : forall m P m',
    Mem.unchanged_on_tl P m m' ->
    Mem.unchanged_on_e P m m'.
Proof.
  intros. inv H. split. inv unchanged_on_thread_tl. split. lia. auto.
  eapply Mem.unchanged_on_implies; eauto.
  intros. apply H.
Qed.

(* thread_local, the local accessibility for internel transitions and builtin functions
   which only change public memories  *)
Inductive injp_acc_tl : relation injp_world :=
    injp_acc_tl_intro : forall (f : meminj) (m1 m2 : mem) (Hm : Mem.inject f m1 m2) (f' : meminj) 
                        (m1' m2' : mem) (Hm' : Mem.inject f' m1' m2')
                     (Hnb1: new_block_local m1 m1')
                     (Hnb2:new_block_local m2 m2'),
                     Mem.ro_unchanged m1 m1' ->
                     Mem.ro_unchanged m2 m2' ->
                      injp_max_perm_decrease m1 m1' ->
                     injp_max_perm_decrease m2 m2' ->
                     Mem.unchanged_on_tl (loc_unmapped f) m1 m1' ->
                     Mem.unchanged_on_tl (loc_out_of_reach f m1) m2 m2' ->
                     inject_incr f f' ->
                     inject_separated f f' m1 m2 ->
                     inject_separated_noglobal f f' ->
                     free_preserved f m1 m1' m2' ->
                     injp_acc_tl (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').

Lemma injp_acc_tl_i : forall w1 w2, injp_acc_tl w1 w2 -> injp_acci w1 w2.
Proof.
  intros. inv H. constructor; eauto using unchanged_on_tl_i.
Qed.

Lemma injp_acc_tl_e : forall w1 w2, injp_acc_tl w1 w2 -> injp_acce w1 w2.
Proof.
  intros. inv H. constructor; eauto using unchanged_on_tl_e.
Qed.

Lemma injp_acc_tl_alloc: forall f f' m1 m2 b1 b2 lo1 hi1 lo2 hi2 m1' m2' Hm Hm',
    Mem.alloc m1 lo1 hi1 = (m1',b1) ->
    Mem.alloc m2 lo2 hi2 = (m2',b2) ->
    inject_incr f f' ->
    f' b1 = Some (b2, 0) ->
    (forall b, b<> b1 -> f' b = f b) ->
    injp_acc_tl (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').
Proof.
  intros. constructor.
  - red. intros.
    exploit Mem.valid_block_alloc_inv. apply H. eauto. intros [|]. subst.
    apply Mem.alloc_result in H. subst. reflexivity. congruence.
  - red. intros.
    exploit Mem.valid_block_alloc_inv. apply H0. eauto. intros [|]. subst.
    apply Mem.alloc_result in H0. subst. reflexivity. congruence.
  - eauto using Mem.ro_unchanged_alloc.
  - eauto using Mem.ro_unchanged_alloc.
  - intros b ofs p Hb Hp.
    eapply Mem.perm_alloc_inv in Hp; eauto.
    destruct (eq_block b b1); eauto; subst.
    eelim (Mem.fresh_block_alloc m1); eauto.
  - intros b ofs p Hb Hp.
    eapply Mem.perm_alloc_inv in Hp; eauto.
    destruct (eq_block b b2); eauto; subst.
    eelim (Mem.fresh_block_alloc m2); eauto.
  - eapply Mem.alloc_unchanged_on_tl; eauto.
  - eapply Mem.alloc_unchanged_on_tl; eauto.
  - assumption.
  - red. intros b b' delta Hb Hb'.
    assert (b = b1).
    {
      destruct (eq_block b b1); eauto.
      rewrite H3 in Hb'; eauto.
      congruence.
    }
    assert (b' = b2) by congruence.
    subst.
    split; eauto using Mem.fresh_block_alloc.
  - red. intros.
    destruct (eq_block b0 b1). subst.
    split.
    eapply Mem.alloc_block_noglobal; eauto.
    rewrite H2 in H5. inv H5.
    eapply Mem.alloc_block_noglobal; eauto.
    erewrite H3 in H5. congruence. auto.
  - red. intros. exfalso. apply H7. eauto with mem.
Qed.


Lemma injp_acc_tl_free: forall f m1 m2 b1 b2 delta lo1 sz m1' m2' Hm Hm',
    Mem.free m1 b1 lo1 (lo1 + sz) = Some m1' ->
    Mem.free m2 b2 (lo1 + delta) (lo1 + sz + delta) = Some m2' ->
    f b1 = Some (b2, delta) ->
    injp_acc_tl (injpw f m1 m2 Hm) (injpw f m1' m2' Hm').
Proof.
  intros. constructor.
  - red. intros. unfold Mem.valid_block in *.
    erewrite Mem.support_free in H3; eauto. congruence.
  - red. intros. unfold Mem.valid_block in *.
    erewrite Mem.support_free in H3; eauto. congruence.
  - eauto using Mem.ro_unchanged_free.
  - eauto using Mem.ro_unchanged_free.
  - red. eauto using Mem.perm_free_3.
  - red. eauto using Mem.perm_free_3.
  - eapply Mem.free_unchanged_on_tl; eauto.
    intros. intro. congruence.
  - eapply Mem.free_unchanged_on_tl; eauto.
    unfold loc_out_of_reach.
    intros ofs Hofs H'.
    eelim H'; eauto.
    eapply Mem.perm_cur_max.
    eapply Mem.perm_implies; [ | eapply perm_any_N].
    eapply Mem.free_range_perm; eauto.
    extlia.
  - apply inject_incr_refl.
  - apply inject_separated_refl.
  - red. intros. congruence.
  - red. intros. 
    eapply Mem.perm_free_inv in H as Hd; eauto. destruct Hd.
    + destruct H6. subst. rewrite H1 in H2. inv H2.
      eapply Mem.perm_free_2; eauto. lia.
    + congruence.
Qed.

Lemma injp_acc_tl_free_0: forall f m1 m2 b1 b2 delta sz m1' m2' Hm Hm' sz',
    Mem.free m1 b1 0 sz = Some m1' ->
    Mem.free m2 b2 delta sz' = Some m2' ->
    f b1 = Some (b2, delta) ->
    sz' = sz + delta ->
    injp_acc_tl (injpw f m1 m2 Hm) (injpw f m1' m2' Hm').
Proof.
  intros. exploit injp_acc_tl_free.
  replace sz with (0 + sz) in H by lia. eauto.
  rewrite !Z.add_0_l. subst sz'. eauto. eauto.
  intro. apply H3.
Qed.

Lemma injp_acc_tl_store : forall f chunk v1 v2 b1 b2 ofs1 delta m1 m2 m1' m2' Hm Hm',
    Mem.store chunk m1 b1 ofs1 v1 = Some m1' ->
    Mem.store chunk m2 b2 (ofs1 + delta) v2 = Some m2' ->
    (* Val.inject f v1 v2 -> *)
    f b1 = Some (b2,delta) ->
    injp_acc_tl (injpw f m1 m2 Hm) (injpw f m1' m2' Hm').
Proof.
  intros. constructor.
  - red. intros. unfold Mem.valid_block in *.
    erewrite Mem.support_store in H3; eauto. congruence.
  - red. intros. unfold Mem.valid_block in *.
    erewrite Mem.support_store in H3; eauto. congruence.
  - eauto using Mem.ro_unchanged_store.
  - eauto using Mem.ro_unchanged_store.
  - red. eauto using Mem.perm_store_2.
  - red. eauto using Mem.perm_store_2.
  - eapply Mem.store_unchanged_on_tl; eauto.
    unfold loc_unmapped. congruence.
  - eapply Mem.store_unchanged_on_tl; eauto.
    unfold loc_out_of_reach.
    intros ofs Hofs H'.
    eelim H'; eauto.
    edestruct (Mem.store_valid_access_3 chunk m1); eauto.
    eapply Mem.perm_cur_max.
    eapply Mem.perm_implies; [ | eapply perm_any_N].
    eapply H2; eauto.
    extlia.
  - apply inject_incr_refl.
  - apply inject_separated_refl.
  - red. intros. congruence.
  - red. intros. exfalso. apply H5. eauto with mem.
Qed.

Lemma injp_acc_tl_storev : forall f chunk v1 v2 a1 a2 m1 m2 m1' m2' Hm Hm',
    Mem.storev chunk m1 a1 v1 = Some m1' ->
    Mem.storev chunk m2 a2 v2 = Some m2' ->
    Val.inject f a1 a2 -> (* Val.inject f v1 v2 -> *)
    injp_acc_tl (injpw f m1 m2 Hm) (injpw f m1' m2' Hm').
Proof.
  intros. unfold Mem.storev in *. destruct a1; try congruence.
  inv H1.
  erewrite Mem.address_inject in H0. 2: apply Hm. 3: eauto.
  eapply injp_acc_tl_store; eauto.
  apply Mem.store_valid_access_3 in H.
  destruct H as [A B].
  apply A. destruct chunk; simpl; lia.
Qed.

Lemma injp_acc_tl_storebytes' : forall f b1 b2 ofs1 delta vs1 vs2 m1 m2 m1' m2' Hm Hm',
    Mem.storebytes m1 b1 ofs1 vs1 = Some m1' ->
    Mem.storebytes m2 b2 (ofs1 + delta) vs2 = Some m2' ->
    length vs1 = length vs2 ->
    f b1 = Some (b2, delta) ->
    injp_acc_tl (injpw f m1 m2 Hm) (injpw f m1' m2' Hm').
Proof.
  intros. constructor.
  - red. intros. unfold Mem.valid_block in *.
    erewrite Mem.support_storebytes in H4; eauto. congruence.
  - red. intros. unfold Mem.valid_block in *.
    erewrite Mem.support_storebytes in H4; eauto. congruence.
  - eauto using Mem.ro_unchanged_storebytes.
  - eauto using Mem.ro_unchanged_storebytes.
  - red. eauto using Mem.perm_storebytes_2.
  - red. eauto using Mem.perm_storebytes_2.
  - eapply Mem.storebytes_unchanged_on_tl; eauto.
    unfold loc_unmapped. congruence.
  - eapply Mem.storebytes_unchanged_on_tl; eauto.
    unfold loc_out_of_reach.
    intros ofs Hofs HH. 
    eelim HH; eauto.
    eapply Mem.perm_cur_max.
    eapply Mem.perm_implies; [ | eapply perm_any_N].
    eapply Mem.storebytes_range_perm; eauto.
    extlia.
  - apply inject_incr_refl.
  - apply inject_separated_refl.
  - red. intros. congruence.
  - red. intros. exfalso. apply H6. eauto with mem.
Qed.

Lemma injp_acc_tl_storebytes : forall f b1 b2 ofs1 ofs2 vs1 vs2 m1 m2 m1' m2' Hm Hm',
    Mem.storebytes m1 b1 (Ptrofs.unsigned ofs1) vs1 = Some m1' ->
    Mem.storebytes m2 b2 (Ptrofs.unsigned ofs2) vs2 = Some m2' ->
    length vs1 = length vs2 ->
    Val.inject f (Vptr b1 ofs1) (Vptr b2 ofs2) ->
    injp_acc_tl (injpw f m1 m2 Hm) (injpw f m1' m2' Hm').
Proof.
  intros. destruct vs1.
  - destruct vs2; inv H1.
    constructor.
    + red. intros. unfold Mem.valid_block in *.
    erewrite Mem.support_storebytes in H3; eauto. congruence.
    + red. intros. unfold Mem.valid_block in *.
    erewrite Mem.support_storebytes in H3; eauto. congruence.
    + eauto using Mem.ro_unchanged_storebytes.
    + eauto using Mem.ro_unchanged_storebytes.
    + red. eauto using Mem.perm_storebytes_2.
    + red. eauto using Mem.perm_storebytes_2.
    + eapply Mem.storebytes_unchanged_on_tl; eauto.
      unfold loc_unmapped. inv H2. congruence.
    + eapply Mem.storebytes_unchanged_on_tl; eauto.
      simpl. intro. extlia.
    + apply inject_incr_refl.
    + apply inject_separated_refl.
    + red. intros. congruence.
    + red. intros. exfalso. apply H5. eauto with mem.
  - inv H2.
    eapply injp_acc_tl_storebytes'; eauto.
    erewrite <- Mem.address_inject; eauto.
    eapply Mem.perm_storebytes_1; eauto.
    apply Mem.storebytes_range_perm in H.
    eapply H. simpl. lia.
Qed.


(* The internal changes which may change the [private] regions which are not in the
   initial world *)

(** able to change: 1. all public 
                    2. private : only local & not in initial 

    unchanged : private & ( other threads \/ in intial)
*)

(** This should indicate acci, which says that private & other threads are unchanged *)
Inductive injp_acc_small (w0: injp_world) : relation injp_world :=
    injp_acc_small_intro : forall (f : meminj) (m1 m2 : mem) (Hm : Mem.inject f m1 m2) (f' : meminj) 
                        (m1' m2' : mem) (Hm' : Mem.inject f' m1' m2') j m10 m20 Hm0
                     (Hnb1: new_block_local m1 m1')
                     (Hnb2:new_block_local m2 m2'),
                     w0 = injpw j m10 m20 Hm0 ->
                     Mem.ro_unchanged m1 m1' ->
                     Mem.ro_unchanged m2 m2' ->
                      injp_max_perm_decrease m1 m1' ->
                     injp_max_perm_decrease m2 m2' ->
                     Mem.unchanged_on_tl (fun b ofs => loc_unmapped f b ofs /\
                                        (fst b <> Mem.tid (Mem.support m1) \/ Mem.valid_block m10 b)) m1 m1' ->
                     Mem.unchanged_on_tl (fun b ofs => loc_out_of_reach f m1 b ofs /\
                                        (fst b <> Mem.tid (Mem.support m1) \/ Mem.valid_block m20 b)) m2 m2' ->
                     inject_incr f f' ->
                     inject_separated_external f f' m1 m2 ->
                     inject_separated_noglobal f f' ->
                     inject_separated f f' m10 m20 ->
                     free_preserved f m1 m1' m2' ->
                     injp_acc_small w0 (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').

Lemma injp_acce_small : forall w0 w1 w2,
    injp_acce w0 w1 -> injp_acc_small w0 w1 w2 -> injp_acce w0 w2.
Proof.
  intros.
  inv H. inv H0. inv H12.
  destruct H5 as [[S51 S52] H5].
  destruct H6 as [[S61 S62] H6].
  destruct H17 as [[S171 S172] H17].
  destruct H18 as [[S181 S182] H18].
  econstructor; eauto.
  - eapply Mem.ro_unchanged_trans; eauto. inv H5. auto.
  - eapply Mem.ro_unchanged_trans; eauto. inv H6. auto.
  - red. intros. eapply H3; eauto. eapply H15; eauto. inv H5.
    apply unchanged_on_support. auto.
  - red. intros. eapply H4; eauto. eapply H16; eauto. inv H6.
    apply unchanged_on_support. auto.
  - split. constructor. lia. congruence.
    eapply mem_unchanged_on_trans_implies_valid; eauto.
    intros. simpl. destruct H. split; auto. red in H.
    destruct (f' b) as [[? ?]|] eqn: Hf'.
    exploit H8; eauto. intros [X Y]. congruence.
    auto.
  - split. constructor. lia. congruence.
    eapply mem_unchanged_on_trans_implies_valid; eauto.
    intros. simpl. destruct H. split; auto. red in H.
    red. intros. destruct (j b0) as [[b' d']|] eqn:Hj.
    apply H7 in Hj as Heq. rewrite H11 in Heq. inv Heq.
    intro. eapply H; eauto. eapply H3; eauto using Mem.valid_block_inject_1.
    exploit H8; eauto. inv Hm. inv mi_thread. inv Hms.
    rewrite H22. inversion Hm'. inv mi_thread.
    erewrite Hjs0; eauto.
    intros [X Y]. congruence.
  - eapply inject_incr_trans; eauto.
  - intros b1 b2 delta Hb Hb'' Ht.
      destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply H19 in Hb'; split; congruence); subst.
        eapply H8; eauto.
      * eauto.
  - intros b1 b2 delta Hb Hb''.
      destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply H19 in Hb'; split; congruence); subst.
        eapply H9; eauto.
      * eapply H21; eauto.
Qed.

Lemma injp_acc_small_acci : forall w0 w1 w2,
    injp_acc_small w0 w1 w2 ->
    injp_acci w1 w2.
Proof.
  intros. inv H. constructor; eauto.
  - destruct H5. split; auto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. destruct H. split. auto. left. auto.
  - destruct H6. split; auto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. destruct H. split. auto. left. inv Hm.
    inv mi_thread. inv Hms. congruence.
Qed.

Lemma inject_tid: forall j m1 m2,
    Mem.inject j m1 m2 -> Mem.tid (Mem.support m1) = Mem.tid (Mem.support m2).
Proof.
  intros. inv H. inv mi_thread. inv Hms. auto.
Qed.

Lemma inject_block_tid : forall j m1 m2 b1 b2 d,
    Mem.inject j m1 m2 ->
    j b1 = Some (b2, d) ->
    fst b1 = fst b2.
Proof.
  intros. inv H. inv mi_thread. eapply Hjs; eauto.
Qed.
