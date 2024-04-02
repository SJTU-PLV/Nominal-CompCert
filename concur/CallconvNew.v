Require Import Coqlib.
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import CKLR.
Require Import LanguageInterface.
Require Import Smallstep.

Record callconvnew {li1 li2} :=
  mk_callconv {
    ccworld : Type;
    wacc : relation ccworld;
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
    wacc_preorder:
      PreOrder wacc;
      
    }.

Arguments callconvnew: clear implicits.

(**   *)
Section FSIM.

Context {li1 li2} (cc: callconvnew li1 li2).
Context (se1 se2: Genv.symtbl) (w: ccworld cc).
Context {state1 state2: Type}.

(** The general form of a forward simulation. *)

Record fsim_properties (L1: lts li1 li1 state1) (L2: lts li2 li2 state2) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> (ccworld cc) -> state1 -> state2 -> Prop) : Prop := {
    fsim_match_valid_query:
      forall q1 q2, match_query cc w q1 q2 ->
      valid_query L2 q2 = valid_query L1 q1;
    fsim_match_initial_states:
      forall q1 q2 s1, match_query cc w q1 q2 -> initial_state L1 q1 s1 ->
      exists i, exists w', exists s2, initial_state L2 q2 s2 /\ match_states i w' s1 s2 /\ wacc cc w w';
    fsim_match_final_states:
      forall i w s1 s2 r1, match_states i w s1 s2 -> final_state L1 s1 r1 ->
      exists r2 w', final_state L2 s2 r2 /\ match_reply cc w' r1 r2 /\ wacc cc w w';
    fsim_match_external:
      forall i w s1 s2 q1, match_states i w s1 s2 -> at_external L1 s1 q1 ->
      exists w' q2, at_external L2 s2 q2 /\ match_query cc w' q1 q2 /\ match_senv cc w' se1 se2 /\ wacc cc w w' /\
      forall r1 r2 s1' w'', match_reply cc w'' r1 r2 -> after_external L1 s1 r1 s1' -> wacc cc w' w'' ->
      exists i' s2' w''', after_external L2 s2 r2 s2' /\ match_states i' w''' s1' s2' /\ wacc cc w'' w''';
    fsim_simulation:
      forall s1 t s1', Step L1 s1 t s1' ->
      forall i s2 w, match_states i w s1 s2 ->
      exists i', exists s2', exists w',
         (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
      /\ match_states i' w' s1' s2' /\ wacc cc w w';
  }.

Arguments fsim_properties : clear implicits.

(** An alternate form of the simulation diagram *)
End FSIM.

Arguments fsim_properties {_ _} _ _ _ _ {_ _} L1 L2 index order match_states.

Record fsim_components {li1 li2} (cc: callconvnew li1 li2) L1 L2 :=
  Forward_simulation {
    fsim_index: Type;
    fsim_order: fsim_index -> fsim_index -> Prop;
    fsim_match_states: _;

    fsim_skel:
      skel L1 = skel L2;
    fsim_lts se1 se2 w:
      @match_senv li1 li2 cc w se1 se2 ->
      Genv.valid_for (skel L1) se1 ->
      fsim_properties cc se1 se2 w (activate L1 se1) (activate L2 se2)
        fsim_index fsim_order (fsim_match_states se1 se2);
    fsim_order_wf:
      well_founded fsim_order;
  }.

Arguments Forward_simulation {_ _ cc L1 L2 fsim_index}.

Definition forward_simulation {li1 li2} cc L1 L2 :=
  inhabited (@fsim_components li1 li2 cc L1 L2).

(** Definition of new CAinjp *)

Require Import Conventions Mach Asm.
Require Import InjectFootprint CA.

Inductive CAinjp_acc : cc_cainjp_world -> cc_cainjp_world -> Prop :=
  cainjp_acc_intro : forall w1 sig w2 rs1 rs2
    (INJPACC: injp_acc w1 w2)
    (CALLEESAVE: (forall r, is_callee_save r = true -> rs2 (preg_of r) = rs1 (preg_of r)))
    (RSPSAVE: rs2 # SP = rs1 # SP)
    (PCSAVE: rs2 # PC = rs1 # RA),
    CAinjp_acc (cajw w1 sig rs1) (cajw w2 sig rs2).  

Global Instance cainjp_acc_pero:
  PreOrder CAinjp_acc.
Proof.
  split.
  - intros [[j m1 m2 Hm] sig rs].
    constructor; eauto. reflexivity.
    
Inductive cc_c_asm_injp_mr : cc_cainjp_world -> c_reply -> reply li_asm -> Prop :=
  cc_c_asm_injp_mr_intro sg res  j' m' tm' Hm' (rs' :regset) :
     let tres := rs_getpair (map_rpair preg_of (loc_result sg)) rs' in
     Val.inject j' res tres ->
     (* uselss? (forall b ofs, loc_init_args (size_arguments sg) tsp b ofs ->
              loc_out_of_reach j m b ofs) -> *)
     cc_c_asm_injp_mr
       (cajw (injpw j' m' tm' Hm') sg rs')
       (cr res m')
       (rs', tm').

Program Definition cc_c_asm_injp_new : callconvnew li_c li_asm :=
  {|
    match_senv w := match_stbls injp (cajw_injp w);
    wacc := CAinjp_acc;
    match_query := cc_c_asm_injp_mq;
    match_reply := cc_c_asm_injp_mr
  |}.
Next Obligation.
  inv H. inv H1. eauto.
Qed.
Next Obligation.
  inv H.
  eapply Genv.valid_for_match in H2.
  apply H2. eauto.
Qed.
Next Obligation.
