Require Export LogicalRelations.
Require Export List.
Require Export Globalenvs.
Require Export Events.
Require Export LanguageInterface.

Require Import Axioms.
Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import Memory.

Require Export CallconvBig.

(** Algebraic structures on calling conventions. *)

(** * Refinement and equivalence *)

(** ** Definition *)

(** The following relation asserts that the calling convention [cc] is
  refined by the calling convention [cc'], meaning that any
  [cc']-simulation is also a [cc]-simulation. *)

(** cc1: internal, i.e. injp ⋅ injp
    cc2: external, i.e. injp  *)


(** We are trying to define the ccref_outgoing with respect to the "living wp1, however,
    to show from [wp1 *-> (get w1)] we can construct w2 and show [wp2 *-> (get w2)], we still
    have to show that wp1 and wp2 are recording the same injected memories. Such relation has to be **defined**
    in some way "*)

Import GS. 
Definition ccref_outgoing {li1 li2} (cc1 cc2: callconv li1 li2) (match12 : gworld cc1 -> gworld cc2 -> Prop) :=
  forall wp1 wp2 w1 se1 se2 q1 q2,
    match_senv cc1 w1 se1 se2 ->
    match_query cc1 w1 q1 q2 ->
    wp1 *-> (get w1) ->
    match12 wp1 wp2 ->
    exists w2,
      wp2 *-> (get w2) /\
      match_senv cc2 w2 se1 se2 /\
      match_query cc2 w2 q1 q2 /\
      forall r1 r2 (wp2': gworld cc2),
        get w2 o-> wp2' ->
        match_reply cc2 (set w2 wp2') r1 r2 ->
        exists (wp1' : gworld cc1),
        get w1 o-> wp1' /\
        match_reply cc1 (set w1 wp1') r1 r2 /\
        match12 wp1' wp2'.            

Definition ccref_incoming {li1 li2} (cc1 cc2: callconv li1 li2) (match12 : gworld cc1 -> gworld cc2 -> Prop):=
  forall w2 se1 se2 q1 q2,
    match_senv cc2 w2 se1 se2 ->
    match_query cc2 w2 q1 q2 ->
    exists (w1: ccworld cc1) ,
      match_senv cc1 w1 se1 se2 /\
      match_query cc1 w1 q1 q2 /\
      match12 (get w1) (get w2) /\
        (forall r1 r2 wp1 wp2 wp1',
        match12 wp1 wp2 ->    
        get w1 o-> wp1' -> wp1 *-> wp1' ->
        match_reply cc1 (set w1 wp1') r1 r2 ->
        exists (wp2' : gworld cc2),
        (* match12 wp1' wp2' ->*)
        get w2 o-> wp2' /\ wp2 *-> wp2' /\
        match_reply cc2 (set w2 wp2') r1 r2).


Record cctrans {li1 li2} (cc1 cc2: callconv li1 li2) :=
  Callconv_Trans{
        match12 : gworld cc1 -> gworld cc2 -> Prop;
        big_step_incoming : ccref_incoming cc1 cc2 match12;
        big_step_outgoing : ccref_outgoing cc1 cc2 match12;
      }.

  
  Lemma open_fsim_cctrans {li1 li2: language_interface}:
  forall (cc1 cc2: callconv li1 li2) L1 L2,
    forward_simulation cc1 L1 L2 ->
    cctrans cc1 cc2 ->
    forward_simulation cc2 L1 L2.
  (*cc1 : injp @ injp cc2: injp*)
Proof.
  intros.
  destruct X as [match12 INCOM OUTGO].
  inv H.
  destruct X as [index order match_states SKEL PROP WF].
  constructor.
    set (ms se1 se2 (w2 : ccworld cc2) (wp2: gworld cc2) idx s1 s2 :=
         exists w1 (wp1 : gworld cc1),
           match_states se1 se2 w1 wp1 idx s1 s2 /\
             match_senv cc1 w1 se1 se2 /\
             match12 (get w1) (get w2) /\
             match12 wp1 wp2 /\
             (forall r1 r2 wp1 wp2 wp1', match12 wp1 wp2 -> (get w1) o-> wp1' -> wp1 *-> wp1' -> match_reply cc1 (set w1 wp1') r1 r2 ->
            exists (wp2' : gworld cc2), (get w2) o-> wp2' /\ wp2 *-> wp2' /\ match_reply cc2 (set w2 wp2') r1 r2)).
  eapply Forward_simulation with order ms; auto.
  intros se1 se2 wB' Hse' Hse1.
  split.
  - intros q1 q2 Hq'.
    destruct (INCOM wB' se1 se2 q1 q2) as (wB & Hse & Hq & Hr); auto.
    eapply fsim_match_valid_query; eauto.
  - intros q1 q2 s1 Hq' Hs1 Ho.
    destruct (INCOM wB' se1 se2 q1 q2) as (wB & Hse & Hq & Htrans & Hf); auto.
    edestruct @fsim_match_initial_states as (i & s2 & Hs2 & Hs); eauto.
    exists i, s2. split; auto. red. exists wB,(get wB). repeat apply conj; eauto.
  - intros gw i s1 s2 r1 (wB & gw' & Hs & Hse & HmB & Hm & Hf) Hr1.
    edestruct @fsim_match_final_states as (r2 & gw1 & Hr2 & ACCO1 & ACCI1 & Hr); eauto.
    exploit Hf; eauto. intros (gw2 &  ACCO2 & Hr2'). exists r2.
    exists gw2. intuition auto.
  - (*the most tricky part*)
    intros gw2 i s1 s2 qA1 (wB & gw1 & Hs & Hse & HmB & Hm & Hf) HqA1.
    edestruct @fsim_match_external as (wA & qA2 & Hacc1 & HqA2 & HqA & HseA & ?); eauto.
    edestruct OUTGO as (wA' & Hm' & HseA' & HqA' & Hr); eauto.
    exists wA', qA2. intuition auto.
    exploit Hr; eauto. intros (wp1' & ACCO1 & MR1 & Hm'').
    edestruct H as (i' & s2' & Hs2' & Hs'); eauto.
    exists i', s2'. split; auto. exists wB. exists wp1'.
    intuition auto.
  - intros s1 t s1' Hs1' gw2 i s2 (wB & gw1 & Hs & Hse & Hr').
   edestruct @fsim_simulation as (i' & s2' & Hs2' & Hs'); eauto.
    exists i', s2'. split; auto.
    econstructor; eauto.
Qed.






