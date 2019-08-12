Require Import List.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Smallstep.
Require Import Linking.

(** NB: we assume that all components are deterministic and that their
  domains are disjoint. *)

Parameter (valid_query : forall {li}, Smallstep.open_sem li li -> Senv.t -> query li -> Prop).

Section LINK.
  Context {li} (L1 L2 : Smallstep.open_sem li li).
  Notation L i := (if i:bool then L1 else L2).

  Section WITH_SE.
    Context (se: Senv.t).

    Variant frame := st (i: bool) (q: query li) (s: Smallstep.state (L i se q)).
    Notation state := (list frame).

    Inductive step: state -> trace -> state -> Prop :=
      | step_internal i q s t s' k :
          Step (L i se q) s t s' ->
          step (st i q s :: k) t (st i q s' :: k)
      | step_push i q j s qx s' k :
          Smallstep.at_external (L i se q) s qx ->
          valid_query (L j) se qx ->
          Smallstep.initial_state (L j se qx) s' ->
          step (st i q s :: k) E0 (st j qx s' :: st i q s :: k)
      | step_pop i qx j q s sk r s' k :
          Smallstep.final_state (L i se qx) s r ->
          Smallstep.after_external (L j se q) sk r s' ->
          step (st i qx s :: st j q sk :: k) E0 (st j q s' :: k).

    Inductive initial_state (q: query li): state -> Prop :=
      | initial_state_intro i s :
          Smallstep.initial_state (L i se q) s ->
          initial_state q (st i q s :: nil).

    Inductive at_external: state -> query li -> Prop :=
      | at_external_intro i q s qx k:
          Smallstep.at_external (L i se q) s qx ->
          (forall j, ~ valid_query (L j) se qx) ->
          at_external (st i q s :: k) qx.

    Inductive after_external: state -> reply li -> state -> Prop :=
      | after_external_intro i q s r s' k:
          Smallstep.after_external (L i se q) s r s' ->
          after_external (st i q s :: k) r (st i q s' :: k).

    Inductive final_state: state -> reply li -> Prop :=
      | final_state_intro i q s r :
          Smallstep.final_state (L i se q) s r ->
          final_state (st i q s :: nil) r.

  End WITH_SE.

  Definition semantics: option (open_sem li li) :=
    option_map
      (fun sk =>
        {|
          activate se q :=
            {|
              Smallstep.step ge := step se;
              Smallstep.initial_state := initial_state se q;
              Smallstep.at_external := at_external se;
              Smallstep.after_external := after_external se;
              Smallstep.final_state := final_state se;
              Smallstep.globalenv := tt;
            |};
          skel := sk;
        |})
      (link (skel L1) (skel L2)).

End LINK.

Instance Linker_open_sem li: Linker (open_sem li li) :=
  {
    link L1 L2 := semantics L1 L2;
    linkorder := open_fsim cc_id cc_id;
  }.
(* Need to prove: identity and composition for fsim,
  fsim between component and linked program. *)    
Admitted.
