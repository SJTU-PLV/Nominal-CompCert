Require Import List.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep_.
Require Import LanguageInterface_.
Require Import Ctypes.
Require Import Cop.
Require Import Clight.
Require Import Linking.

(* First, we override some definitions in the Clight semantics *)

Inductive after_external: state -> c_reply -> state -> Prop :=
  | after_external_intro vf vargs k m vres m':
      after_external
        (Callstate vf vargs k m)
        (cr vres m')
        (Returnstate vres k m').

Inductive final_state: state -> c_reply -> Prop :=
  | final_state_intro: forall r m,
      final_state
        (Returnstate r Kstop m)
        (cr r m).

Inductive initial_state (ge: genv): c_query -> state -> Prop :=
  | initial_state_intro: forall vf f targs tres tcc vargs m name,
      Genv.find_funct ge vf = Some (Internal f) ->
      type_of_function f = Tfunction targs tres tcc ->
      val_casted_list vargs targs ->
      Ple (Genv.genv_next ge) (Mem.nextblock m) ->
      initial_state ge
        (cq vf (signature_of_type targs tres tcc) vargs m name)
        (Callstate vf vargs Kstop m).

Inductive at_external (ge: genv): state -> c_query -> Prop :=
  | at_external_intro name sg targs tres cconv vf vargs k m:
      let f := External (EF_external name sg) targs tres cconv in
      Genv.find_funct ge vf = Some f ->
      at_external ge
        (Callstate vf vargs k m)
        (cq vf sg vargs m name).

Axiom string_to_ident: string -> ident.

Definition name_is_internal (ge: Genv.t fundef type) (s: string): bool :=
  match Genv.find_symbol ge (string_to_ident s) with
  | Some b => Genv.is_internal ge (Vptr b Ptrofs.zero)
  | None => false
  end.

Definition semantics1 (p: program) :=
    {|
    skel := AST.erase_program p;
    activate se :=
      let ge := globalenv se p in
      {|
        Smallstep_.step := step1;
        Smallstep_.valid_query q := name_is_internal ge q;
        Smallstep_.initial_state := initial_state ge;
        Smallstep_.at_external := at_external ge;
        Smallstep_.after_external := after_external;
        Smallstep_.final_state := final_state;
        Smallstep_.globalenv := ge;
      |};
  |}.

Definition semantics2 (p: program) :=
    {|
    skel := AST.erase_program p;
    activate se :=
      let ge := globalenv se p in
      {|
        Smallstep_.step := step2;
        Smallstep_.valid_query q := true;
        Smallstep_.initial_state := initial_state ge;
        Smallstep_.at_external := at_external ge;
        Smallstep_.after_external := after_external;
        Smallstep_.final_state := final_state;
        Smallstep_.globalenv := ge;
      |};
  |}.

(* We introduce the complete program to avoid free pointers being captured
   during linking *)

Fixpoint complete_expr (cenv: composite_env) (e: expr): bool :=
  complete_type cenv (typeof e).

Fixpoint complete_statement (cenv: composite_env) (s: statement): bool :=
  match s with
  | Sskip => true
  | Sassign el er => complete_expr cenv el && complete_expr cenv er
  | Sset _ e => complete_expr cenv e
  | Scall _ ef eargs => complete_expr cenv ef
                       && fold_left (fun acc e => acc && complete_expr cenv e)
                                    eargs true
  | Sbuiltin _ _ _ eargs => fold_left (fun acc e => acc && complete_expr cenv e)
                                     eargs true
  | Ssequence s1 s2 => complete_statement cenv s1
                      && complete_statement cenv s2
  | Sifthenelse e s1 s2 => complete_expr cenv e
                          && complete_statement cenv s1
                          && complete_statement cenv s2
  | Sloop s sbody => complete_statement cenv s
                    && complete_statement cenv sbody
  | Sbreak => true
  | Scontinue => true
  | Sreturn (Some e) => complete_expr cenv e
  | Sreturn None => true
  | Sswitch e ls => complete_expr cenv e
                   && complete_labeled_statement cenv ls
  | Slabel _ s => complete_statement cenv s
  | Sgoto _ => true
  end
with complete_labeled_statement (cenv: composite_env) (ls: labeled_statements): bool :=
  match ls with
  | LSnil => true
  | LScons _ s ls => complete_statement cenv s
                    && complete_labeled_statement cenv ls
  end.

Definition complete_function (cenv: composite_env) (f: Ctypes.fundef function): bool :=
  match f with
  | Internal f => complete_statement cenv f.(fn_body)
  | External _ _ _ _ => true
  end.

Definition complete_globdef (cenv: composite_env) (gdef: globdef (Ctypes.fundef function) type) : bool :=
  match gdef with
  | Gfun f => complete_function cenv f
  | Gvar_  => true
  end.

Definition complete_program (cenv: composite_env) (p: program): Prop :=
  Forall (fun f => complete_globdef p.(prog_comp_env) (snd f) = true) p.(prog_defs).

(* The new linker has two major changes: 1. only one component is allowed to
   call the other 2. cross component function calls are well typed because
   Clight is a typed language *)

Fixpoint build_typelist (l: list (ident * type)): typelist :=
  match l with
  | nil => Tnil
  | cons (_, t) ts => Tcons t (build_typelist ts)
  end.

Definition link_fundef (fd1 fd2: Ctypes.fundef function) :=
  match fd1, fd2 with
  | Internal _, Internal _ => None
  | External ef1 targs1 tres1 cc1, External ef2 targs2 tres2 cc2 =>
    if external_function_eq ef1 ef2
       && typelist_eq targs1 targs2
       && type_eq tres1 tres2
       && calling_convention_eq cc1 cc2
    then Some (External ef1 targs1 tres1 cc1)
    else None
  (* p2 is not allowed to call p1 in the linked program in p1 + p2 *)
  | Internal f, External ef targs tres cc => None
  | External ef targs tres cc, Internal f =>
    match ef with
    | EF_external id sg =>
      if typelist_eq targs (build_typelist f.(fn_params))
         && type_eq tres f.(fn_return)
         && calling_convention_eq cc f.(fn_callconv)
      then Some (Internal f)
      else None
    | _ => None end
  end.

Inductive linkorder_fundef: fundef -> fundef -> Prop :=
| linkorder_fundef_refl: forall fd,
    linkorder_fundef fd fd
| linkorder_fundef_ext_int: forall f id sg targs tres cc,
    linkorder_fundef (External (EF_external id sg) targs tres cc) (Internal f).

Program Instance Linker_fundef: Linker fundef := {
  link := link_fundef;
  linkorder := linkorder_fundef
}.
Next Obligation.
  constructor.
Defined.
Next Obligation.
  inv H; inv H0; constructor.
Defined.
Next Obligation.
  destruct x, y; simpl in H.
+ discriminate.
+ destruct e; inv H.
+ destruct (typelist_eq t (build_typelist (fn_params f)) && type_eq t0 (fn_return f) && calling_convention_eq c (fn_callconv f))
           eqn:A; destruct e; inv H.
  split; constructor.
+ destruct (external_function_eq e e0 && typelist_eq t t1 && type_eq t0 t2 && calling_convention_eq c c0) eqn:A; inv H.
  InvBooleans. subst. split; constructor.
Defined.

Remark link_fundef_either:
  forall (f1 f2 f: Ctypes.fundef function), link f1 f2 = Some f -> f = f1 \/ f = f2.
Proof.
  simpl; intros. unfold link_fundef in H. destruct f1, f2; try discriminate.
- destruct (_ && type_eq t0 (fn_return f0) && calling_convention_eq c (fn_callconv f0)); destruct e; inv H; auto.
- destruct (external_function_eq e e0 && typelist_eq t t1 && type_eq t0 t2 && calling_convention_eq c c0); inv H; auto.
Qed.

Global Opaque Linker_fundef.

Definition link_program (p1 p2: program): option program :=
  match link (program_of_program p1) (program_of_program p2) with
  | None => None
  | Some p =>
      match lift_option (link p1.(prog_types) p2.(prog_types)) with
      | inright _ => None
      | inleft (exist typs EQ) =>
          match link_build_composite_env
                   p1.(prog_types) p2.(prog_types) typs
                   p1.(prog_comp_env) p2.(prog_comp_env)
                   p1.(prog_comp_env_eq) p2.(prog_comp_env_eq) EQ with
          | exist env (conj P Q) =>
              Some {| prog_defs := p.(AST.prog_defs);
                      prog_public := p.(AST.prog_public);
                      prog_main := p.(AST.prog_main);
                      prog_types := typs;
                      prog_comp_env := env;
                      prog_comp_env_eq := P |}
          end
      end
  end.

Definition linkorder_program (p1 p2: program) : Prop :=
     linkorder (program_of_program p1) (program_of_program p2)
  /\ (forall id co, p1.(prog_comp_env)!id = Some co -> p2.(prog_comp_env)!id = Some co).

Program Instance Linker_program: Linker program := {
  link := link_program;
  linkorder := linkorder_program
}.
Next Obligation.
  split. apply linkorder_refl. auto.
Defined.
Next Obligation.
  destruct H, H0. split. eapply linkorder_trans; eauto.
  intros; auto.
Defined.
Next Obligation.
  revert H. unfold link_program.
  destruct (link (program_of_program x) (program_of_program y)) as [p|] eqn:LP; try discriminate.
  destruct (lift_option (link (prog_types x) (prog_types y))) as [[typs EQ]|EQ]; try discriminate.
  destruct (link_build_composite_env (prog_types x) (prog_types y) typs
       (prog_comp_env x) (prog_comp_env y) (prog_comp_env_eq x)
       (prog_comp_env_eq y) EQ) as (env & P & Q & R).
  destruct (link_linkorder _ _ _ LP).
  intros X; inv X.
  split; split; auto.
Defined.

Global Opaque Linker_program.

Require Import CategoricalComp.

(* Linking of two semantics *)
Definition comp_semantics' {liA liB liC} (L1: semantics liB liC)
           (L2: semantics liA liB) sk: semantics liA liC :=
  {|
  activate se := comp_lts (L1 se) (L2 se);
  skel := sk;
  |}.

Definition comp_semantics {liA liB liC} (L1: semantics liB liC)
           (L2: semantics liA liB) :=
  option_map (comp_semantics' L1 L2) (link (skel L1) (skel L2)).

Section LINKING.
  Context (p1 p2 p: program) (LINK: link p1 p2 = Some p).
  Let p_ i := match i with true => p1 | false => p2 end.
  Let L i := semantics1 (p_ i).

  Inductive match_cont: state -> cont -> cont -> Prop :=
  | match_Kstop vf args k m:
      match_cont (Callstate vf args k m) Kstop k
  | match_Kseq s k k' call_state:
      match_cont call_state k k' ->
      match_cont call_state (Kseq s k) (Kseq s k')
  | match_Kloop1 call_state s1 s2 k k':
      match_cont call_state k k' ->
      match_cont call_state (Kloop1 s1 s2 k) (Kloop1 s1 s2 k')
  | match_Kloop2 call_state s1 s2 k k':
      match_cont call_state k k' ->
      match_cont call_state (Kloop2 s1 s2 k) (Kloop2 s1 s2 k')
  | match_Kswitch call_state k k':
      match_cont call_state k k' ->
      match_cont call_state (Kswitch k) (Kswitch k')
  | match_Kcall call_state optid f e le k k':
      match_cont call_state k k' ->
      match_cont call_state (Kcall optid f e le k) (Kcall optid f e le k').

  Inductive match_states: (@comp_state state state) -> state -> Prop :=
  | Match1 s:
      match_states (st1 s) s
  | State_match f s k k' e le m call_state:
      match_cont call_state k k' ->
      match_states (st2 call_state (State f s k e le m)) (State f s k' e le m)
  | Callstate_match vf args k k' m call_state:
      match_cont call_state k k' ->
      match_states (st2 call_state (Callstate vf args k m)) (Callstate vf args k' m)
  | Returnstate_match res k k' m call_state:
      match_cont call_state k k' ->
      match_states (st2 call_state (Returnstate res k m)) (Returnstate res k' m).

  Definition measure (S: @comp_state state state): nat :=
    match S with
    | st1 _ => 0
    | st2 _ _ => 1
    end.

  Lemma eval_expr_lvalue_match se i env le m:
    (forall e v, eval_expr (globalenv se (p_ i)) env le m e v ->
            eval_expr (globalenv se p) env le m e v)
    /\
    (forall e b ofs, eval_lvalue (globalenv se (p_ i)) env le m e b ofs ->
                eval_lvalue (globalenv se p) env le m e b ofs).
    Proof.
      apply eval_expr_lvalue_ind; intros; try now econstructor.
    Admitted.

    Lemma assign_loc_match se i e m loc ofs v m':
      assign_loc (globalenv se (p_ i)) (typeof e) m loc ofs v m' ->
      assign_loc (globalenv se p) (typeof e) m loc ofs v m'.
    Proof.
      inversion 1. subst.
      - eapply assign_loc_value; eauto.
      - eapply assign_loc_copy; subst; eauto.
        admit.
    Admitted.

    Lemma eval_exprlist_match se i e le m es tys vs:
      eval_exprlist (globalenv se (p_ i)) e le m es tys vs ->
      eval_exprlist (globalenv se p) e le m es tys vs.
    Proof.
      induction 1; econstructor; eauto.
      eapply eval_expr_lvalue_match. eauto.
    Qed.

  Lemma step_match1 se s1 s2 s1' t:
      match_states (st1 s1) s2 ->
      Clight.step1 (globalenv se p1) s1 t s1' ->
      exists (s2' : state),
        Clight.step1 (globalenv se p) s2' t s2' /\
        match_states (st1 s1') s2'.
  Proof.
    intros Hs Hstep. inv Hs. inv Hstep.

  Admitted.


  Lemma clight_linking:
    forward_simulation
      1 1
      (comp_semantics' (L true) (L false) (erase_program p))
      (semantics1 p).
  Proof.
    constructor.
    eapply Forward_simulation with
        (fsim_order := ltof _ measure)
        (fsim_match_states := fun se1 se2 w idx s1 s2 => idx = s1 /\ match_states s1 s2); auto.
    2: apply well_founded_ltof.
    intros se _ [ ] [ ] Hse. econstructor.
    - intros q _ [ ]. cbn.      (* the source program has a smaller domain *)
      admit.
    - (* initial state *)
      admit.
    - (* final_state *)
      admit.
    - (* external_call *)
      admit.
    - intros s1 t s' Hstep1 idx s2 [Hidx Hs].
      subst. inv Hstep1; cbn in *.
      +

  Admitted.


End LINKING.
