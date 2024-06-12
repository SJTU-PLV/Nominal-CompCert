Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Linking.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import Clight.
Require Import RustlightBase RustIR.
Require Import Errors.
Require Import Clightgen Clightgenspec.
Require Import LanguageInterface cklr.CKLR cklr.Inject cklr.InjectFootprint.

Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope gensym_monad_scope.

(** Correctness proof for the generation of Clight *)

Record match_prog (p: RustIR.program) (tp: Clight.program) : Prop := {
    match_prog_comp_env:
    tr_composite_env p.(prog_comp_env) tp.(Ctypes.prog_comp_env);
    match_prog_def:    
    match_program_gen tr_fundef (fun ty ty' => to_ctype ty = ty') p p tp;
    match_prog_skel:
    erase_program tp = erase_program p
  }.

Section PRESERVATION.

Variable prog: RustIR.program.
Variable tprog: Clight.program.
Hypothesis TRANSL: match_prog prog tprog.

Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
(* injp or inj ? *)

Variable w: inj_world.
Let ge := RustIR.globalenv se prog.
Let tge := Clight.globalenv tse tprog.

(* Simulation relation *)

Let ce := prog.(prog_comp_env).
Let tce := tprog.(Ctypes.prog_comp_env).
Variable dropm: PTree.t ident.

Definition match_env (f: meminj) (e: env) (te: Clight.env) : Prop :=
  (* me_mapped in Simpllocalproof.v *)
  forall id b ty, e!id = Some (b, ty) ->
          exists tb, te!id = Some (tb, to_ctype ty) /\ f b = Some (tb, 0).


Inductive match_cont : RustIR.cont -> Clight.cont -> Prop :=
| match_Kstop: match_cont RustIR.Kstop Clight.Kstop
| match_Kseq: forall s ts k tk,
    (* To avoid generator, we need to build the spec *)
    tr_stmt ce tce dropm s ts ->
    match_cont k tk ->
    match_cont (RustIR.Kseq s k) (Clight.Kseq ts tk)
| match_Kloop: forall s ts k tk,
    tr_stmt ce tce dropm s ts ->
    match_cont k tk ->
    match_cont (RustIR.Kloop s k) (Clight.Kloop1 ts Clight.Sskip tk)
| match_Kcall1: forall p f tf e te le k tk cty temp pe j,
    (* we need to consider temp is set to a Clight expr which is
    translated from p *)
    transl_function ce tce dropm f = OK tf ->
    cty = to_ctype (typeof_place p) ->
    place_to_cexpr tce p = OK pe ->
    match_cont k tk ->
    match_env j e te ->
    match_cont (RustIR.Kcall (Some p) f e k) (Clight.Kcall (Some temp) tf te le (Clight.Kseq (Clight.Sassign pe (Etempvar temp cty)) tk))
| match_Kcall2: forall f tf e te le k tk,
    (* how to relate le? *)
    transl_function ce tce dropm f = OK tf ->
    match_cont k tk ->
    match_cont (RustIR.Kcall None f e k) (Clight.Kcall None tf te le tk)
| match_Kcalldrop: forall id e te le k tk tf co j,
    (* Is it correct? *)
    ce ! id = Some co ->
    drop_glue_for_composite ce tce dropm id co.(co_sv) co.(co_members) co.(co_attr) = OK (Some tf) ->
    match_env j e te ->
    match_cont (RustIR.Kcalldrop id e k) (Clight.Kcall None tf te le tk)
.


Inductive match_states: RustIR.state -> Clight.state -> Prop :=
| match_regular_state: forall f tf s ts k tk m tm e te le j
    (MFUN: tr_function ce tce dropm f tf)
    (MSTMT: tr_stmt ce tce dropm s ts)
    (* match continuation *)
    (MCONT: match_cont k tk)
    (MINJ: Mem.inject j m tm)   
    (MENV: match_env j e te),
    match_states (RustIR.State f s k e m) (Clight.State tf ts tk te le tm)
| match_call_state: forall vf vargs k m tvf tvargs tk tm j fd targs tres cconv orgs rels
   (MCONT: match_cont k tk)
   (VINJ: Val.inject j vf tvf)
   (MINJ: Mem.inject j m tm)
   (AINJ: Val.inject_list j vargs tvargs)
   (VFIND: Genv.find_funct ge vf = Some fd)
   (FUNTY: type_of_fundef fd = Tfunction orgs rels targs tres cconv),
    match_states (RustIR.Callstate vf vargs k m) (Clight.Callstate tvf tvargs tk tm)
| match_return_state: forall v k m tv tk tm j
   (MCONT: match_cont k tk)
   (MINJ: Mem.inject j m tm)
   (RINJ: Val.inject j v tv),
    match_states (RustIR.Returnstate v k m) (Clight.Returnstate tv tk tm)
| match_calldrop_box: forall p k e m b ofs tk tm ty a j fb
    (* we can store the address of p in calldrop and build a local env
    in Drop state according to this address *)
    (VFIND: Genv.find_def tge fb = Some (Gfun malloc_decl))
    (PTY: typeof_place p = Tbox ty a)
    (PADDR: eval_place ce e m p b ofs)
    (MCONT: match_cont k tk)
    (MINJ: Mem.inject j m tm),
    match_states (RustIR.Calldrop p k e m) (Clight.Callstate (Vptr fb Ptrofs.zero) [(Vptr b ofs)] tk tm)
| match_calldrop_composite: forall p k e m b ofs tk tm a j fb id fid drop_glue orgs
    (DROPM: dropm!id = Some fid)
    (VFIND: Genv.find_def tge fb = Some drop_glue)
    (SYMB: Genv.find_symbol tge fid = Some fb)
    (* Is it correct? *)
    (GLUE: In (fid, drop_glue) tprog.(prog_defs))
    (PTY: typeof_place p = Tstruct orgs id a \/ typeof_place p = Tvariant orgs id a)
    (PADDR: eval_place ce e m p b ofs)
    (MCONT: match_cont k tk)
    (MINJ: Mem.inject j m tm),
    match_states (RustIR.Calldrop p k e m) (Clight.Callstate (Vptr fb Ptrofs.zero) [(Vptr b ofs)] tk tm)
| match_drop_state: forall id s k e m tf ts tk te le tm j co
    (* How to relate e and te? and le? *)
    (MSTMT: tr_stmt ce tce dropm s ts)
    (MCONT: match_cont k tk)
    (MINJ: Mem.inject j m tm),
    ce ! id = Some co ->
    drop_glue_for_composite ce tce dropm id co.(co_sv) co.(co_members) co.(co_attr) = OK (Some tf) ->
    match_states (RustIR.Dropstate id s k e m) (Clight.State tf ts tk te le tm)
.

(* Type preservation in translation *)

Lemma place_to_cexpr_type: forall p e,
    place_to_cexpr tce p = OK e ->
    Clight.typeof e = to_ctype (typeof_place p).
Admitted.

Lemma expr_to_cexpr_type: forall e e',
    expr_to_cexpr ce tce e = OK e' ->
    Clight.typeof e' = to_ctype (typeof e) .
Admitted.


(* Injection is preserved during evaluation *)

Lemma eval_expr_inject: forall e te j a a' m tm v le,
    expr_to_cexpr ce tce a = OK a' ->
    eval_expr ge e m a v ->
    match_env j e te ->
    Mem.inject j m tm ->
    exists v', Clight.eval_expr tge te le tm a' v' /\ Val.inject j v v'.
(* To prove this lemma, we need to support type checking in the
   evaluation of expression in RustIR *)
Admitted.

Lemma eval_place_inject: forall e te j p lv m tm le b ofs,
    place_to_cexpr tce p = OK lv ->
    eval_place ge e m p b ofs ->
    match_env j e te ->
    Mem.inject j m tm ->
    exists b' ofs', Clight.eval_lvalue tge te le tm lv b' ofs' Full /\ Val.inject j (Vptr b ofs) (Vptr b' ofs').
Admitted.

Lemma assign_loc_inject: forall f ty m loc ofs v m' tm loc' ofs' v',
    assign_loc ge ty m loc ofs v m' ->
    Val.inject f (Vptr loc ofs) (Vptr loc' ofs') ->
    Val.inject f v v' ->
    Mem.inject f m tm ->
    exists tm',
      Clight.assign_loc tge (to_ctype ty) tm loc' ofs' Full v' tm'
      /\ Mem.inject f m' tm'.
Admitted.


Remark list_cons_neq: forall A (a: A) l, a :: l <> l.
Proof.
  intros. induction l. intro. congruence.
  intro. inv H.  congruence.
Qed.

Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus step1 tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
  
  (* assign *)
  - inv MSTMT. simpl in H2.
    monadInv_comb H2.
    (* eval place and expr *)
    exploit eval_place_inject;eauto. instantiate (1:= le0).
    intros (b' & ofs' & EL & INJL).
    exploit eval_expr_inject; eauto. instantiate (1:= le0).
    intros (v' & ER & INJR).
    exploit assign_loc_inject;eauto.
    intros (tm2 & TASS & INJA).
    eexists. split.
    (* step *)
    + eapply plus_one.
      eapply Clight.step_assign;eauto.
      (* sem_cast *)
      instantiate (1:= v').
      (* Proof strategy:
         1. type equal between lhs and rhs
         2. evaluation of well typed expression produces casted value (val_casted)
         3. use cast_val_casted *)
      admit.
      (* assign_loc *)
      erewrite place_to_cexpr_type; eauto.
    (* match state *)
    + eapply match_regular_state;eauto.
      econstructor. simpl. instantiate (1 := g). eauto.

  (* assign_variant *)
  - inv MSTMT. simpl in H6.
    monadInv_comb H6.
    unfold transl_assign_variant in EQ2.
    rename H1 into SENUM.
    unfold ge in SENUM. simpl in SENUM. fold ce in SENUM.
    rewrite SENUM in EQ2.
    destruct (co_sv co) eqn: SCV; [inv EQ2|].
    rewrite H2 in EQ2. rename H2 into TAG.
    destruct TRANSL. eapply match_prog_comp_env0 in SENUM as MATCHCOMP.
    rewrite SCV in MATCHCOMP.
    destruct MATCHCOMP as (tco & union_id & tag_fid & union_fid & union & MATCHCOMP).
    cbn in MATCHCOMP.
    destruct MATCHCOMP as (A & B & C & D & MATCHCOMP).
    fold tce in A. rewrite A in EQ2.
    rewrite D in EQ2.
    inv EQ2.
    (* step in target *)
    (* eexists. split. *)
    (* + eapply plus_left. *)
    (*   eapply Clight.step_seq. *)
    (*   eapply star_step. eapply Clight.step_assign. *)
    admit.

  (* box *)
  - admit.

  (* step_drop1 *)
  - inv MSTMT. simpl in H.
    monadInv_sym H. unfold gensym in EQ. inv EQ.
    monadInv_comb EQ0. destruct expand_drop in EQ1;[|inv EQ1].
    inv EQ1. destruct g. simpl in H1. inv H1. eapply list_cons_neq in H0.
    contradiction.
    unfold expand_drop in H1. destruct (typeof_place p) eqn: TYP; try congruence.
    (* three cases: box, struct and enum *)
    + admit.
    + destruct (dropm ! i) eqn: DROPM;inv H1.
      admit.
    + destruct (dropm ! i) eqn: DROPM;inv H1.
      admit.

  (* step_drop2: drop in Dropstate *)
  - inv MSTMT. simpl in H.
    monadInv_sym H. unfold gensym in EQ. inv EQ.
    monadInv_comb EQ0. destruct expand_drop in EQ1;[|inv EQ1].
    inv EQ1. destruct g. simpl in H1. inv H1. eapply list_cons_neq in H0.
    contradiction.
    unfold expand_drop in H1. destruct (typeof_place p) eqn: TYP; try congruence.
    + admit.
    + destruct (dropm ! i) eqn: DROPM;inv H1.
      admit.
    + destruct (dropm ! i) eqn: DROPM;inv H1.
      admit.

  (* step_drop_seq *)
  - admit.

  (* step_calldrop_box: simulate [free] semantics *)
  - admit.

  (* impossible *)
  - destruct PTY. congruence. congruence.
  (* impossible *)
  - congruence.

  (* step_drop_struct *)
  - destruct PTY; try congruence. rewrite H in H1. inv H1.
    (* how to prove drop_glue is generated from drop_glue_for_composite *)
    admit.

  (* impossible *)
  - congruence.
    
  (* step_drop_enum *)
  - destruct PTY; try congruence. rewrite H in H4. inv H4.
    admit.
  (* step_drop_return *)
  - admit.
  (* step_returnstate_drop *)
  - admit.
  (* step_storagelive *)
  - admit.
  (* step_storagedead *)
  - admit.

  (* step_call *)
  - inv MSTMT. simpl in H4.
    monadInv_comb H4. monadInv_sym EQ3. unfold gensym in EQ2. inv EQ2.
    inv EQ4. destruct g. simpl in H6. inv H6. eapply list_cons_neq in H5.
    contradiction.
    admit.

  (* step_internal_function *)
  - (* how to prove tr_function f tf because we should guarantee that
    f is not a drop glue *)
    admit.

  (* step_external_function *)
  - admit.

  (* step_return_0 *)
  - admit.
  (* step_return_1 *)
  - admit.
  (* step_skip_call *)
  - admit.
  (* step_returnstate *)
  - admit.
  (* step_seq *)
  - admit.
  (* step_skip_seq *)
  - admit.
  (* step_continue_seq *)
  - admit.
  (* step_break_seq *)
  - admit.
  (* step_ifthenelse *)
  - admit.
  (* step_loop *)
  - admit.
  (* step_skip_or_continue_loop *)
  - admit.
  (* step_break_loop *)
  - admit.
        
Admitted.

Lemma initial_states_simulation:
  forall q1 q2 S, match_query (cc_c inj) w q1 q2 -> initial_state ge q1 S ->
  exists R, Clight.initial_state tge q2 R /\ match_states S R.
Admitted.

Lemma final_states_simulation:
  forall S R r1, match_states S R -> final_state S r1 ->
  exists r2, Clight.final_state R r2 /\ match_reply (cc_c inj) w r1 r2.
Admitted.

Lemma external_states_simulation:
  forall S R q1, match_states S R -> at_external ge S q1 ->
  exists wx q2, Clight.at_external tge R q2 /\ cc_c_query injp wx q1 q2 /\ match_stbls injp wx se tse /\
  forall r1 r2 S', match_reply (cc_c injp) wx r1 r2 -> after_external S r1 S' ->
  exists R', Clight.after_external R r2 R' /\ match_states S' R'.
Admitted.


End PRESERVATION.

Theorem transl_program_correct prog tprog:
  match_prog prog tprog ->
  forward_simulation cc_id cc_id (RustIR.semantics prog) (Clight.semantics1 tprog).
Admitted.
