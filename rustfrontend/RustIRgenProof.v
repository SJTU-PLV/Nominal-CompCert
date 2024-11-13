Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Linking.
Require Import Rusttypes.
Require Import Errors.
Require Import LanguageInterface CKLR Inject InjectFootprint.
Require Import RustIR Rustlight RustOp RustIRgen.
Require Import RustIRown.
Require Import Rustlightown.    

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope error_monad_scope.

(** Semantics preservation of the generation of RustIR programs from
Rustlight programs. The key part of the proof is to relate the
semantics drops expressed in the continuation to the drop statements
explicitly inserted in the program *)


Definition match_glob (ctx: composite_env) (gd: globdef Rustlight.fundef type) (tgd: globdef RustIR.fundef type) : Prop :=
  match gd, tgd with
  | Gvar v1, Gvar v2 =>
      match_globvar eq v1 v2
  | Gfun fd1, Gfun fd2 =>
      transl_fundef ctx fd1 = fd2
  | _, _ => False
  end.

Record match_prog (p : Rustlight.program) (tp : RustIR.program) : Prop := {
    match_prog_main:
    tp.(prog_main) = p.(prog_main);
    match_prog_public:
    tp.(prog_public) = p.(prog_public);
    match_prog_types:
    tp.(prog_types) = p.(prog_types);
    match_prog_defs:
    list_forall2 (fun g1 g2 => fst g1 = fst g2 /\ match_glob p.(prog_comp_env) (snd g1) (snd g2)) p.(prog_defs) tp.(prog_defs);
    match_dropm:
    generate_dropm p = RustIR.generate_dropm tp;
    match_prog_skel:
    erase_program tp = erase_program p;
  }.


(* Prove match_genv for this specific match_prog *)

Section MATCH_PROGRAMS.

Variable p: program.
Variable tp: RustIR.program.
Hypothesis TRANSL: match_prog p tp.

Section INJECT.

Variable j: meminj.
Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
Hypothesis sematch: Genv.match_stbls j se tse.

Let ce := prog_comp_env p.

Lemma globalenvs_match:
  Genv.match_genvs j (match_glob ce) (Genv.globalenv se p) (Genv.globalenv tse tp).
Proof.
  intros. split; auto. intros. cbn [Genv.globalenv Genv.genv_defs NMap.get].
  assert (Hd:forall i, Coqlib.option_rel (match_glob ce) (prog_defmap p)!i (prog_defmap tp)!i).
  {
    intros.
    eapply PTree_Properties.of_list_related.
    apply TRANSL.
  }
  rewrite !PTree.fold_spec.
  apply PTree.elements_canonical_order' in Hd. revert Hd.
  generalize (prog_defmap p), (prog_defmap tp). intros d1 d2 Hd.
  (*   cut (option_rel match_gd (PTree.empty _)!b1 (PTree.empty _)!b2). *)
  cut (Coqlib.option_rel (match_glob ce)
         (NMap.get _ b1 (NMap.init (option (globdef (Rusttypes.fundef function) type)) None))
         (NMap.get _ b2 (NMap.init (option (globdef (Rusttypes.fundef RustIR.function) type)) None ))).
  (* adhoc generalize because types are the same *)
  - generalize (NMap.init (option (globdef (Rusttypes.fundef function) type)) None).
    generalize (NMap.init (option (globdef (Rusttypes.fundef RustIR.function) type)) None).
    induction Hd as [ | [id1 g1] l1 [id2 g2] l2 [Hi Hg] Hl IH]; cbn in *; eauto.
    intros t1 t2 Ht. eapply IH. eauto. rewrite Hi.
    eapply Genv.add_globdef_match; eauto.
  - unfold NMap.get. rewrite !NMap.gi. constructor.
Qed.

Theorem find_def_match:
  forall b tb delta g,
  Genv.find_def (Genv.globalenv se p) b = Some g ->
  j b = Some (tb, delta) ->
  exists tg,
  Genv.find_def (Genv.globalenv tse tp) tb = Some tg /\
  match_glob ce g tg /\
  delta = 0.
Proof.
  apply Genv.find_def_match_genvs, globalenvs_match.
Qed.

Theorem find_funct_match:
  forall v tv f,
  Genv.find_funct (Genv.globalenv se p) v = Some f ->
  Val.inject j v tv ->
  exists tf,
  Genv.find_funct (Genv.globalenv tse tp) tv = Some tf /\ transl_fundef ce f = tf.
Proof.
  intros. exploit Genv.find_funct_inv; eauto. intros [b EQ]. subst v. inv H0.
  rewrite Genv.find_funct_find_funct_ptr in H. unfold Genv.find_funct_ptr in H.
  destruct Genv.find_def as [[|]|] eqn:Hf; try congruence. inv H.
  edestruct find_def_match as (tg & ? & ? & ?); eauto. subst.
  simpl in H0. destruct tg.
  rewrite Genv.find_funct_find_funct_ptr. unfold Genv.find_funct_ptr. rewrite H. eauto.
  contradiction.
Qed.


Theorem find_funct_none:
  forall v tv,
  Genv.find_funct (globalenv se p) v = None ->
  Val.inject j v tv ->
  v <> Vundef ->
  Genv.find_funct (RustIR.globalenv tse tp) tv = None.
Proof.
  intros v tv Hf1 INJ Hv. destruct INJ; auto; try congruence.
  destruct (Mem.sup_dec b1 se.(Genv.genv_sup)).
  - edestruct Genv.mge_dom; eauto. rewrite H1 in H. inv H.
    rewrite Ptrofs.add_zero. revert Hf1.
    unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def.
    destruct Ptrofs.eq_dec; auto.
    generalize (Genv.mge_defs globalenvs_match b1 H1). intros REL. simpl.
    inv REL. auto.
    destruct x. congruence. simpl in H2.
    destruct y. contradiction. auto.    
  - unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def.
    destruct Ptrofs.eq_dec; auto.
    destruct NMap.get as [[|]|] eqn:Hdef; auto. exfalso.
    apply Genv.genv_defs_range in Hdef.
    eapply Genv.mge_separated in H; eauto. cbn in *.
    apply n,H,Hdef.
Qed.

Theorem is_internal_match :
  (forall f tf, transl_fundef ce f = tf ->
   fundef_is_internal tf = fundef_is_internal f) ->
  forall v tv,
    Val.inject j v tv ->
    v <> Vundef ->
    Genv.is_internal (RustIR.globalenv tse tp) tv = Genv.is_internal (globalenv se p) v.
Proof.
  intros Hmatch v tv INJ DEF. unfold Genv.is_internal.
  destruct (Genv.find_funct _ v) eqn:Hf.
  - edestruct find_funct_match as (tf & Htf & ?); try eassumption.
    unfold fundef.
    simpl. setoid_rewrite Htf. eauto.
  - erewrite find_funct_none; eauto.
Qed.


End INJECT.

End MATCH_PROGRAMS.


Section PRESERVATION.


Variable prog: program.
Variable tprog: RustIR.program.

Hypothesis TRANSL: match_prog prog tprog.

Variable se: Genv.symtbl.
(* Variable dropflags: PTree.t (list (place * ident)). *)

Let ge := globalenv se prog.
Let tge := RustIR.globalenv se tprog.

(* Some lemmas about function definitions in identical symtbls *)

Corollary find_funct_match_id:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef ge f = tf.
Proof.
  intros. eapply find_funct_match; eauto using Genv.match_stbls_id.
    apply val_inject_id. auto.
Qed.

Theorem is_internal_match_id :
  (forall f tf, transl_fundef ge f = tf ->
   fundef_is_internal tf = fundef_is_internal f) ->
  forall v ,
    v <> Vundef ->
    Genv.is_internal tge v = Genv.is_internal ge v.
Proof.
  intros. destruct v; auto.
  eapply is_internal_match; eauto using Genv.match_stbls_id.
  apply val_inject_id; auto. 
Qed.


Lemma comp_env_preserved:
  RustIR.genv_cenv tge = genv_cenv ge.
Proof.
  unfold tge, ge. destruct prog, tprog; simpl. inv TRANSL. simpl in *.
  congruence.
Qed.


Lemma type_of_fundef_preserved:
  forall fd tfd,
  transl_fundef ge fd = tfd -> RustIR.type_of_fundef tfd = type_of_fundef fd.
Proof.
  intros. destruct fd; simpl in H; subst.
  simpl; unfold type_of_function; simpl. auto.
  simpl; unfold type_of_function; simpl. auto.
Qed.

Lemma function_not_drop_glue_preserved: forall fd tfd,
    transl_fundef ge fd = tfd ->
    function_not_drop_glue fd ->
    RustIR.function_not_drop_glue tfd.
Proof.
  intros. destruct fd.
  - simpl in *. destruct (fn_drop_glue f) eqn: A; try contradiction.
    subst. simpl. rewrite A. auto.
  - subst. simpl in *. auto.
Qed.

Inductive match_drop_insert_kind: drop_insert_kind -> RustIR.statement -> Prop :=
| match_drop_reassign: forall p,
    match_drop_insert_kind (drop_reassign p) (gen_drop ge p)
| match_drop_escape_before: forall l,
    match_drop_insert_kind (drop_escape_before l) (gen_drops_for_escape_vars ge l)
| match_drop_escape_after: forall id l,
    match_drop_insert_kind (drop_escape_after id l) (RustIR.Ssequence (Sstoragedead id) (gen_drops_for_escape_vars ge l))
| match_drop_return: forall l,
    match_drop_insert_kind (drop_return l) (gen_drops_for_vars ge l)
| match_drop_reassign_end:
  match_drop_insert_kind drop_reassign_end RustIR.Sskip
.


(* We distinguish the dropcont from reassign purpose and out-of-scope
purpose *)

Inductive match_dropcont : dropcont -> RustIR.statement -> Prop :=
| match_Dassign: forall p e,
    match_dropcont (Dassign p e) (RustIR.Sassign p e)
| match_Dassign_variant: forall p e eid fid,
    match_dropcont (Dassign_variant p eid fid e) (RustIR.Sassign_variant p eid fid e)
| match_Dbox: forall p e,
    match_dropcont (Dbox p e) (RustIR.Sbox p e)
| match_Dcall: forall p a al,
    match_dropcont (Dcall p a al) (RustIR.Scall p a al)
| match_Dbreak:
  match_dropcont Dbreak RustIR.Sbreak
| match_Dcontinue:
  match_dropcont Dcontinue RustIR.Scontinue
| match_Dendlet:
  (* may be we should generate sskip in the end of the let *)
  match_dropcont Dendlet RustIR.Sskip
.


Inductive match_cont (params: list (ident * type)) : cont -> RustIRown.cont -> Prop :=
| match_Klet: forall k tk drop id ty
    (MCONT: match_cont params k tk)
    (DROP: drop = gen_drops_for_escape_vars ge [(id, ty)]),
    (* when executing Klet, Rustlight would enter Dropinsert state
    where drop_escape contains the out-of-scope variable which is
    related to (drop;storagedead id) *)
    (* The additional Kseq is used to simulate the step in Dendlet *)
    match_cont params (Klet id ty k) (RustIRown.Kseq drop (RustIRown.Kseq RustIR.Sskip tk))
(* The drops are inserted for the reassignment. The translated
statement does not contain storagedead *)
| match_Kdropinsert: forall k tk dk s1 s2 st
    (MCONT: match_cont params k tk)
    (MDCONT: match_dropcont dk s2)
    (MDINS: match_drop_insert_kind st s1),
    (** TODO: before running st, we may need to execute the
    storagedead in the target *)
    match_cont params (Kdropinsert st dk k)
      (* s1 should contain the storagedead of the first element of st *)
      (RustIRown.Kseq s1 (RustIRown.Kseq s2 tk))
| match_Kstop:
    match_cont params Kstop RustIRown.Kstop
| match_Kseq: forall k s tk ts
    (TRSTMT: transl_stmt ge params s (cont_vars k) = ts)
    (MCONT: match_cont params k tk),
    match_cont params (Kseq s k) (RustIRown.Kseq ts tk)
| match_Kloop: forall k tk s ts
    (MCONT: match_cont params k tk)
    (TRSTMT: transl_stmt ge params s (cont_vars k) = ts),
    match_cont params (Kloop s k) (RustIRown.Kloop ts tk)
| match_Kcall: forall k tk p f tf le own
    (TRFUN: transl_function ge f = tf)
    (MCONT: match_cont f.(fn_params) k tk),
    match_cont params (Kcall p f le own k) (RustIRown.Kcall p tf le own tk)
| match_Kdropplace: forall k tk f tf st drops le own
    (MCONT: match_cont f.(fn_params) k tk)
    (TRFUN: transl_function ge f = tf),
    match_cont params (Kdropplace f st drops le own k) (RustIRown.Kdropplace tf st drops le own tk)
| match_Kdropcall: forall k tk id v st membs
    (MCONT: match_cont params k tk),
    match_cont params (Kdropcall id v st membs k) (RustIRown.Kdropcall id v st membs tk)
.
     
Inductive match_states: Rustlightown.state -> RustIRown.state -> Prop := 
| match_regular_state: forall f s k e own m tf ts tk vars
    (TRFUN: transl_function ge f = tf)
    (TRSTMT: transl_stmt ge f.(fn_params) s vars = ts)
    (* The in-scope variables collected in transl_stmt are the same as
    those collected in the continuation *)
    (CONTVARS: cont_vars k = vars)
    (MCONT: match_cont f.(fn_params) k tk),
    match_states (State f s k e own m) (RustIRown.State tf ts tk e own m)
| match_dropinsert: forall f tf st dk k tk le own m ts1 ts2
    (TRFUN: transl_function ge f = tf)
    (STMT1: match_drop_insert_kind st ts1)
    (STMT2: match_dropcont dk ts2)
    (MCONT: match_cont f.(fn_params) k tk),
    match_states (Dropinsert f st dk k le own m) (RustIRown.State tf ts1 (RustIRown.Kseq ts2 tk) le own m)
| match_dropplace: forall f tf k tk st drops le m own
    (TRFUN: transl_function ge f = tf)
    (MCONT: match_cont f.(fn_params) k tk),
    match_states (Dropplace f st drops k le own m) (RustIRown.Dropplace tf st drops tk le own m)
| match_dropstate: forall id v st membs k tk m
    (* We does not care the parameters in drop glue state *)
    (MCONT: forall l, match_cont l k tk),
    match_states (Dropstate id v st membs k m) (RustIRown.Dropstate id v st membs tk m)
| match_callstate: forall v al k tk m
    (MCONT: forall l, match_cont l k tk),
    match_states (Callstate v al k m) (RustIRown.Callstate v al tk m)
| match_returnstate: forall v k tk m
    (MCONT: forall l, match_cont l k tk),
    match_states (Returnstate v k m) (RustIRown.Returnstate v tk m)
.

Lemma gen_drops_for_escape_vars_nil:
    gen_drops_for_escape_vars ge nil = RustIR.Sskip.
Proof.
  auto.
Qed.

  
Lemma gen_drops_for_escape_vars_cons1: forall id ty l,
    own_type ge ty = true ->
    gen_drops_for_escape_vars ge ((id, ty) :: l) =
      RustIR.Ssequence (Sdrop (Plocal id ty)) (RustIR.Ssequence (Sstoragedead id) (gen_drops_for_escape_vars ge l)).
Proof.
  unfold gen_drops_for_escape_vars.
  intros. simpl in *. rewrite H. auto.
Qed.


Lemma gen_drops_for_escape_vars_cons2: forall id ty l,
    own_type ge ty = false ->
    gen_drops_for_escape_vars ge ((id, ty) :: l) =
      RustIR.Ssequence RustIR.Sskip (RustIR.Ssequence (Sstoragedead id) (gen_drops_for_escape_vars ge l)).
Proof.
  unfold gen_drops_for_escape_vars.
  intros. simpl in *. rewrite H.
 auto.
Qed.

Lemma gen_drops_for_vars_cons1: forall id ty l,
    own_type ge ty = true ->
    gen_drops_for_vars ge ((id, ty) :: l) =
      RustIR.Ssequence (Sdrop (Plocal id ty)) (gen_drops_for_vars ge l).
Proof.
  unfold gen_drops_for_vars.
  intros. simpl in *.
  unfold  vars_to_drops. simpl.
  rewrite H. 
  auto.
Qed.


Lemma gen_drops_for_vars_cons2: forall id ty l,
    own_type ge ty = false ->
    gen_drops_for_vars ge ((id, ty) :: l) =
      RustIR.Ssequence RustIR.Sskip (gen_drops_for_vars ge l).
Proof.
  unfold gen_drops_for_vars.
  intros. simpl in *.
  unfold  vars_to_drops. simpl.
  rewrite H.  
  auto.
Qed.

Ltac solve_eval :=
  try erewrite comp_env_preserved; eauto.


Lemma step_in_dropinsert_simulation:
  forall S1 t S2, step_dropinsert ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus RustIRown.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
  (* step_dropinsert_to_dropplace_escape *)
  - inv STMT1. erewrite gen_drops_for_escape_vars_cons1; eauto.
    eexists. split.
    (* step *)
    econstructor.
    econstructor. eapply star_step.
    econstructor; eauto. rewrite comp_env_preserved. eauto. 
    eapply star_refl. 1-2 : eauto.
    (* match_states *)
    econstructor; auto.
    econstructor; auto.
    econstructor.
  (* step_dropinsert_to_dropplace_reassign *)
  - inv STMT1. unfold gen_drop. rewrite OWNTY. simpl.
    eexists. split.
    (* step *)
    econstructor.
    econstructor. eapply star_step.
    econstructor; eauto. rewrite comp_env_preserved. eauto. 
    eapply star_refl. 1-2 : eauto.
    (* match_states *)
    econstructor; auto.
    econstructor; auto.
    econstructor.
  (* step_dropinsert_skip_escape *)
  - inv STMT1. erewrite gen_drops_for_escape_vars_cons2; eauto.
    eexists. split.
    (* step *)
    econstructor.
    econstructor.
    eapply star_step. eapply RustIRown.step_skip_seq.
    eapply star_refl. 1-2: eauto.
    (* match_states *)
    econstructor; auto.
    econstructor; auto.
  (* step_dropinsert_skip_reassign *)
  - inv STMT1. unfold gen_drop. rewrite OWNTY. simpl.
    eexists. split.
    (* step *)
    econstructor.
    econstructor. eapply star_step.
    econstructor; eauto. 
    eapply star_refl. 1-2 : eauto.
    (* match_states *)
    econstructor; auto.
    econstructor; auto.
  (* step_dropinsert_to_dropplace_return *)
  - inv STMT1. erewrite gen_drops_for_vars_cons1; eauto.
    eexists. split.
    (* step *)
    econstructor.
    econstructor. eapply star_step.
    econstructor; eauto.
    rewrite comp_env_preserved. eauto. 
    eapply star_refl. 1-2 : eauto.
    (* match_states *)
    econstructor; auto.
    econstructor; auto.
    econstructor.
  (* step_dropinsert_skip_return *)
  - inv STMT1. erewrite gen_drops_for_vars_cons2; eauto.
    eexists. split.
    (* step *)
    econstructor.
    econstructor. eapply star_step.
    eapply RustIRown.step_skip_seq.
    eapply star_refl. 1-2 : eauto.
    (* match_states *)
    econstructor; auto.
    econstructor; auto.
  (* step_dropinsert_escape_to_after *)
  - inv STMT1.
    eexists. split.
    (* step *)
    econstructor.
    econstructor. eapply star_step.
    econstructor. eapply star_step.
    eapply RustIRown.step_skip_seq.    
    eapply star_refl. 1-3 : eauto.
    (* match_state *)
    econstructor; auto.
    constructor.
  (* step_dropinsert_assign *)
  - inv STMT1. inv STMT2.
    eexists. split.
    econstructor. eapply RustIRown.step_skip_seq.    
    eapply star_step. econstructor; solve_eval.
    eapply star_refl. 1-2: eauto.
    (* match_states *)
    econstructor; eauto.
  (* step_dropinsert_assign_variant *)
  - inv STMT1. inv STMT2.
    eexists. split.
    econstructor. eapply RustIRown.step_skip_seq.    
    eapply star_step. econstructor; solve_eval.
    eapply star_refl. 1-2: eauto.
    (* match_states *)
    econstructor; eauto.
  (* step_dropinsert_box *)
  - inv STMT1. inv STMT2.
    eexists. split.
    econstructor. eapply RustIRown.step_skip_seq.    
    eapply star_step. econstructor; solve_eval.
    eapply star_refl. 1-2: eauto.
    (* match_states *)
    econstructor; eauto.
  (* step_dropinset_call *)
  - inv STMT1. inv STMT2.
    exploit find_funct_match_id; eauto.
    intros (tf & FIND & TRF).
    eexists. split.
    econstructor. eapply RustIRown.step_skip_seq.    
    eapply star_step. econstructor; solve_eval.
    eapply function_not_drop_glue_preserved; eauto.
    erewrite type_of_fundef_preserved; eauto.
    eapply star_refl. 1-2: eauto.
    (* match_states *)
    econstructor; eauto.
    intros. econstructor; auto.
  (* step_dropinsert_break_seq *)
  - inv STMT1. inv STMT2. inv MCONT.
    rewrite gen_drops_for_escape_vars_nil.
    eexists. split.
    econstructor. eapply RustIRown.step_skip_seq.
    eapply star_step. econstructor.
    eapply star_refl. 1-2: eauto.
    
    
Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus RustIRown.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
  (* step_assign *)
  - simpl.
    eexists. split.
    (* step *)
    econstructor. econstructor.
    eapply star_refl. auto.
    econstructor; auto.
    econstructor. econstructor.
  (* step_assign_variant *)
  - simpl.
    eexists. split.
    (* step *)
    econstructor. econstructor.
    eapply star_refl. auto.
    econstructor; auto.
    econstructor. econstructor.
  (* step_box *)
  - simpl.
    eexists. split.
    (* step *)
    econstructor. econstructor.
    eapply star_refl. auto.
    econstructor; auto.
    econstructor. econstructor.
  (* step_let *)
  - simpl.
    eexists. split.
    (* step *)
    econstructor. econstructor.
    eapply star_step. econstructor.
    eapply star_step. econstructor.
    eapply star_step. econstructor.
    eapply star_step. econstructor.
    eapply star_refl. 1-5: eauto.
    econstructor; auto.
    econstructor; auto.
  (* step_end_let *)
  - simpl. inv MCONT.
    eexists. split.
    econstructor. eapply RustIRown.step_skip_seq.
    eapply star_refl. auto.
    econstructor; auto.
    constructor. constructor.
  (* step_in_dropinsert *)
  - 
  (* step_in_dropplace *)
  - admit.
  (* step_dropstate *)
  - admit.
  (* step_call *)
  - admit.
  (* step_internal_function *)
  - admit.
  (* step_external_function *)
  - admit.
  (* step_return_1 *)
  - admit.
  (* step_returnstate *)
  - admit.
  (* step_seq *)
  - admit.
  (* step_skip_seq *)
  - admit.
  (* step_continue_insert_drops *)    
  - admit.
  (* step_break_insert_drops *)    
  - admit.
  (* step_ifthenelse *)
  - admit.
  (* step_loop *)
  - admit.
  (* steP_skip_loop *)
  - admit.
  Admitted. 

(* Theorem transl_program_correct prog tprog:
   match_prog prog tprog ->
   forward_simulation (cc_rs injp) (cc_rs injp) (semantics prog) (RustIRown.semantics tprog).
Proof.
  fsim eapply forward_simulation_plus. 
  - inv MATCH. auto. 
  - intros. inv MATCH. destruct Hse, H. simpl in *. admit. 
  - admit. 
  - admit.  
  - simpl. admit. 
  - admit. 

    

