Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Linking.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import Clight.
Require Import RustlightBase RustIR RustOp.
Require Import Errors.
Require Import Clightgen Clightgenspec.
Require Import LanguageInterface cklr.CKLR cklr.Inject cklr.InjectFootprint.

Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope gensym_monad_scope.

(** Correctness proof for the generation of Clight *)

Definition match_glob (ctx: clgen_env) gd tgd : Prop :=
  match gd, tgd with
  | Gvar v1, Gvar v2 =>
      match_globvar (fun ty ty' => to_ctype ty = ty') v1 v2
  | Gfun fd1, Gfun fd2 =>
      tr_fundef ctx fd1 fd2
  | _, _ => False
  end.

Record match_prog (p: RustIR.program) (tp: Clight.program) : Prop := {
    match_prog_main:
    tp.(prog_main) = p.(prog_main);
    match_prog_public:
    tp.(prog_public) = p.(prog_public);
    match_prog_comp_env:
    tr_composite_env p.(prog_comp_env) tp.(Ctypes.prog_comp_env);
    match_prog_def:
    (* match_program_gen tr_fundef (fun ty ty' => to_ctype ty = ty') p p tp; *)
    forall id, Coqlib.option_rel (match_glob (build_clgen_env p tp)) ((prog_defmap p)!id) ((prog_defmap tp)!id);
    match_prog_skel:
    erase_program tp = erase_program p;
    match_prog_malloc:
    exists orgs rels tyl rety cc, (prog_defmap p) ! malloc_id = Some (Gfun (Rusttypes.External orgs rels EF_malloc tyl rety cc));
    match_prog_free:
    exists orgs rels tyl rety cc, (prog_defmap p) ! malloc_id = Some (Gfun (Rusttypes.External orgs rels EF_free tyl rety cc));

  }.

(* Prove match_genv for this specific match_prog *)

Section MATCH_PROGRAMS.

Variable p: RustIR.program.
Variable tp: Clight.program.
Let build_ctx := build_clgen_env p tp.
Hypothesis TRANSL: match_prog p tp.

Section INJECT.

Variable j: meminj.
Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
Hypothesis sematch: Genv.match_stbls j se tse.

Lemma globalenvs_match:
  Genv.match_genvs j (match_glob build_ctx) (Genv.globalenv se p) (Genv.globalenv tse tp).
Proof.
  intros. split; auto. intros. cbn [Genv.globalenv Genv.genv_defs NMap.get].
  assert (Hd:forall i, Coqlib.option_rel (match_glob build_ctx) (prog_defmap p)!i (prog_defmap tp)!i).
  {
    intro. apply TRANSL.
  }
  rewrite !PTree.fold_spec.
  apply PTree.elements_canonical_order' in Hd. revert Hd.
  generalize (prog_defmap p), (prog_defmap tp). intros d1 d2 Hd.
  (*   cut (option_rel match_gd (PTree.empty _)!b1 (PTree.empty _)!b2). *)
  cut (Coqlib.option_rel (match_glob build_ctx)
         (NMap.get _ b1 (NMap.init (option (globdef (Rusttypes.fundef function) type)) None))
         (NMap.get _ b2 (NMap.init (option (globdef (Ctypes.fundef Clight.function) Ctypes.type)) None ))).
  - generalize (NMap.init (option (globdef (Rusttypes.fundef function) type)) None),
      (NMap.init (option (globdef (Ctypes.fundef Clight.function) Ctypes.type)) None).
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
  match_glob (build_ctx) g tg /\
  delta = 0.
Proof.
  apply Genv.find_def_match_genvs, globalenvs_match.
Qed.

Theorem find_funct_match:
  forall v tv f,
  Genv.find_funct (Genv.globalenv se p) v = Some f ->
  Val.inject j v tv ->
  exists tf,
  Genv.find_funct (Genv.globalenv tse tp) tv = Some tf /\ tr_fundef build_ctx f tf.
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
  Genv.find_funct (Clight.globalenv tse tp) tv = None.
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
  (forall c f tf, tr_fundef c f tf ->
   fundef_is_internal tf = fundef_is_internal f) ->
  forall v tv,
    Val.inject j v tv ->
    v <> Vundef ->
    Genv.is_internal (Clight.globalenv tse tp) tv = Genv.is_internal (globalenv se p) v.
Proof.
  intros Hmatch v tv INJ DEF. unfold Genv.is_internal.
  destruct (Genv.find_funct _ v) eqn:Hf.
  - edestruct find_funct_match as (tf & Htf & ?); try eassumption.
    unfold Clight.fundef.
    simpl. rewrite Htf. eauto.
  - erewrite find_funct_none; eauto.
Qed.


End INJECT.

End MATCH_PROGRAMS.

Section PRESERVATION.

Variable prog: RustIR.program.
Variable tprog: Clight.program.
Let ctx := build_clgen_env prog tprog.
Let ce := ctx.(clgen_src_cenv).
Let tce := ctx.(clgen_tgt_cenv).
Let dropm := ctx.(clgen_dropm).
Let glues := ctx.(clgen_glues).

Hypothesis TRANSL: match_prog prog tprog.
Variable w: inj_world.

Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
(* injp or inj ? *)
Hypothesis SEVALID: Genv.valid_for (erase_program prog) se.

Let ge := RustIR.globalenv se prog.
Let tge := Clight.globalenv tse tprog.

Hypothesis GE: inj_stbls w se tse.

(* Simulation relation *)

(* Let ce := prog.(prog_comp_env). *)
(* Let tce := tprog.(Ctypes.prog_comp_env). *)
(* Let dropm := generate_dropm prog. *)
(* Let glues := generate_drops ce tce prog.(prog_types) dropm. *)

Definition var_block_rel (f: meminj) (s: block * type) (t: block * Ctypes.type) : Prop :=
  let (b, ty) := s in
  let (tb, cty) := t in
  f b = Some (tb, 0) /\ cty = to_ctype ty.

Definition match_env (f: meminj) (e: env) (te: Clight.env) : Prop :=
  (* me_mapped in Simpllocalproof.v *)
  forall id, Coqlib.option_rel (var_block_rel f) e!id te!id.
  
Lemma match_env_incr: forall e te j1 j2,
    match_env j1 e te ->
    inject_incr j1 j2 ->
    match_env j2 e te.
Proof.
  unfold match_env.
  intros. generalize (H id). intros REL.
  inv REL. constructor. constructor.
  destruct x. destruct y.
  red. red in H3. destruct H3.
  split; eauto.
Qed.


(* We need to maintain the well-formedness of local environment in the
simulation *)
Definition well_formed_env (f: function) (e: env) : Prop :=
  forall id, ~ In id (var_names f.(fn_vars)) -> e!id = None.

Lemma wf_env_target_none: forall j e te l id f,
    match_env j e te ->
    well_formed_env f e ->
    list_disjoint (var_names (f.(fn_params) ++ f.(fn_vars))) l ->
    In id l ->
    te!id = None.
Proof.
Admitted.

Lemma function_entry_wf_env: forall ge f vargs e m1 m2,
    function_entry ge f vargs m1 e m2 ->
    well_formed_env f e.
Admitted.


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
| match_Kcall1: forall p f tf e te le k tk cty temp pe j
    (WFENV: well_formed_env f e)
    (NORMALF: f.(fn_drop_glue) = None),
    (* we need to consider temp is set to a Clight expr which is
    translated from p *)
    tr_function ce tce dropm glues f tf ->
    cty = to_ctype (typeof_place p) ->
    place_to_cexpr tce p = OK pe ->
    match_cont k tk ->
    match_env j e te ->
    match_cont (RustIR.Kcall (Some p) f e k) (Clight.Kcall (Some temp) tf te le (Clight.Kseq (Clight.Sassign pe (Etempvar temp cty)) tk))
| match_Kcall2: forall f tf e te le k tk
    (WFENV: well_formed_env f e)
    (NORMALF: f.(fn_drop_glue) = None),
    (* how to relate le? *)
    tr_function ce tce dropm glues f tf ->
    match_cont k tk ->
    match_cont (RustIR.Kcall None f e k) (Clight.Kcall None tf te le tk)
| match_Kcalldrop: forall id e te le k tk tf j,
    (* Is it correct? *)
    (* ce ! id = Some co -> *)
    (* Use PTree.fold in generate_drops instead of fold right ? *)
    glues ! id = Some tf ->
    (* drop_glue_for_composite ce tce dropm id co.(co_sv) co.(co_members) co.(co_attr) = Some tf -> *)
    match_env j e te ->
    match_cont (RustIR.Kcalldrop id empty_env k) (Clight.Kcall None tf te le tk)
.


Inductive match_states: RustIR.state -> Clight.state -> Prop :=
| match_regular_state: forall f tf s ts k tk m tm e te le j
    (WFENV: well_formed_env f e)
    (* maintain that this function is a normal function *)
    (NORMALF: f.(fn_drop_glue) = None)
    (MFUN: tr_function ce tce dropm glues f tf)
    (MSTMT: tr_stmt ce tce dropm s ts)    
    (* match continuation *)
    (MCONT: match_cont k tk)
    (MINJ: Mem.inject j m tm)   
    (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm)))
    (MENV: match_env j e te),
    match_states (RustIR.State f s k e m) (Clight.State tf ts tk te le tm)
| match_call_state: forall vf vargs k m tvf tvargs tk tm j
    (* match_kcall is independent of ce and dropm  *)
    (MCONT: match_cont k tk)
    (VINJ: Val.inject j vf tvf)
    (MINJ: Mem.inject j m tm)
    (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm)))
    (AINJ: Val.inject_list j vargs tvargs),
    (* (VFIND: Genv.find_funct ge vf = Some fd) *)
    (* (FUNTY: type_of_fundef fd = Tfunction orgs rels targs tres cconv), *)
    match_states (RustIR.Callstate vf vargs k m) (Clight.Callstate tvf tvargs tk tm)
| match_return_state: forall v k m tv tk tm j
   (MCONT: match_cont k tk)
   (MINJ: Mem.inject j m tm)
   (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm)))
   (RINJ: Val.inject j v tv),
    match_states (RustIR.Returnstate v k m) (Clight.Returnstate tv tk tm)
| match_calldrop_box: forall p k e m b ofs tk tm ty j fb
    (* we can store the address of p in calldrop and build a local env
       in Drop state according to this address *)
    (VFIND: Genv.find_def tge fb = Some (Gfun malloc_decl))
    (PTY: typeof_place p = Tbox ty)
    (PADDR: eval_place ce e m p b ofs)
    (MCONT: match_cont k tk)
    (MINJ: Mem.inject j m tm)
    (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm))),
    match_states (RustIR.Calldrop p k e m) (Clight.Callstate (Vptr fb Ptrofs.zero) [(Vptr b ofs)] tk tm)
| match_calldrop_composite: forall p k e m b ofs tk tm j fb id fid drop_glue orgs
    (GLUE: glues ! id = Some drop_glue)
    (DROPM: dropm ! id = Some fid)
    (VFIND: Genv.find_funct tge (Vptr fb Ptrofs.zero) = Some (Ctypes.Internal drop_glue))
    (SYMB: Genv.find_symbol tge fid = Some fb)
    (PTY: typeof_place p = Tstruct orgs id \/ typeof_place p = Tvariant orgs id)
    (PADDR: eval_place ce e m p b ofs)
    (MCONT: match_cont k tk)
    (MINJ: Mem.inject j m tm)
    (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm))),
    match_states (RustIR.Calldrop p k e m) (Clight.Callstate (Vptr fb Ptrofs.zero) [(Vptr b ofs)] tk tm)
| match_drop_state: forall id s k e m tf ts tk te le tm j
      (* How to relate e and te? and le? *)
    (MSTMT: tr_stmt ce tce dropm s ts)
    (MCONT: match_cont k tk)
    (MINJ: Mem.inject j m tm)
    (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm)))
    (GLUE: glues ! id = Some tf),
    match_states (RustIR.Dropstate id s k e m) (Clight.State tf ts tk te le tm)
.

(* Type preservation in translation *)

Lemma place_to_cexpr_type: forall p e,
    place_to_cexpr tce p = OK e ->
    to_ctype (typeof_place p) = Clight.typeof e.
Admitted.

Lemma expr_to_cexpr_type: forall e e',
    expr_to_cexpr ce tce e = OK e' ->
    to_ctype (typeof e) = Clight.typeof e'.
Proof.  
Admitted.


(* Injection is preserved during evaluation *)

Lemma eval_expr_inject: forall e te j a a' m tm v le,
    expr_to_cexpr ce tce a = OK a' ->
    eval_expr ce e m a v ->
    match_env j e te ->
    Mem.inject j m tm ->
    exists v', Clight.eval_expr tge te le tm a' v' /\ Val.inject j v v'.
(* To prove this lemma, we need to support type checking in the
   evaluation of expression in RustIR *)
Admitted.

Lemma eval_place_inject: forall e te j p lv m tm le b ofs,
    place_to_cexpr tce p = OK lv ->
    eval_place ce e m p b ofs ->
    match_env j e te ->
    Mem.inject j m tm ->
    (** Why eval_lvalue requires tge ? Because eval_Evar_global ! We
    want to just use ctce. But I think we can prove that ctce!id =
    tge.(cenv)!id because we have ce!id and tr_composte ce tge.(cenv)
    and tr_composite ce ctce *)
    exists b' ofs', Clight.eval_lvalue tge te le tm lv b' ofs' Full /\ Val.inject j (Vptr b ofs) (Vptr b' ofs').
Admitted.


Lemma assign_loc_inject: forall f ty m loc ofs v m' tm loc' ofs' v',
    assign_loc ge ty m loc ofs v m' ->
    Val.inject f (Vptr loc ofs) (Vptr loc' ofs') ->
    Val.inject f v v' ->
    Mem.inject f m tm ->
    exists f' tm',
      Clight.assign_loc tge (to_ctype ty) tm loc' ofs' Full v' tm'
      /\ Mem.inject f' m' tm'
      /\ inj_incr (injw f (Mem.support m) (Mem.support tm)) (injw f' (Mem.support m') (Mem.support tm')).
Admitted.

Lemma sem_cast_to_ctype_inject: forall f v1 v1' v2 t1 t2 m,
    sem_cast v1 t1 t2 = Some v2 ->
    Val.inject f v1 v1' ->
    exists v2', Cop.sem_cast v1' (to_ctype t1) (to_ctype t2) m = Some v2' /\ Val.inject f v2 v2'.
Admitted.

(* use injp_acc to prove inj_incr *)
Lemma injp_acc_inj_incr: forall f f' m1 m2 m1' m2' Hm Hm',
          injp_acc (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm') ->
          inj_incr (injw f (Mem.support m1) (Mem.support m2)) (injw f' (Mem.support m1') (Mem.support m2')).
Proof.
  intros. inv H.
  econstructor. eauto.
  red. red in H13. unfold Mem.valid_block in H13. eauto.
  eapply (Mem.unchanged_on_support _ _ _ H10).
  eapply (Mem.unchanged_on_support _ _ _ H11).
Qed.


Remark list_cons_neq: forall A (a: A) l, a :: l <> l.
Proof.
  intros. induction l. intro. congruence.
  intro. inv H.  congruence.
Qed.

Lemma initial_states_simulation:
  forall q1 q2 S, match_query (cc_c inj) w q1 q2 -> initial_state ge q1 S ->
             exists R, Clight.initial_state tge q2 R /\ match_states S R.
Proof.
  intros ? ? ? Hq HS.
  inversion Hq as [vf1 vf2 sg vargs1 vargs2 m1 m2 Hvf Hvargs Hm Hvf1]. clear Hq.
  subst. 
  inversion HS. clear HS. subst vf sg vargs m.
  exploit find_funct_match;eauto. eapply inj_stbls_match. eauto. eauto.
  intros (tf & FIND & TRF).
  (* inversion TRF to get tf *)
  inv TRF.
  eexists. split.
  - assert (SIG: signature_of_type targs tres tcc = Ctypes.signature_of_type (to_ctypelist targs) (to_ctype tres) tcc) by admit.
    rewrite SIG. econstructor. eauto.
    (* type of function *) admit.
    (* val_casted_list *) admit.
    (* sup include *) admit.
  - econstructor; eauto. econstructor.
    inv Hm. simpl. reflexivity.
Admitted.

Lemma function_entry_inject:
  forall f tf m1 m2 tm1 j1 vargs tvargs e
    (VARS:  Clight.fn_vars tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_vars))
    (PARAMS: Clight.fn_params tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_params)),
    function_entry ge f vargs m1 e m2 ->
    Mem.inject j1 m1 tm1 ->
    Val.inject_list j1 vargs tvargs ->
    exists j2 te tm2,
      Clight.function_entry1 tge tf tvargs tm1 te (create_undef_temps (fn_temps tf)) tm2
      /\ match_env j2 e te
      /\ Mem.inject j2 m2 tm2
      /\ inj_incr (injw j1 (Mem.support m1) (Mem.support tm1)) (injw j2 (Mem.support m2) (Mem.support tm2)).
Admitted.

    

Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus step1 tge S1' t S2' /\ match_states S2 S2'.
Proof.
  unfold build_clgen_env in *. unfold ctx in *. simpl in *.
  induction 1; intros; inv MS.
          
  (* assign *)
  - inv MSTMT. simpl in H3.
    monadInv_comb H3.
    (* eval place and expr *)       
    exploit eval_place_inject;eauto. instantiate (1:= le0).
    intros (b' & ofs' & EL & INJL).
    exploit eval_expr_inject; eauto. instantiate (1:= le0).
    intros (v' & ER & INJV1).
    exploit sem_cast_to_ctype_inject; eauto. instantiate (1 := tm).
    intros (v1' & CASTINJ & INJV2).
    exploit assign_loc_inject. eauto. eauto. eapply INJV2. eauto.
    intros (j2 & tm2 & TASS & INJA & INCR2).
    erewrite place_to_cexpr_type in *;eauto.
    erewrite expr_to_cexpr_type in *;eauto.
    eexists. split.
    (* step *)
    + eapply plus_one.
      eapply Clight.step_assign;eauto.
      (* Other proof strategy for sem_cast:
         1. type equal between lhs and rhs
         2. evaluation of well typed expression produces casted value (val_casted)
         3. use cast_val_casted *)
    (* match state *)
    + assert (INCR3: inj_incr w (injw j2 (Mem.support m2) (Mem.support tm2))).
      etransitivity. eauto. eauto.      
      eapply match_regular_state;eauto.
      econstructor. simpl. instantiate (1 := g). eauto.
      eapply match_env_incr;eauto. inv INCR2. auto.
      
  (* assign_variant *)
  - inv MSTMT. simpl in H9.
    monadInv_comb H9.
    unfold transl_assign_variant in EQ2.
    rename H4 into SENUM.
    unfold ge in SENUM. simpl in SENUM. fold ce in SENUM.
    rewrite SENUM in EQ2.
    destruct (co_sv co) eqn: SCV; [inv EQ2|].
    rename H5 into TAG. rewrite TAG in EQ2. 
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
  - inv MSTMT. simpl in H7.
    monadInv_sym H7. unfold gensym in EQ. inv EQ.    
    monadInv_comb EQ0.
    destruct g. simpl in H9. inv H9. eapply list_cons_neq in H8.
    contradiction.
    unfold transl_Sbox in H11. monadInv H11.
    destruct andb eqn: ANDB in EQ0;try congruence.
    eapply andb_true_iff in ANDB. destruct ANDB as (SZGT & SZLT).
    eapply Z.leb_le in SZGT. eapply Z.leb_le in SZLT.
    inv EQ0.
    (* find_symbol malloc = Some b *)
    destruct (match_prog_malloc _ _ TRANSL) as (orgs & rels & tyl & rety & cc & MALLOC).    
    exploit Genv.find_def_symbol. eauto. intros A.
    eapply A in MALLOC as (mb & FINDSYMB & FINDMALLOC). clear A.    
    edestruct @Genv.find_symbol_match as (tmb & Htb & TFINDSYMB).
    eapply inj_stbls_match. eauto. eauto.
    (* find_funct tge tb = Some malloc_decl *)
    assert (TFINDFUN: Genv.find_funct tge (Vptr tmb Ptrofs.zero) = Some malloc_decl).
    { edestruct find_funct_match as (malloc & TFINDFUN & TRMALLOC).
      eauto. 
      eapply inj_stbls_match. eauto.
      instantiate (2 := (Vptr mb Ptrofs.zero)). simpl.
      destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff. eauto.
      econstructor. eauto. eauto.
      erewrite Ptrofs.add_zero_l in TFINDFUN. unfold tge.
      inv TRMALLOC. eauto. intuition. }
    (* mem alloc in target *)
    exploit Mem.alloc_parallel_inject. eapply MINJ.
    eauto. eapply Z.le_refl. eapply Z.le_refl. 
    intros (j2 & tm2 & tb & TALLOC & INJ2 & INCR2 & A & B).
    cut (match_env j2 le te).
    2: { eapply match_env_incr;eauto. }
    intros MENV2.
    (* store in malloc *)
    exploit Mem.store_mapped_inject. eapply INJ2. eauto.
    eapply A. instantiate (1:= (Vptrofs (Ptrofs.repr (sizeof ge (typeof e))))).
    econstructor. rewrite Z.add_0_r.
    intros (tm3 & STORE & INJ3).
    (* evaluate the expression which is stored in the malloc pointer *)
    exploit eval_expr_inject. eauto. eauto.
    eapply match_env_incr. eapply match_env_incr.
    eauto. eauto. eauto. eauto.
    instantiate (1:= (set_opttemp (Some temp) (Vptr tb Ptrofs.zero) le0)).
    intros (tv & EXPR & VINJ). 
    (* sem_cast *)
    exploit sem_cast_to_ctype_inject. eauto. eauto. instantiate (1 := tm3).
    intros (tv1 & CAST1 & INJCAST).
    (* assign_loc for *temp *)
    exploit assign_loc_inject. eapply H4. instantiate (3 := j2).
    econstructor;eauto. eauto. eauto.
    rewrite Ptrofs.add_zero_l.
    intros (j3 & tm4 & ASSIGNLOC1 & INJ4 & INCR3).
    cut (match_env j3 le te).
    2: { eapply match_env_incr;eauto. inv INCR3. eauto. }
    intros MENV3.
    (* eval_lvalue lhs *)
    exploit eval_place_inject. eauto. eauto.
    eauto. eauto.
    instantiate (1 := (set_opttemp (Some temp) (Vptr tb Ptrofs.zero) le0)).
    intros (tpb & tpofs & ELHS & VINJ3).
    (* assign_loc for lhs *)
    exploit assign_loc_inject. eapply H6. instantiate (3 := j3).
    eauto. 
    econstructor. inv INCR3. eapply H12. eauto. eauto.
    eauto. rewrite Ptrofs.add_zero_l.
    intros (j4 & tm5 & ASSIGNLOC2 & INJ5 & INCR4).
    cut (match_env j4 le te).
    2: { eapply match_env_incr;eauto. inv INCR4. eauto. }
    intros MENV4.
    
    eexists. split.
    + econstructor. econstructor. eapply star_step.
      econstructor. eapply star_left.
      (* step_call to malloc *)
      { eapply Clight.step_call.
        * simpl. eauto.
        * eapply eval_Elvalue. eapply eval_Evar_global.
          (* We have to ensure that e!malloc_id = None *)
          eapply wf_env_target_none; eauto. simpl. auto.
          inv MFUN; try congruence.
          eauto. simpl. eauto.
          eauto.
          simpl. eapply Clight.deref_loc_reference. auto.
        * repeat econstructor.
        * eauto.          
        * auto. }
      eapply star_step.
      (* evaluate malloc *)
      { eapply Clight.step_external_function.
        eauto.
        econstructor. erewrite Ptrofs.unsigned_repr; try lia.
        (* alloc *)
        instantiate (1 := tb).
        erewrite <- TALLOC. f_equal. symmetry.
        eapply to_ctype_sizeof. eapply expr_to_cexpr_type;eauto.
        eapply TRANSL.
        (* store sz *)        
        erewrite <- STORE. repeat f_equal. symmetry.
        eapply to_ctype_sizeof. eapply expr_to_cexpr_type;eauto.
        eapply TRANSL. }
      eapply star_step.
      (* returnstate to regular state *)
      eapply Clight.step_returnstate.
      eapply star_step.
      eapply Clight.step_skip_seq.
      eapply star_step.
      (* assign to the malloc pointer *)
      { eapply Clight.step_assign.
        eapply eval_Ederef. eapply eval_Etempvar.
        simpl. eapply PTree.gss.
        eauto.
        (* sem_cast in C side *)
        erewrite <- CAST1. rewrite H. f_equal. symmetry.
        eapply expr_to_cexpr_type;eauto.
        rewrite H. eauto. }
      eapply star_step.
      eapply Clight.step_skip_seq.
      eapply star_one.
      (* assign temp to p *)
      { eapply Clight.step_assign.
        eauto.
        econstructor. eapply PTree.gss.
        instantiate (1 := (Vptr tb Ptrofs.zero)).
        erewrite <- (place_to_cexpr_type p lhs). rewrite H. simpl.
        eapply cast_val_casted. econstructor.
        eauto.
        erewrite <- (place_to_cexpr_type p lhs). eauto.
        auto. }
      1-8: eauto.
    (* match_states *)
    + econstructor; eauto.
      econstructor. simpl. eauto.
      exploit Mem.support_alloc. eapply H0. intros SUPM2.
      exploit Mem.support_alloc. eapply TALLOC. intros SUPTM2.      
      etransitivity. eauto.
      etransitivity. instantiate (1 := injw j2 (Mem.support m2) (Mem.support tm2)).
      eapply injp_acc_inj_incr. eapply injp_acc_alloc;eauto.
      exploit Mem.support_store. eapply H1.
      exploit Mem.support_store. eapply STORE. intros S1 S2.
      rewrite <- S1. rewrite <- S2.
      etransitivity. eauto. eauto.
            
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
    assert (MSTBL: Genv.match_stbls j se tse). {   
      destruct w. inv GE. simpl in *. inv INCR. 
      eapply Genv.match_stbls_incr; eauto. 
      (* disjoint *)
      intros. exploit H7; eauto. intros (A & B). split; eauto. }
    
    edestruct find_funct_match as (tfd & FINDT & TF); eauto.
    inv TF. inv H1;try congruence.

    (* function entry inject *)
    exploit function_entry_inject; eauto.
    intros (j' & te & tm' & TENTRY & MENV1 & MINJ1 & INCR1).
    exists (Clight.State tf tf.(Clight.fn_body) tk te (create_undef_temps (fn_temps tf)) tm').
    (* step and match states *)
    split.
    + eapply plus_one. econstructor;eauto.
    + econstructor; eauto.
      (* initial env is well_formed *)
      eapply function_entry_wf_env. eauto.
      eapply tr_function_normal;eauto.
      etransitivity;eauto.
      
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

    
Lemma final_states_simulation:
  forall S R r1, match_states S R -> final_state S r1 ->
  exists r2, Clight.final_state R r2 /\ match_reply (cc_c inj) w r1 r2.
Admitted.

Lemma external_states_simulation:
  forall S R q1, match_states S R -> at_external ge S q1 ->
  exists wx q2, Clight.at_external tge R q2 /\ cc_c_query inj wx q1 q2 /\ match_stbls inj wx se tse /\
  forall r1 r2 S', match_reply (cc_c inj) wx r1 r2 -> after_external S r1 S' ->
  exists R', Clight.after_external R r2 R' /\ match_states S' R'.
Admitted.


End PRESERVATION.

Theorem transl_program_correct prog tprog:
  match_prog prog tprog ->
  forward_simulation (cc_c inj) (cc_c inj) (RustIR.semantics prog) (Clight.semantics1 tprog).
Proof.
  fsim eapply forward_simulation_plus. 
  - inv MATCH. auto.
  - intros. destruct Hse, H. simpl.
    eapply is_internal_match. eapply MATCH.
    eauto.
    (* tr_fundef relates internal function to internal function *)
    intros. inv H3;auto.
    auto. auto.
  (* initial state *)
  - eapply initial_states_simulation; eauto. 
  (* final state *)
  - eapply final_states_simulation; eauto.
  (* external state *)
  - eapply external_states_simulation; eauto.
  (* step *)
  - eapply step_simulation;eauto.
Qed.
