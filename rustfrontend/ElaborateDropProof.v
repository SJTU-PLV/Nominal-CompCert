Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Linking.
Require Import Rusttypes.
Require Import Errors.
Require Import LanguageInterface CKLR Inject InjectFootprint.
Require Import InitDomain InitAnalysis ElaborateDrop.
Require Import Rustlight Rustlightown RustIR RustOp.
Require Import RustIRsem RustIRown RustIRcfg.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope error_monad_scope.

Record match_prog (p tp: RustIR.program) : Prop := {
  match_prog_main:
    tp.(prog_main) = p.(prog_main);
  match_prog_public:
    tp.(prog_public) = p.(prog_public);
  match_prog_skel:
    erase_program tp = erase_program p;
  match_prog_defs:
    list_norepet (prog_defs_names p)
}.

Lemma match_transf_program: forall p tp,
    transl_program p = OK tp ->
    match_prog p tp.
Proof.
  intros. unfold transl_program in H. monadInv H. unfold transform_partial_program in EQ.
  destruct p. simpl in *. unfold transform_partial_program2 in EQ. 
Admitted. 


Section MATCH_PROGRAMS.
Variable p: program.
Variable tp: program.
Hypothesis TRANSL: match_prog p tp.

Section INJECT.

Variable j: meminj.
Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
Hypothesis sematch: Genv.match_stbls j se tse.

Theorem is_internal_match:
  forall v tv (f tf: RustIR.fundef),
  fundef_is_internal tf = fundef_is_internal f ->
  Val.inject j v tv ->
  v <> Vundef ->
  Genv.is_internal (globalenv tse tp) tv = Genv.is_internal (globalenv se p) v.
Proof.
Admitted. 
   
  
End INJECT.
End MATCH_PROGRAMS.


Inductive match_drop_place_state : option drop_place_state -> statement -> Prop :=
| match_dps_none:
  match_drop_place_state None Sskip
| match_dps_comp: forall p l,
    (* step_dropplace_init2 has simulated the drop flag condition
    checking *)
    match_drop_place_state (Some (drop_fully_owned_comp p l)) (Ssequence (Sdrop p) (makeseq (map (fun p => Sdrop p) l)))
| match_dps_box: forall l,
    match_drop_place_state (Some (drop_fully_owned_box l)) (makeseq (map (fun p => Sdrop p) l))
.

(* Because in dropplace state we do not know the pc, so we use own_env
to establish the relation between split drop places and target
statement. This relation should be proved when we enter Dropplace
state *)
Inductive match_split_drop_places flagm : own_env -> list (place * bool) -> statement -> Prop :=
| match_sdp_nil: forall own,
    match_split_drop_places flagm own nil Sskip
| match_sdp_cons_flag: forall p flag own l ts full
    (FLAG: get_dropflag_temp flagm p = Some flag)
    (SPLIT: match_split_drop_places flagm (move_place own p) l ts),
    (* how to ensure that p is owned in own_env *)    
    match_split_drop_places flagm own ((p,full)::l) (Ssequence (generate_drop p full (Some flag)) ts)
| match_sdp_cons_must_init: forall p own l ts full
    (FLAG: get_dropflag_temp flagm p = None)
    (SPLIT: match_split_drop_places flagm (move_place own p) l ts)
    (OWN: is_owned own p = true),
    (* how to ensure that p is owned in own_env *)    
    match_split_drop_places flagm own ((p,full)::l) (Ssequence (generate_drop p full None) ts)
| match_sdp_cons_must_uninit: forall p own l ts full
    (FLAG: get_dropflag_temp flagm p = None)
    (SPLIT: match_split_drop_places flagm (move_place own p) l ts)
    (OWN: is_owned own p = false),
    (* how to ensure that p is owned in own_env *)    
    match_split_drop_places flagm own ((p,full)::l) (Ssequence Sskip ts)
.

 
Section PRESERVATION.

Variable prog: program.
Variable tprog: program.

Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
(* Variable dropflags: PTree.t (list (place * ident)). *)

Let ge := globalenv se prog.
Let tge := globalenv tse tprog.
Let ce := ge.(genv_cenv).

(* analysis result and flag map types *)
Definition AN : Type := (PMap.t PathsMap.t * PMap.t PathsMap.t * PathsMap.t).
Definition FM : Type := PTree.t (list (place * ident)).

Let match_stmt (ae: AN) (flagm: FM) := match_stmt get_init_info ae (elaborate_stmt flagm ce).

(* relation between source env and target env including the own_env
and invariant of flags map *)
Record match_env_flagm (j: meminj) (own: own_env) (e te: env) (m tm: mem) (flagm: FM) : Type :=
  { wf_flagm: forall p id,
      get_dropflag_temp flagm p = Some id ->
      exists tb v, te ! id = Some (tb, type_bool)
              /\ Mem.load Mint8unsigned tm tb 0 = Some (Vint v)
              (* TODO: add a rust bool_val *)
              /\ negb (Int.eq v Int.zero) = is_owned own p
              (* protection *)
              /\ (forall ofs, loc_out_of_reach j m tb ofs)
              /\ e ! id = None;

    match_vars: forall id b ty,
      e ! id = Some (b, ty) ->
      exists tb, te ! id = Some (tb, ty)
            /\ j b = Some (tb, 0);
    
  }.
    

Inductive match_cont (j: meminj) : AN -> FM -> statement -> rustcfg -> cont -> RustIRsem.cont -> node -> option node -> option node -> node -> Prop :=
| match_Kseq: forall an flagm body cfg s ts k tk pc next cont brk nret
    (MSTMT: match_stmt an flagm body cfg s ts pc next cont brk nret)
    (MCONT: match_cont j an flagm body cfg k tk next cont brk nret),
    match_cont j an flagm body cfg (Kseq s k) (RustIRsem.Kseq ts tk) pc cont brk nret
| match_Kstop: forall an flagm body cfg nret
    (RET: cfg ! nret = Some Iend),
    match_cont j an flagm body cfg Kstop RustIRsem.Kstop nret None None nret
| match_Kloop: forall an flagm body cfg s ts k tk body_start loop_jump_node exit_loop nret contn brk
    (START: cfg ! loop_jump_node = Some (Inop body_start))
    (MSTMT: match_stmt an flagm body cfg s ts body_start loop_jump_node (Some loop_jump_node) (Some exit_loop) nret)
    (MCONT: match_cont j an flagm body cfg k tk exit_loop contn brk nret),
    match_cont j an flagm body cfg (Kloop s k) (RustIRsem.Kloop ts tk) loop_jump_node (Some loop_jump_node) (Some exit_loop) nret
| match_Kcall: forall an flagm body cfg k tk nret f tf le tle own p
    (MSTK: match_stacks j (Kcall p f le own k) (RustIRsem.Kcall p tf tle tk))
    (RET: cfg ! nret = Some Iend),
    (* in the end of a function. an and body are not important, those
    in match_stacks are important *)
    match_cont j an flagm body cfg (Kcall p f le own k) (RustIRsem.Kcall p tf tle tk) nret None None nret
| match_Kdropcall: forall an flagm body cfg k tk pc cont brk nret st membs b tb ofs tofs id
    (INJ: Val.inject j (Vptr b ofs) (Vptr tb tofs))
    (MCONT: match_cont j an flagm body cfg k tk pc cont brk nret),
    match_cont j an flagm body cfg (Kdropcall id (Vptr b ofs) st membs k) (RustIRsem.Kdropcall id (Vptr tb tofs) st membs tk) pc cont brk nret
| match_Kdropplace: forall an f tf st l k tk e te own flagm cfg nret cont brk pc ts1 ts2
    (** Do we need match_stacks here?  *)
    (TRFUN: tr_fun f nret cfg)
    (AN: analyze ce f = OK an)
    (MSTK: match_cont j an flagm f.(fn_body) cfg k tk pc cont brk nret)    
    (MDPS: match_drop_place_state st ts1)
    (MSPLIT: match_split_drop_places flagm own l ts2),
    (* source program: from dropplace to droopstate, target: from
    state to dropstate. So Kdropplace matches Kcall *)
    match_cont j an flagm f.(fn_body) cfg (Kdropplace f st l e own k) (RustIRsem.Kcall None tf te (RustIRsem.Kseq (Ssequence ts1 ts2) tk)) pc cont brk nret 
               
with match_stacks (j: meminj) : cont -> RustIRsem.cont -> Prop :=
| match_stacks_stop: match_stacks j Kstop (RustIRsem.Kstop)
| match_stacks_call: forall an flagm f tf nret cfg pc contn brk k tk own p le tle
    (TRFUN: tr_fun f nret cfg)
    (AN: analyze ce f = OK an)
    (** TODO: added constraint to flagm *)
    (MCONT: match_cont j an flagm f.(fn_body) cfg k tk pc contn brk nret),
    match_stacks j (Kcall p f le own k) (RustIRsem.Kcall p tf tle tk)
.

Inductive match_states : state -> RustIRsem.state -> Prop := 
| match_regular_state:
  forall f s k e own m tf ts tk te tm j flagm maybeInit maybeUninit universe cfg nret cont brk next pc
    (AN: analyze ce f = OK (maybeInit, maybeUninit, universe))
    (TRFUN: tr_fun f nret cfg)
    (MSTMT: match_stmt (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg s ts pc next cont brk nret)
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk next cont brk nret)
    (MINJ: Mem.inject j m tm)
    (* well-formedness of the flag map *)
    (WFFM: wf_flagm own te tm flagm),
    match_states (State f s k e own m) (RustIRsem.State tf ts tk te tm)
| match_drppplace: forall f tf st l k tk e te own m tm j flagm  maybeInit maybeUninit universe cfg nret cont brk next ts1 ts2
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk next cont brk nret)    
    (MDPS: match_drop_place_state st ts1)
    (MSPLIT: match_split_drop_places flagm own l ts2)
    (MINJ: Mem.inject j m tm),
    match_states (Dropplace f st l k e own m) (RustIRsem.State tf ts1 (RustIRsem.Kseq ts2 tk) te tm)
| match_dropstate: forall k tk m tm j flagm maybeInit maybeUninit universe body cfg nret cont brk next b ofs tb tofs st membs id
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm body cfg k tk next cont brk nret)
    (MINJ: Mem.inject j m tm)
    (VINJ: Val.inject j (Vptr b ofs) (Vptr tb tofs)),
    match_states (Dropstate id (Vptr b ofs) st membs k m) (RustIRsem.Dropstate id (Vptr tb tofs) st membs tk tm)
| match_callstate: forall j vf tvf m tm vargs tvargs k tk
    (VINJ: Val.inject j vf tvf)
    (MINJ: Mem.inject j m tm)
    (AINJ: Val.inject_list j vargs tvargs)
    (MCONT: match_stacks j k tk),
    match_states (Callstate vf vargs k m) (RustIRsem.Callstate tvf tvargs tk tm)
| match_returnstate: forall j v tv m tm k tk
    (VINJ: Val.inject j v tv)
    (MINJ: Mem.inject j m tm)
    (MCONT: match_stacks j k tk),
    match_states (Returnstate v k m) (RustIRsem.Returnstate tv tk tm)
. 


Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus RustIRsem.step tge S1' t S2' /\ match_states S2 S2'.
Proof. 
  induction 1; intros; inv MS. 
  - eexists. split. eapply plus_one. 
Admitted. 

Lemma transf_initial_states q:
  forall S1, initial_state ge q S1 ->
  exists S2, RustIRsem.initial_state tge q S2 /\ match_states S1 S2.
Proof.
Admitted. 

Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> final_state S1 r -> RustIRsem.final_state S2 r.
Proof.
Admitted. 

Lemma transf_external:
  forall S R q, match_states S R -> at_external ge S q ->
  RustIRsem.at_external tge R q /\
  forall r S', after_external S r S' ->
  exists R', RustIRsem.after_external R r R' /\ match_states S' R'.
Proof.
  intros S R q HSR Hq. destruct Hq; inv HSR.
Qed. 

Lemma transf_fundef_internal: 
forall q se2,
Genv.is_internal (Genv.globalenv se2 tprog) (cq_vf q) =
Genv.is_internal (Genv.globalenv se2 prog) (cq_vf q). 
Admitted. 

End PRESERVATION.

Theorem transl_program_correct prog tprog:
   match_prog prog tprog ->
   forward_simulation (cc_id) (cc_id) (semantics prog) (RustIRsem.semantics tprog).
Proof.
    fsim eapply forward_simulation_plus; simpl in *. 
    - inv MATCH. simpl. auto. 
    - intros. inv H. eapply transf_fundef_internal; eauto. 
    - intros. inv H. eapply transf_initial_states. eauto.  
    - intros. exploit transf_final_states; eauto. 
    - intros. edestruct transf_external; eauto. exists tt, q1. intuition subst; eauto.
    - eauto using step_simulation.
Admitted. 
