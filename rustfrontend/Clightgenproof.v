Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import LanguageInterface.
Require Import AST Linking.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import Clight.
Require Import RustlightBase RustIR.
Require Import Errors.
Require Import Clightgen.
Require Import LanguageInterface cklr.CKLR cklr.Inject cklr.InjectFootprint.

Import ListNotations.

(** Correctness proof for the generation of Clight *)

Variable tr_fundef: RustIR.program -> RustIR.fundef -> Clight.fundef -> Prop.

Variable tr_type: Rusttypes.type -> Ctypes.type -> Prop.

Record match_prog (p: RustIR.program) (tp: Clight.program) : Prop := {
    match_prog_types:
    tp.(Ctypes.prog_types) = transl_composites p.(prog_types);
    match_prog_def:    
    match_program_gen tr_fundef tr_type p p tp;
    match_prog_skel:
    erase_program tp = erase_program p
  }.

Section PRESERVATION.

Variable match_prog: RustIR.program -> Clight.program -> Prop. (* TODO *)

Variable prog: RustIR.program.
Variable tprog: Clight.program.
Hypothesis TRANSL: match_prog  prog tprog.

Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
(* injp or inj ? *)
Variable w: world injp.
Let ge := RustIR.globalenv se prog.
Let tge := Clight.globalenv tse tprog.

(** TODO: Relational specification of the translation. *)

Variable tr_stmt: composite_env -> Ctypes.composite_env -> PTree.t ident -> RustIR.statement -> Clight.statement -> Prop.

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
| match_Kcall1: forall p f tf e te le k tk cty temp pe,
    (* we need to consider temp is set to a Clight expr which is
    translated from p *)
    transl_function ce tce dropm f = OK tf ->
    cty = to_ctype (typeof_place p) ->
    place_to_cexpr tce p = OK pe ->
    match_cont k tk ->
    match_env (mi injp w) e te ->
    match_cont (RustIR.Kcall (Some p) f e k) (Clight.Kcall (Some temp) tf te le (Clight.Kseq (Clight.Sassign pe (Etempvar temp cty)) tk))
| match_Kcall2: forall f tf e te le k tk,
    (* how to relate le? *)
    transl_function ce tce dropm f = OK tf ->
    match_cont k tk ->
    match_cont (RustIR.Kcall None f e k) (Clight.Kcall None tf te le tk)
| match_Kcalldrop: forall id e te le k tk tf co,
    (* Is it correct? *)
    ce ! id = Some co ->
    drop_glue_for_composite ce tce dropm id co.(co_sv) co.(co_members) co.(co_attr)= OK (Some tf) ->
    match_env (mi injp w) e te ->
    match_cont (RustIR.Kcalldrop id e k) (Clight.Kcall None tf te le tk)
.


Inductive match_states: RustIR.state -> Clight.state -> Prop :=
| match_regular_state: forall f tf s ts k tk m tm e te le j Hm,
    (* Ignore the generators here *)
    transl_function ce tce dropm f = OK tf ->
    tr_stmt ce tce dropm s ts ->
    (* match continuation *)
    match_cont k tk ->
    (* we need to consider that tm may contains more block for its call stacks of drop glue *)
    (* use injp_acc ? *)
    injp_acc w (injpw j m tm Hm) ->
    (* local environments are the same? *)
    match_env (mi injp w) e te ->
    match_states (RustIR.State f s k e m) (Clight.State tf ts tk te le tm)
| match_call_state: forall vf vargs k m tvf tvargs tk tm j fd targs tres cconv Hm orgs rels
   (MCONT: match_cont k tk)
   (VINJ: Val.inject j vf tvf)
   (MINJ: injp_acc w (injpw j m tm Hm))
   (AINJ: Val.inject_list j vargs tvargs)
   (VFIND: Genv.find_funct ge vf = Some fd)
   (FUNTY: type_of_fundef fd = Tfunction orgs rels targs tres cconv),
    match_states (RustIR.Callstate vf vargs k m) (Clight.Callstate tvf tvargs tk tm)
| match_return_state: forall v k m tv tk tm j Hm
   (MCONT: match_cont k tk)
   (MINJ: injp_acc w (injpw j m tm Hm))
   (RINJ: Val.inject j v tv),
    match_states (RustIR.Returnstate v k m) (Clight.Returnstate tv tk tm)
| match_calldrop_box: forall p k e m b ofs tk tm ty a j Hm fb
    (* we can store the address of p in calldrop and build a local env
    in Drop state according to this address *)
    (VFIND: Genv.find_def tge fb = Some (Gfun malloc_decl))
    (PTY: typeof_place p = Tbox ty a)
    (PADDR: eval_place ce e m p b ofs)
    (MCONT: match_cont k tk)
    (MINJ: injp_acc w (injpw j m tm Hm)),
    match_states (RustIR.Calldrop p k e m) (Clight.Callstate (Vptr fb Ptrofs.zero) [(Vptr b ofs)] tk tm)
| match_calldrop_composite: forall p k e m b ofs tk tm a j Hm fb id fid drop_glue orgs
    (DROPM: dropm!id = Some fid)
    (VFIND: Genv.find_def tge fb = Some drop_glue)
    (SYMB: Genv.find_symbol tge fid = Some fb)
    (* Is it correct? *)
    (GLUE: In (fid, drop_glue) tprog.(prog_defs))
    (PTY: typeof_place p = Tstruct orgs id a \/ typeof_place p = Tvariant orgs id a)
    (PADDR: eval_place ce e m p b ofs)
    (MCONT: match_cont k tk)
    (MINJ: injp_acc w (injpw j m tm Hm)),
    match_states (RustIR.Calldrop p k e m) (Clight.Callstate (Vptr fb Ptrofs.zero) [(Vptr b ofs)] tk tm)
| match_drop_state: forall id s k e m tf ts tk te le tm j Hm co
    (* How to relate e and te? and le? *)
    (MSTMT: tr_stmt ce tce dropm s ts)
    (MCONT: match_cont k tk)
    (MINJ: injp_acc w (injpw j m tm Hm)),
    ce ! id = Some co ->
    drop_glue_for_composite ce tce dropm id co.(co_sv) co.(co_members) co.(co_attr) = OK (Some tf) ->
    match_states (RustIR.Dropstate id s k e m) (Clight.State tf ts tk te le tm)
.


Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus step2 tge S1' t S2' /\ match_states S2 S2'.
Admitted.

Lemma initial_states_simulation:
  forall q1 q2 S, match_query (cc_c injp) w q1 q2 -> initial_state ge q1 S ->
  exists R, Clight.initial_state tge q2 R /\ match_states S R.
Admitted.

Lemma final_states_simulation:
  forall S R r1, match_states S R -> final_state S r1 ->
  exists r2, Clight.final_state R r2 /\ match_reply (cc_c injp) w r1 r2.
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
