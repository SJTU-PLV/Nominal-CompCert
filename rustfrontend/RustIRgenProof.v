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
    list_forall2 (fun '(id1, gd) '(id2, tgd) => id1 = id2 /\ match_glob p.(prog_comp_env) gd tgd) p.(prog_defs) tp.(prog_defs);
    match_dropm:
    generate_dropm p = RustIR.generate_dropm tp;
    match_prog_skel:
    erase_program tp = erase_program p;
  }.


Section PRESERVATION.


Variable prog: program.
Variable tprog: RustIR.program.

Hypothesis TRANSL: match_prog prog tprog.

Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
(* Variable dropflags: PTree.t (list (place * ident)). *)

Let ge := globalenv se prog.
Let tge := RustIR.globalenv tse tprog.

Inductive match_drop_insert_kind: drop_insert_kind -> RustIR.statement -> Prop :=
| match_drop_reassign: forall p,
    match_drop_insert_kind (drop_reassign p) (gen_drop ge p)
| match_drop_escape: forall l,
    match_drop_insert_kind (drop_escape l) (gen_drops_for_escape_vars ge l)
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
    (DROP: drop = gen_drop ge (Plocal id ty)),
    (* when executing Klet, Rustlight would enter Dropinsert state
    where drop_escape contains the out-of-scope variable which is
    related to (drop;storagedead id) *)
    match_cont params (Klet id ty k) (RustIRown.Kseq (RustIR.Ssequence drop (Sstoragedead id)) tk)
(* The drops are inserted for the reassignment. The translated
statement does not contain storagedead *)
| match_Kdropinsert: forall k tk dk s1 s2 st
    (MCONT: match_cont params k tk)
    (MDCONT: match_dropcont dk s2)
    (MDINS: match_drop_insert_kind st s1),
    match_cont params (Kdropinsert st dk k)
      (RustIRown.Kseq (RustIR.Ssequence s1 s2) tk)
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


Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus RustIRown.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
  - simpl.
    eexists. split.
    (* step *)
    econstructor. econstructor.
    eapply star_refl. auto.
    econstructor; auto.
    unfold gen_drop, gen_drops.
    destruct (own_type (prog_comp_env prog) (typeof_place p)); auto.
    econstructor.
    
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

    

