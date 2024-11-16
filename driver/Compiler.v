(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** The whole compiler and its proof of semantic preservation *)

(** Libraries. *)
Require Import String.
Require Import Coqlib Errors.
Require Import AST Linking Smallstep.

(** Simulation convention algebra *)
Require Import LanguageInterface.
Require Import Invariant.
Require Import CallconvAlgebra.
Require Import CKLR.
Require Import CKLRAlgebra.
Require Import Inject.
Require Import InjectFootprint.
Require Import Extends.
Require Import Clightrel.
Require Import RTLrel.
Require Import Asmrel.
Require Import ValueAnalysis.
Require Import Conventions.
Require Import CallConv.
Require Import CA RA.

(** Languages (syntax and semantics). *)
Require Ctypes Csyntax Csem Cstrategy (*Cexec*).
Require Clight.
Require Csharpminor.
Require Cminor.
Require CminorSel.
Require RTL.
Require LTL.
Require Linear.
Require Mach.
Require Asm.
(** Translation passes. *)
Require Initializers.
Require SimplExpr.
Require SimplLocals.
Require Cshmgen.
Require Cminorgen.
Require Selection.
Require RTLgen.
Require Tailcall.
Require Inlining.
Require Renumber.
Require Constprop.
Require CSE.
Require Deadcode.
Require Unusedglob.
Require Allocation.
Require Tunneling.
Require Linearize.
Require CleanupLabels.
Require Debugvar.
Require Stacking.
Require Asmgen.
(** Proofs of semantic preservation. *)
Require SimplExprproof.
Require SimplLocalsproof.
Require Cshmgenproof.
Require Cminorgenproof.
Require Selectionproof.
Require RTLgenproof.
Require Tailcallproof.
Require Inliningproof.
Require Renumberproof.
Require Constpropproof.
Require CSEproof.
Require Deadcodeproof.
Require Unusedglobproof.

Require Allocproof.
Require Tunnelingproof.
Require Linearizeproof.
Require CleanupLabelsproof.
Require Debugvarproof.
Require Stackingproof.
Require Asmgenproof.
(** Command-line flags. *)
Require Import Compopts.

(** Rust frontend *)
Require Import Rusttypes.
Require Rustsyntax.
Require Rustlight.
Require RustIR.

Require Rustlightgen.
Require RustIRgen.
Require InitAnalysis.
Require ElaborateDrop.
(* Require BorrowCheckPolonius. *)
Require Clightgen.

(** Proof of Rust frontend  *)
Require RustIRgenProof.
Require Clightgenproof.
Require ElaborateDropProof.

(** Pretty-printers (defined in Caml). *)
Parameter print_Clight: Clight.program -> unit.
Parameter print_Cminor: Cminor.program -> unit.
Parameter print_RTL: Z -> RTL.program -> unit.
Parameter print_LTL: LTL.program -> unit.
Parameter print_Mach: Mach.program -> unit.

Local Open Scope string_scope.

(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a !@@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.

Definition total_if {A: Type}
          (flag: unit -> bool) (f: A -> A) (prog: A) : A :=
  if flag tt then f prog else prog.

Definition partial_if {A: Type}
          (flag: unit -> bool) (f: A -> res A) (prog: A) : res A :=
  if flag tt then f prog else OK prog.

(** We define three translation functions for whole programs: one
  starting with a C program, one with a Cminor program, one with an
  RTL program.  The three translations produce Asm programs ready for
  pretty-printing and assembling. *)

Definition transf_rtl_program (f: RTL.program) : res Asm.program :=
   OK f
  !@@ print (print_RTL 0)
  !@@ total_if Compopts.optim_tailcalls (time "Tail calls" Tailcall.transf_program)
  !@@ print (print_RTL 1)
  @@@ time "Inlining" Inlining.transf_program
  !@@ print (print_RTL 2)
  !@@ time "Renumbering" Renumber.transf_program
  !@@ print (print_RTL 3)
  !@@ total_if Compopts.optim_constprop (time "Constant propagation" Constprop.transf_program)
  !@@ print (print_RTL 4)
  !@@ total_if Compopts.optim_constprop (time "Renumbering" Renumber.transf_program)
  !@@ print (print_RTL 5)
  @@@ partial_if Compopts.optim_CSE (time "CSE" CSE.transf_program)
  !@@ print (print_RTL 6)
  @@@ partial_if Compopts.optim_redundancy (time "Redundancy elimination" Deadcode.transf_program)
  !@@ print (print_RTL 7)
  @@@ time "Unused globals" Unusedglob.transform_program
  !@@ print (print_RTL 8)
  @@@ time "Register allocation" Allocation.transf_program
  !@@ print print_LTL
  !@@ time "Branch tunneling" Tunneling.tunnel_program
  @@@ time "CFG linearization" Linearize.transf_program
  !@@ time "Label cleanup" CleanupLabels.transf_program
  @@@ partial_if Compopts.debug (time "Debugging info for local variables" Debugvar.transf_program)
  @@@ time "Mach generation" Stacking.transf_program
  !@@ print print_Mach
  @@@ time "Asm generation" Asmgen.transf_program.

Definition transf_cminor_program (p: Cminor.program) : res Asm.program :=
   OK p
  !@@ print print_Cminor
  @@@ time "Instruction selection" Selection.sel_program
  @@@ time "RTL generation" RTLgen.transl_program
  @@@ transf_rtl_program.

Definition transf_clight_program (p: Clight.program) : res Asm.program :=
  OK p
  !@@ print print_Clight
  @@@ time "Simplification of locals" SimplLocals.transf_program
  @@@ time "C#minor generation" Cshmgen.transl_program
  @@@ time "Cminor generation" Cminorgen.transl_program
  @@@ transf_cminor_program.

Definition transf_c_program (p: Csyntax.program) : res Asm.program :=
  OK p
  @@@ time "Clight generation" SimplExpr.transl_program
  @@@ transf_clight_program.

(** Force [Initializers] and [Cexec] to be extracted as well. *)


Definition transl_init := Initializers.transl_init.
(* Definition cexec_do_step := Cexec.do_step.
*)

(** * Rust frontend compiler  *)

Definition transf_rust_program (p: Rustsyntax.program) : res Asm.program :=
  OK p
  @@@ time "Rustsyntax to Rustlight" Rustlightgen.transl_program
  !@@ time "Rustlight to RustIR" RustIRgen.transl_program
  @@@ time "Elaborate drop in RustIR" ElaborateDrop.transl_program
  (** The move checking and borrow checking are not verified yet *)
  (* @@@ time "Replace origins in RustIR" ReplaceOrigins.transl_program *)
  (* @@@ time "Borrow check" (fun p => match BorrowCheckPolonius.borrow_check_program p with *)
  (*                                | OK _ => OK p *)
  (*                                | Error msg => Error msg *)
  (*                                end) *)
  @@@ time "Generate Clight and insert drop glue" Clightgen.transl_program
  @@@ transf_clight_program.

(* For ownership language, we just consider Rustlight as the source
language and remove the borrow checking passes. This compilation is
verified. *)
Definition transf_rustlight_program (p: Rustlight.program) : res Asm.program :=
  OK p
  !@@ time "Rustlight to RustIR" RustIRgen.transl_program
  @@@ time "Elaborate drop in RustIR" ElaborateDrop.transl_program
  @@@ time "Generate Clight and insert drop glue" Clightgen.transl_program
  @@@ transf_clight_program.


(** The following lemmas help reason over compositions of passes. *)

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. destruct (printer prog); auto.
Qed.

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit),
  x !@@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto.
Qed.

(** * Relational specification of compilation *)

Definition match_if {A: Type} (flag: unit -> bool) (R: A -> A -> Prop): A -> A -> Prop :=
  if flag tt then R else eq.

Lemma total_if_match:
  forall (A: Type) (flag: unit -> bool) (f: A -> A) (rel: A -> A -> Prop) (prog: A),
  (forall p, rel p (f p)) ->
  match_if flag rel prog (total_if flag f prog).
Proof.
  intros. unfold match_if, total_if. destruct (flag tt); auto.
Qed.

Lemma partial_if_match:
  forall (A: Type) (flag: unit -> bool) (f: A -> res A) (rel: A -> A -> Prop) (prog tprog: A),
  (forall p tp, f p = OK tp -> rel p tp) ->
  partial_if flag f prog = OK tprog ->
  match_if flag rel prog tprog.
Proof.
  intros. unfold match_if, partial_if in *. destruct (flag tt). auto. congruence.
Qed.

Global Instance TransfIfLink {A: Type} {LA: Linker A}
                      (flag: unit -> bool) (transf: A -> A -> Prop) (TL: TransfLink transf)
                      : TransfLink (match_if flag transf).
Proof.
  unfold match_if. destruct (flag tt).
- auto.
- red; intros. subst tp1 tp2. exists p; auto.
Qed.

(** This is the list of compilation passes of CompCert in relational style.
  Each pass is characterized by a [match_prog] relation between its
  input code and its output code.  The [mkpass] and [:::] combinators,
  defined in module [Linking], ensure that the passes are composable
  (the output language of a pass is the input language of the next pass)
  and that they commute with linking (property [TransfLink], inferred
  by the type class mechanism of Coq). *)

Local Open Scope linking_scope.

Definition CompCertO's_passes :=
      mkpass SimplLocalsproof.match_prog
  ::: mkpass Cshmgenproof.match_prog
  ::: mkpass Cminorgenproof.match_prog
  ::: mkpass Selectionproof.match_prog
  ::: mkpass RTLgenproof.match_prog
  ::: mkpass (match_if Compopts.optim_tailcalls Tailcallproof.match_prog)
  ::: mkpass Inliningproof.match_prog
  ::: mkpass Renumberproof.match_prog
  ::: mkpass (match_if Compopts.optim_constprop Constpropproof.match_prog)
  ::: mkpass (match_if Compopts.optim_constprop Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.optim_CSE CSEproof.match_prog)
  ::: mkpass (match_if Compopts.optim_redundancy Deadcodeproof.match_prog)
  ::: mkpass Unusedglobproof.match_prog
  ::: mkpass Allocproof.match_prog
  ::: mkpass Tunnelingproof.match_prog
  ::: mkpass Linearizeproof.match_prog
  ::: mkpass CleanupLabelsproof.match_prog
  ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
  ::: mkpass Stackingproof.match_prog
  ::: mkpass Asmgenproof.match_prog
  ::: pass_nil _.

Definition CompCertO's_passes_rust :=
  mkpass RustIRgenProof.match_prog
    ::: mkpass ElaborateDropProof.match_prog
    ::: mkpass Clightgenproof.match_prog
    ::: CompCertO's_passes.

(** Composing the [match_prog] relations above, we obtain the relation
  between CompCert C sources and Asm code that characterize CompCert's
  compilation. *)

Definition match_prog: Clight.program -> Asm.program -> Prop :=
  pass_match (compose_passes CompCertO's_passes).

Definition match_prog_rust: Rustlight.program -> Asm.program -> Prop :=
  pass_match (compose_passes CompCertO's_passes_rust).

(** For CompCertO we are mostly interested in using Clight as a source
  language, however we can still prove a correctness theorem for CompCert C. *)

Definition CompCert's_passes :=
  mkpass SimplExprproof.match_prog ::: CompCertO's_passes.

Definition match_c_prog: Csyntax.program -> Asm.program -> Prop :=
  pass_match (compose_passes CompCert's_passes).

(** The [transf_c_program] function, when successful, produces
  assembly code that is in the [match_prog] relation with the source C program. *)

Theorem transf_clight_program_match:
  forall p tp,
  transf_clight_program p = OK tp ->
  match_prog p tp.
Proof.
  intros p1 tp T.
  unfold transf_clight_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (SimplLocals.transf_program p1) as [p2|e] eqn:P2; simpl in T; try discriminate.
  destruct (Cshmgen.transl_program p2) as [p3|e] eqn:P3; simpl in T; try discriminate.
  destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
  unfold transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold transf_rtl_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  set (p7 := total_if optim_tailcalls Tailcall.transf_program p6) in *.
  destruct (Inlining.transf_program p7) as [p8|e] eqn:P8; simpl in T; try discriminate.
  set (p9 := Renumber.transf_program p8) in *.
  set (p10 := total_if optim_constprop Constprop.transf_program p9) in *.
  set (p11 := total_if optim_constprop Renumber.transf_program p10) in *.
  destruct (partial_if optim_CSE CSE.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
  destruct (partial_if optim_redundancy Deadcode.transf_program p12) as [p13|e] eqn:P13; simpl in T; try discriminate.
  destruct (Unusedglob.transform_program p13) as [p14|e] eqn:P14; simpl in T; try discriminate.
  destruct (Allocation.transf_program p14) as [p15|e] eqn:P15; simpl in T; try discriminate.
  set (p16 := Tunneling.tunnel_program p15) in *.
  destruct (Linearize.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
  set (p18 := CleanupLabels.transf_program p17) in *.
  destruct (partial_if debug Debugvar.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
  destruct (Stacking.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
  unfold match_prog; simpl.
  exists p2; split. apply SimplLocalsproof.match_transf_program; auto.
  exists p3; split. apply Cshmgenproof.transf_program_match; auto.
  exists p4; split. apply Cminorgenproof.transf_program_match; auto.
  exists p5; split. apply Selectionproof.transf_program_match; auto.
  exists p6; split. apply RTLgenproof.transf_program_match; auto.
  exists p7; split. apply total_if_match. apply Tailcallproof.transf_program_match.
  exists p8; split. apply Inliningproof.transf_program_match; auto.
  exists p9; split. apply Renumberproof.transf_program_match; auto.
  exists p10; split. apply total_if_match. apply Constpropproof.transf_program_match.
  exists p11; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p12; split. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
  exists p13; split. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
  exists p14; split. apply Unusedglobproof.transf_program_match; auto.
  exists p15; split. apply Allocproof.transf_program_match; auto.
  exists p16; split. apply Tunnelingproof.transf_program_match.
  exists p17; split. apply Linearizeproof.transf_program_match; auto.
  exists p18; split. apply CleanupLabelsproof.transf_program_match; auto.
  exists p19; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
  exists p20; split. apply Stackingproof.transf_program_match; auto.
  exists tp; split. apply Asmgenproof.transf_program_match; auto.
  reflexivity.
Qed.

Theorem transf_c_program_match:
  forall p tp,
  transf_c_program p = OK tp ->
  match_c_prog p tp.
Proof.
  intros p tp T.
  unfold transf_c_program, time in T. simpl in T.
  destruct (SimplExpr.transl_program p) as [p1|e] eqn:P1; simpl in T; try discriminate.
  destruct (transf_clight_program p1) as [p2|e] eqn:P2; simpl in T; try discriminate.
  inv T. unfold match_c_prog. cbn -[CompCertO's_passes].
  exists p1; split. apply SimplExprproof.transf_program_match; auto.
  apply transf_clight_program_match; auto.
Qed.

(* Rust compilation chain *)

Theorem transf_rustlight_program_match: forall p tp,
    transf_rustlight_program p = OK tp ->
    match_prog_rust p tp.
Proof.
  intros p tp T.
  unfold transf_rustlight_program, time in T. simpl in T.
  set (p1 := (RustIRgen.transl_program p)) in *.
  destruct (ElaborateDrop.transl_program p1) as [p2|e] eqn: P2; simpl in T; try discriminate.
  destruct (Clightgen.transl_program p2) as [p3|e] eqn: P3; simpl in T; try discriminate.
  unfold match_prog_rust. cbn -[CompCertO's_passes_rust].
  exists p1; split. apply RustIRgenProof.match_transf_program; auto.
  exists p2; split. apply ElaborateDropProof.match_transf_program; auto.
  exists p3; split. apply Clightgenproof.match_transf_program; auto.
  apply transf_clight_program_match; eauto.
Qed.

  
(** * Semantic preservation *)

(** We now prove that the whole CompCert compiler (as characterized by the
  [match_prog] relation) preserves semantics by constructing
  the following simulations:
- Forward simulations from [Cstrategy] to [Asm]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Asm]).
- Backward simulation from [Csem] to [Asm]
  (composition of two backward simulations).
*)

(** Preliminaries: this should be in Coqrel. Alternatively, we could
  define it for [ccref] alone. *)

Instance po_subrel {A} (eqv R: relation A) `{!Equivalence eqv} `{!PreOrder R}:
  PartialOrder eqv R ->
  Related eqv R subrel.
Proof.
  firstorder.
Qed.

(*
Instance po_subrel' {A} (eqv R: relation A) `{!Equivalence eqv} `{!PreOrder R}:
  PartialOrder eqv R ->
  Related eqv (flip R) subrel.
Proof.
  firstorder.
Qed.
*)

(** ** Calling conventions *)

Require Import Conventions Asm Mach Lineartyping.

(** This is the simulation convention for the whole compiler. *)

Definition cc_compcert : callconv li_c li_asm :=
       ro @ wt_c @
       cc_c_asm_injp @
       cc_asm injp.

(** The C-level simulation convention *)
Definition cc_c_level : callconv li_c li_c := ro @ wt_c @ cc_c injp.

Definition cc_compcert_cod : callconv li_c li_asm :=
  ro @ wt_c @ cc_c injp @
       cc_c_locset @ cc_locset_mach @ cc_mach_asm @
       @ cc_asm inj.

Definition cc_compcert_dom : callconv li_c li_asm :=
  ro @ wt_c @  cc_c injp @
       cc_c_locset @ cc_locset_mach @ cc_mach_asm.

Lemma transport_injp_to_asm :
  ccref (ro @ wt_c @ cc_c injp @ cc_c_locset @ cc_locset_mach @ cc_mach_asm @ cc_asm injp @ cc_asm inj)
        cc_compcert_cod.
Proof.
  rewrite (commute_around cc_mach_asm).
  rewrite (commute_around cc_locset_mach).
  rewrite (commute_around cc_c_locset).
  rewrite <- (cc_compose_assoc (cc_c injp)).
  rewrite <- cc_c_compose.
  rewrite injp_injp_eq.
  reflexivity.
Qed.

(** The first expand of cc_compcert for both directions *)
Theorem cc_compcert_merge:
  forall p tp,
  forward_simulation cc_compcert_dom cc_compcert_cod (Clight.semantics1 p) (Asm.semantics tp) ->
  forward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics tp).
Proof.
  intros.
  unfold cc_compcert, cc_compcert_cod, cc_compcert_dom in *.
  rewrite injp__injp_inj_injp at 2. rewrite !cc_asm_compose.
  rewrite <- transport_injp_to_asm in H.
  rewrite <- !cc_compose_assoc.
  eapply compose_forward_simulations.
  rewrite <- cc_injpca_cainjp at 1.
  rewrite cc_cainjp__injp_ca.
  rewrite <- cc_cllmma_ca at 1.
  rewrite cc_ca_cllmma.
  rewrite cc_compose_assoc at 1.
  rewrite !cc_compose_assoc. eauto.
  eapply semantics_asm_rel.
Qed.

(** Derivation of the simulation conventions after C-level at the incoming side *)
Lemma cc_compcert_expand:
  ccref
    cc_compcert_cod
    (cc_c_level @                                          (* Passes up to Alloc *)
     cc_c inj @                                            (* Unusedglob *)
     (wt_c @ cc_c ext @ cc_c_locset) @                     (* Alloc *)
     cc_locset ext @                                       (* Tunneling *)
     (wt_loc @ cc_locset_mach @ cc_mach inj) @             (* Stacking *)
     (cc_mach ext @ cc_mach_asm) @                         (* Asmgen *)
     cc_asm inj).
Proof.
  unfold cc_compcert_cod. unfold cc_c_level.
  rewrite !cc_compose_assoc.
  etransitivity.
  {
    rewrite inj_inj, !cc_asm_compose.
    rewrite inj_inj at 1. rewrite !cc_asm_compose. rewrite cc_compose_assoc.
    rewrite <- lessdef_c_cklr, cc_compose_assoc.
    rewrite <- (cc_compose_assoc wt_c lessdef_c).
    rewrite (inv_dup wt_c), (cc_compose_assoc wt_c), (cc_compose_assoc wt_c).
    rewrite (commute_around (_@_) (R2:= cc_c injp)).
    do 4 rewrite (commute_around _ (R2 := _ inj)).
    reflexivity.
  }
  repeat (rstep; [rauto | ]).
  etransitivity.
  {
    rewrite !cc_compose_assoc.
    rewrite <- ext_inj, !cc_asm_compose.
    rewrite cc_compose_assoc.
    rewrite <- ext_ext at 1. rewrite cc_asm_compose, cc_compose_assoc.
    do 4 rewrite (commute_around cc_mach_asm).
    do 2 rewrite (commute_around cc_locset_mach).
    do 1 rewrite (commute_around cc_c_locset).
    rewrite <- (cc_compose_assoc lessdef_c), lessdef_c_cklr.
    rewrite <- wt_loc_out_of_thin_air, cc_compose_assoc.
    reflexivity.
  }
  reflexivity.
Qed.

(** Derivation of the simulation conventions after C-level at the outgoing side *)
Lemma cc_compcert_collapse:
  ccref
    (cc_c_level @                                 (* Passes up to Alloc *)
     cc_c inj @                                   (* Unusedglob  *)
     (wt_c @ cc_c ext @ cc_c_locset) @            (* Alloc *)
     cc_locset ext @                              (* Tunneling *)
     (wt_loc @ cc_locset injp @ cc_locset_mach) @ (* Stacking *)
     (cc_mach ext @ cc_mach_asm) @
    cc_asm inj)                                   (* Asmgen *)
    cc_compcert_dom.
Proof.
  (* commute the cklrs towards source C level *)
  rewrite <- wt_loc_out_of_thin_air.
  rewrite <- (cc_compose_assoc wt_loc) at 1.
  rewrite <- (cc_compose_assoc (wt_loc @ _)) at 1.
  rewrite (cc_compose_assoc wt_loc) at 1.
  rewrite (inv_drop (cc_locset injp) wt_loc), (cc_compose_assoc _ wt_loc).
  rewrite wt_loc_out_of_thin_air, !cc_compose_assoc.
  assert (ccref (cc_mach_asm @ cc_asm inj) (cc_mach inj @ cc_mach_asm)).
  eapply commut_mach_asm.
  rewrite H.
  rewrite !(commute_around cc_locset_mach).
  rewrite !(commute_around cc_c_locset).
  unfold cc_c_level. rewrite !cc_compose_assoc.

  (* compose the wt_c invaraint using its propagatation property *)
  rewrite <- lessdef_c_cklr, cc_compose_assoc, <- (cc_compose_assoc wt_c) at 1.
  rewrite (commute_around (wt_c @ lessdef_c)), cc_compose_assoc.
  rewrite <- (cc_compose_assoc lessdef_c).
  rewrite lessdef_c_cklr.
  rewrite <- (cc_compose_assoc (cc_c inj)).
  rewrite <- (cc_compose_assoc wt_c).
  rewrite (inv_drop _ wt_c), !cc_compose_assoc.
  (* move the wt_c to top level *)
  rewrite <- (lessdef_c_cklr ext) , cc_compose_assoc, <- (cc_compose_assoc wt_c) at 1.
  rewrite <- (cc_compose_assoc (cc_c inj)).
  rewrite !wt_R_refinement. rewrite cc_compose_assoc.
  rewrite <- (cc_compose_assoc (cc_c injp)).
  rewrite wt_R_refinement. rewrite !cc_compose_assoc.
  rewrite <- (cc_compose_assoc lessdef_c).
  rewrite lessdef_c_cklr.

  (* manully compose the cklrs into a single injp *)
  rewrite <- (cc_compose_assoc (cc_c inj)), <- cc_c_compose.
  rewrite inj_ext.
  rewrite <- (cc_compose_assoc (cc_c inj)), <- cc_c_compose.
  rewrite inj_ext.
  rewrite <- (cc_compose_assoc (cc_c ext)), <- cc_c_compose.
  rewrite ext_inj.
  rewrite <- (cc_compose_assoc (cc_c injp)), <- cc_c_compose.
  rewrite injp_inj.
  rewrite <- (cc_compose_assoc (cc_c injp)), <- cc_c_compose.
  rewrite injp_injp_eq.
  rewrite <- (cc_compose_assoc (cc_c injp)), <- cc_c_compose.
  rewrite injp_inj.
  reflexivity.
Qed.

(** Derivation of the simulation conventions for C-level at the incoming side *)
Lemma cc_c_level_expand:
  ccref cc_c_level
        ( ro @ cc_c injp @ 
              cc_c inj@
              (wt_c @ cc_c ext) @ cc_c ext @
              cc_c inj @
              cc_c ext @ cc_c inj @ cc_c injp @
              (ro @ injp) @ (ro @ injp) @ (ro @ injp)).
Proof.
  unfold cc_c_level.
  (*p j e e j e j p*)
  etransitivity.
  (*prepare for ro*)
  rewrite <- cc_compose_assoc at 1.
  rewrite inv_commute_ref.
  rewrite cc_compose_assoc.
  rewrite (trans_injp_inv_incoming ro).
  rewrite (trans_injp_inv_incoming ro).
  rewrite ! cc_compose_assoc.
  rewrite <- cc_compose_assoc.
  rewrite inv_commute_ref.
  rewrite cc_compose_assoc.
  reflexivity. rstep. rauto.
  
  (*prepare for other C optimizations *)
  etransitivity.
  rewrite injp__injp_inj_injp, !cc_c_compose at 1.
  rewrite inj_inj, cc_c_compose, cc_compose_assoc.
  rewrite inj_inj, cc_c_compose, cc_compose_assoc at 1.
  rewrite <- inj_ext, cc_c_compose, cc_compose_assoc at 1.
  rewrite <- inj_ext, cc_c_compose, cc_compose_assoc at 1.
  rewrite <- inj_ext at 2. rewrite cc_c_compose, cc_compose_assoc.
  rewrite <- (lessdef_c_cklr injp) at 1. rewrite cc_compose_assoc.
  rewrite <- (cc_compose_assoc wt_c).
  rewrite <- cc_compose_assoc.
  assert (HINJP: ccref ((wt_c @ lessdef_c) @ injp) (injp @ wt_c @ lessdef_c)).
  apply commut_wt_c.
  rewrite HINJP.
  rewrite !cc_compose_assoc.
  rewrite <- (cc_compose_assoc wt_c).
  rewrite <- (cc_compose_assoc (_@_)).
  assert (HINJ: ccref ((wt_c @ lessdef_c) @ inj) (inj @ wt_c @ lessdef_c)).
  apply commut_wt_c.
  rewrite HINJ.
  rewrite !cc_compose_assoc. rewrite <- (cc_compose_assoc lessdef_c).
  rewrite lessdef_c_cklr. reflexivity.
  rewrite !cc_compose_assoc.
  repeat rstep.
Qed.

(** Derivation of the simulation conventions for C-level at the outgoing side *)
Lemma cc_c_level_collapse:
  ccref (ro @ cc_c injp @ cc_c injp @
              (wt_c @ cc_c ext) @ cc_c ext @
              cc_c inj @
              cc_c ext @
              cc_c injp @
              cc_c injp @
              (ro @ injp) @ (ro @ injp) @ (ro @ injp)
        )
        cc_c_level.
Proof.
  rewrite <- (cc_compose_assoc injp), <- cc_c_compose. rewrite injp_injp_eq.
  rewrite <- (lessdef_c_cklr ext) at 1. rewrite !cc_compose_assoc.
  rewrite <- (cc_compose_assoc wt_c).
  rewrite <- (cc_compose_assoc injp).
  rewrite wt_R_refinement.
  rewrite !cc_compose_assoc.
  rewrite <- (cc_compose_assoc lessdef_c).
  rewrite lessdef_c_cklr.
  (* unfold cc_c_level. rstep. rauto. *)
  rewrite <- (cc_compose_assoc ext), <- cc_c_compose. rewrite ext_ext.
  rewrite <- (cc_compose_assoc ext), <- cc_c_compose. rewrite ext_inj.
  rewrite <- (cc_compose_assoc inj), <- cc_c_compose. rewrite inj_ext.
  rewrite <- (cc_compose_assoc inj).
  rewrite <- (cc_c_compose inj). rewrite inj_injp.
  rewrite <- (cc_compose_assoc injp), <- cc_c_compose. rewrite injp_injp_eq.
  rewrite <- (cc_compose_assoc injp), <- cc_c_compose. rewrite injp_injp_eq.
  unfold cc_c_level. rewrite <- !(cc_compose_assoc ro).
  rewrite <- inv_commute_ref at 2. rewrite inv_commute_ref.
  rewrite !cc_compose_assoc. rstep. rauto.
  rewrite <- !(cc_compose_assoc ro).
  assert (ccref (injp @ injp) injp).
  rewrite <- cc_c_compose. rewrite injp_injp_eq. reflexivity.
  rewrite !(trans_injp_ro_outgoing); eauto. reflexivity.
Qed.

(** Unification of the incoming side *)
Lemma cc_expand :
  ccref 
    cc_compcert_cod
    (
      ro @
      cc_c injp @ 
      cc_c inj @
      (wt_c @ cc_c ext) @ cc_c ext @
      cc_c inj @
      cc_c ext @ cc_c inj @ cc_c injp @
      (ro @ injp) @ (ro @ injp) @ (ro @ injp) @
    cc_c inj @                                   (* Unusedglob *)
    (wt_c @ cc_c ext @ cc_c_locset) @            (* Alloc *)
    cc_locset ext @                              (* Tunneling *)
    (wt_loc @ cc_locset_mach @ cc_mach inj ) @   (* Stacking *)
    (cc_mach ext @ cc_mach_asm) @
    cc_asm inj
    ).
Proof.
  unfold cc_compcert_cod. rewrite cc_compcert_expand.
  rewrite cc_c_level_expand. rewrite !cc_compose_assoc.
  reflexivity.
Qed.

(** Unification of the outgoing side *)
Lemma cc_collapse :
  ccref
    ( ro @ cc_c injp @ 
      cc_c injp @
      (wt_c @ cc_c ext) @ cc_c ext @
      cc_c inj @
      cc_c ext @ cc_c injp @ cc_c injp @
      (ro @ injp) @ (ro @ injp) @ (ro @ injp) @
      cc_c inj @                                   (* Unusedglob *)
      (wt_c @ cc_c ext @ cc_c_locset) @            (* Alloc *)
      cc_locset ext @                              (* Tunneling *)
      (wt_loc @ cc_locset injp @ cc_locset_mach) @ (* Stacking *)
      (cc_mach ext @ cc_mach_asm) @
      cc_asm inj
    )
    cc_compcert_dom.
Proof.
  rewrite <- cc_compcert_collapse.
  rewrite <- cc_c_level_collapse.
  rewrite ! cc_compose_assoc.
  reflexivity.
Qed.

Lemma injp_pass: forall p tp,
    let sem := RTL.semantics p in
    let tsem := RTL.semantics tp in
  forward_simulation (cc_c injp) (cc_c inj) sem tsem ->
  forward_simulation (cc_c injp) (cc_c injp) sem tsem.
Proof.
  intros.
  rewrite injp__injp_inj_injp at 2.
  rewrite <- injp_injp2,  !cc_c_compose at 1.
  rewrite <- injp_injp2,  !cc_c_compose at 1.
  rewrite cc_compose_assoc.
  eapply compose_forward_simulations.
  eapply RTLrel.semantics_rel.
  eapply compose_forward_simulations. eauto.
  eapply RTLrel.semantics_rel.
Qed.

Lemma compose_identity_pass {liA1 liA2 liB1 liB2} ccA ccB sem bsem tsem:
  forward_simulation 1 1 sem bsem ->
  forward_simulation ccA ccB bsem tsem ->
  @forward_simulation liA1 liA2 ccA liB1 liB2 ccB sem tsem.
Proof.
  intros.
  rewrite <- (cc_compose_id_left ccA).
  rewrite <- (cc_compose_id_left ccB).
  eapply compose_forward_simulations; eauto.
Qed.

Lemma compose_optional_pass {A liA1 liA2 liB1 liB2 ccA ccB ccA' ccB' sem}:
  (forall prog tprog tsem,
      forward_simulation ccA ccB (sem prog) (sem tprog) ->
      forward_simulation ccA' ccB' (sem tprog) tsem ->
      @forward_simulation liA1 liA2 ccA' liB1 liB2 ccB' (sem prog) tsem) ->
  forall flag transf prog tprog tsem,
    @match_if A flag transf prog tprog ->
    (forall p tp, transf p tp -> forward_simulation ccA ccB (sem p) (sem tp)) ->
    forward_simulation ccA' ccB' (sem tprog) tsem ->
    forward_simulation ccA' ccB' (sem prog) tsem.
Proof.
  intros. unfold match_if in *.
  destruct (flag tt); subst; eauto.
Qed.

Lemma va_interface_selfsim: forall (prog: RTL.program),
  forward_simulation (ro @ injp) (ro @ injp) (RTL.semantics prog) (RTL.semantics prog).
Proof.
  intros.
  eapply compose_forward_simulations.
  eapply preserves_fsim. eapply ValueAnalysis.RTL_ro_preserves.
  eapply RTLrel.semantics_rel.
Qed.

Lemma deadcode_va_correct : forall (p tp:  RTL.program),
    let sem1 := RTL.semantics p in
    let sem2 := RTL.semantics tp in
    forward_simulation (ro @ injp) (ro @ inj) sem1 sem2 ->
    forward_simulation (ro @ injp) (ro @ injp) sem1 sem2.
Proof.
  intros. rewrite (ro_injp_inj_I_incoming ro) at 2.
  rewrite <- Deadcode_ext_out at 1.
  eapply compose_forward_simulations.
  eapply va_interface_selfsim; eauto.
  eapply compose_forward_simulations. eauto.
  apply RTLrel.semantics_rel.
Qed.


(** Simulation convention of the rust compiler *)

(* Definition of ro and wt for rust interface  *)

Inductive sound_rust_query ge m: rust_query -> Prop :=
  sound_rust_query_intro vf sg vargs:
    sound_memory_ro ge m ->
    sound_rust_query ge m (rsq vf sg vargs m).

Inductive sound_rust_reply m: rust_reply -> Prop :=
  sound_rust_reply_intro res tm:
    ro_acc m tm ->
    sound_rust_reply m (rsr res tm).

Definition ro_rs : invariant li_rs :=
  {|
    symtbl_inv '(row ge m) := eq ge;
    query_inv '(row ge m) := sound_rust_query ge m;
    reply_inv '(row ge m) := sound_rust_reply m;
  |}.

(* we just copy wt_c. *)
Definition wt_rs : invariant li_rs :=
  {|
    symtbl_inv :=
      fun '(se, sg) => eq se;
    query_inv :=
      fun '(se, sg) q =>
        sg = rsq_sg q /\ Val.has_type_list (rsq_args q) (map typ_of_type (rs_sig_args sg));
    reply_inv :=
      fun '(se, sg) r =>
        Val.has_type (rsr_retval r) (proj_rettype (rettype_of_type (rs_sig_res sg)));
  |}.

Definition cc_rust_compcert: callconv li_rs li_asm :=
  ro_rs @ wt_rs @
  cc_rust_asm_injp @
  cc_asm injp.

(* Compilation (R) in C side can be implemented in Rust side *)
Instance commut_rust_c R:
  Commutes cc_rust_c (cc_rs R) (cc_c R).
Proof.
  intros [[_ w] wR] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
  destruct Hqi2. inv Hq1i.
  exists (se2, wR, tt). repeat apply conj.
  - econstructor; auto. simpl; auto.
  - econstructor. split.
    econstructor; eauto.
    econstructor.
  - intros r1 r2 (ri & (wR'' & HwR'' & Hr1i) & Hri2).
    destruct Hr1i. inv Hri2.
    econstructor. split.
    econstructor.
    econstructor; eauto. split; eauto.
    econstructor; auto.
Qed.

(* Compilation (ro) in C side can be implemented in Rust side. *)
Instance commut_rust_c_ro:
  Commutes cc_rust_c ro_rs ro.
Proof.
  intros [[_ w] (se' & m)] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
  destruct Hqi2. inv H. inv Hse. inv H. inv Hq1i.
  exists (se2, row se2 m, tt). repeat apply conj.
  - econstructor; simpl; auto.
    econstructor. auto.
  - econstructor. split.
    econstructor. econstructor; auto.
    econstructor.
  - intros r1 r2 (r1' & (Hr1 & Hr2)). inv Hr1. inv Hr2.
    inv H. econstructor. split.
    econstructor.
    econstructor. constructor. auto.
Qed.


(** Rust-level typing constraints *)

Inductive lessdef_rs_mq: rust_query -> rust_query -> Prop :=
  lessdef_rs_mq_intro vf sg args_ args m:
    Val.lessdef_list args_ args ->
    lessdef_rs_mq (rsq vf sg args_ m) (rsq vf sg args m).

Inductive lessdef_rs_mr: rust_reply -> rust_reply -> Prop :=
  lessdef_rs_mr_intro res_ res m:
    Val.lessdef res_ res ->
    lessdef_rs_mr (rsr res_ m) (rsr res m).

Program Definition lessdef_rs : callconv li_rs li_rs :=
  {|
    ccworld := unit;
    match_senv _ := eq;
    match_query _ := lessdef_rs_mq;
    match_reply _ := lessdef_rs_mr;
  |}.
Next Obligation.
  split; auto.
Defined.

(* Intuition: wt_rs does not really utilize the rust type to do
compilation. It uses typ_of_type to transform to rust types to AST
type, so the compilation also can be done in C-side. Oppositely, the
C-side compilation based on wt_c can also be done in Rust side if we
can construct the corresponding rust types (it should work because
rust types have more information than AST type). *)
Lemma commut_rust_c_wt_lessdef:
  cceqv ((wt_rs @ lessdef_rs) @ cc_rust_c) (cc_rust_c @ (wt_c @ lessdef_c)).
Proof.
  split.
  - red. intros ((se' & ((se1'' & (se1''' & sg)) & ?)) & ?).
    intros se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
    inv H0. inv Hse. inv Hqi2. destruct Hq1i. destruct H0. inv H1. inv H. inv H1.
    inv H0. inv H. simpl in H1.
    (* construct C signature from Rust *)
    exists (se2, tt, (se2, (se2, (signature_of_rust_signature sg0)), tt)).
    repeat apply conj.
    + econstructor. simpl. auto.
      do 4 econstructor. 
    + econstructor. split.
      econstructor.
      econstructor. split.
      * econstructor. econstructor. simpl. auto.
        simpl. auto.
      * econstructor. auto.
    + intros r1 r2. intros Hr. inv Hr. destruct H. inv H. inv H0.
      destruct H. inv H0. inv H. simpl in H3.
      econstructor. split.
      * econstructor. split.
        econstructor. eauto.
        econstructor. eauto.
      * econstructor.
  - red. intros ((se' & ?) & ((se1'' & (se1''' & sg)) & ?)).
    intros se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
    inv Hq1i. inv Hse. inv H. inv H1. inv H0.
    inv Hqi2. destruct H. inv H0. inv H. inv H2.
    cbn [cq_args cq_sg] in *.
    exists (se2,(se2, (se2, sg0), tt), tt).
    repeat apply conj.
    + do 4  econstructor.
    + econstructor. split.
      econstructor. split.
      econstructor. econstructor; eauto.
      econstructor. eauto.
      econstructor.
    + intros r1 r2. intros Hr. inv Hr. destruct H. inv H. inv H2.
      destruct H3. inv H2. inv H. simpl in H2.
      econstructor. split.
      * econstructor.
      * econstructor. split.
        econstructor; eauto.
        econstructor. auto.
Qed.


(* copy from lessdef_c_cklr in CallConv *)
Lemma lessdef_rs_cklr R:
  cceqv (lessdef_rs @ cc_rs R) (cc_rs R).
Proof.
  split.
  - intros [[_ [ ]] wR] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2). cbn in * |-.
    destruct Hqi2. inv Hq1i.
    eexists wR. cbn. repeat apply conj; auto.
    + constructor; auto. clear - H0 H5.
      eapply val_lessdef_inject_list_compose; eauto.
    + intros r1 r2 Hr. exists r1; split; auto.
      destruct r1; constructor; auto.
  - intros wR se1 se2 q1 q2 Hse Hq.
    exists (se1, tt, wR). repeat apply conj; cbn; eauto.
    + exists q1. split; auto. destruct q1. constructor; auto.
      clear. induction rsq_args; constructor; auto.
    + intros r1 r2 (ri & Hr1i & wR' & HwR' & Hri2).
      exists wR'. split; auto. destruct Hri2; inv Hr1i; constructor; auto.
      eapply Mem.val_lessdef_inject_compose; eauto.
Qed.

(* copy from wt_R_refinement in CallConv *)
Theorem wt_rs_R_refinement R:
  ccref (cc_rs R @ (wt_rs @ lessdef_rs)) ((wt_rs @ lessdef_rs) @ cc_rs R).
Proof.
  rewrite cc_compose_assoc. rewrite lessdef_rs_cklr.
  intros [[se wR][[se' [se'' sg]] ?]].
  intros se1 se2 q1 q2 [Hse1 [Hse2 Hse3]] [q2' [Hq1 [q2'' [Hq2 Hq3]]]].
  inv Hse2. inv Hse3. cbn in H. cbn in Hq1. subst se''.
  inv Hq1. inv Hq2. inv Hq3. cbn in H3. destruct H3 as [? TYPE]. subst.
  exists (se1,(se1,sg0),wR). repeat apply conj.
  - constructor; cbn; eauto. constructor; eauto.
  - cbn in H0. cbn in H.
    exists (rsq vf1 sg0 vargs1 m1). split.
    econstructor; eauto. split.
    econstructor; eauto.
    eapply val_has_type_list_inject; eauto.
    econstructor; eauto.
    eapply val_inject_lessdef_list_compose; eauto.
  - intros r1 r2 [r1' [Hr1 Hr2]].
    inv Hr1. cbn in H3.
    destruct Hr2 as [w [Hw Hr2]].
    inv Hr2.
    set (res' := Val.ensure_type vres2 (proj_sig_res (signature_of_rust_signature sg0)) ).
    exists (rsr res' m2'). split. exists w. split. eauto.
    econstructor; eauto.
    unfold res'.
    apply has_type_inject; eauto.
    exists (rsr res' m2'). split.
    constructor; eauto. cbn. unfold res'. apply Val.ensure_has_type.
    constructor; eauto. unfold res'.
    destruct vres2, (proj_sig_res (signature_of_rust_signature sg0)); auto. 
Qed.

(* copy from commut_wt_c in CallConv *)
Instance commut_wt_rs (R : cklr):
  Commutes (wt_rs @ lessdef_rs) (cc_rs R) (cc_rs R).
Proof.
 red. rewrite cc_compose_assoc. rewrite lessdef_rs_cklr.
  intros [[_ [ ]] wR] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
  destruct Hqi2. inv Hq1i. inv H4. cbn [rsq_sg rsq_args] in *.
  eexists (se2, wR, (se2, (se2, sg), tt)). repeat apply conj; cbn.
  + repeat constructor; cbn; auto.
  + edestruct has_type_inject_list as (vl2 & Hvl2 & Hvl & Hvl'); eauto.
    exists (rsq vf2 sg vl2 m2). split.
    * constructor; eauto.
    * eexists. split; constructor; cbn; eauto.
  + intros r1 r2 (ri & (wR' & HwR' & Hr1i) & rj & Hrij & Hrj2).
    destruct Hr1i. inv Hrij. inv Hrj2. cbn in *.
    eexists; split.
    * constructor. cbn. eapply val_has_type_inject; eauto.
    * exists wR'. split; auto. constructor; eauto.
      eapply Mem.val_inject_lessdef_compose; eauto.
Qed.

(* just copy trans_injp_ro_outgoing *)
Lemma trans_injp_rors_outgoing:
  ccref ((ro_rs @ (cc_rs injp)) @ (ro_rs @ (cc_rs injp))) (ro_rs @ (cc_rs injp)).
Proof.
  red.
  intros w se1' se3 q1 q3 MSTBL13 MMEM13.
  destruct w as [[se2' [[se1 wi1] w12]] [[se2 wi2] w23]].
  destruct MSTBL13 as [[Hsi1 MSTBL12] [Hsi2 MSTBL23]].
  destruct MMEM13 as [m2 [[q1' [Hmi1 MMEM12]] [q2' [Hmi2 MMEM23]]]].
  inv Hsi1. inv Hsi2. inv Hmi1. inv Hmi2. rename q1' into q1. rename q2' into q2.
  inv MMEM12. inv H5. rename f into j12. rename Hm0 into INJ12. clear Hm1.
  inv MMEM23. inv H13. rename f into j23. rename Hm1 into INJ23. clear Hm2.
  cbn in H12, MSTBL12, H10, MSTBL23,H3, H4. destruct wi1. inv H. inv H1.
  destruct wi2. inv H0. inv H2.
  exists (se1, (row se1 m1), (injpw (compose_meminj j12 j23)
          m1 m3 (Mem.inject_compose _ _ _ _ _ INJ12 INJ23))).
  simpl.
  repeat apply conj.
  - constructor. eauto.
  - inv MSTBL12. inv MSTBL23.
    econstructor; simpl; auto.
    eapply Genv.match_stbls_compose; eauto.
  - exists (rsq vf1 sg vargs1 m1). split. constructor; eauto. constructor; eauto.
    constructor; cbn; eauto.
    eapply val_inject_compose; eauto.
    eapply CKLRAlgebra.val_inject_list_compose.
    econstructor; eauto.
  - intros r1 r3 [r2 [Hi2 [w13' [INCR13' Hr13]]]].
    inv Hr13. inv H1. rename f into j13'. rename Hm3 into INJ13'.
    cbn in INCR13'. rename m2' into m3'.
    inversion INCR13' as [? ? ? ? ? ? ? ? RO1 RO3 MAXPERM1 MAXPERM3 UNCHANGE1 UNCHANGE3 INCR13 DISJ13]. subst.
    generalize (inject_implies_image_in _ _ _ INJ12).
    intros IMGIN12.
    generalize (inject_implies_image_in _ _ _ INJ23).
    intros IMGIN23.
    generalize (inject_implies_dom_in _ _ _ INJ12).
    intros DOMIN12.
    generalize (inject_implies_dom_in _ _ _ INJ23).
    intros DOMIN23.
    generalize (inject_implies_dom_in _ _ _ INJ13').
    intros DOMIN13'.
    generalize (Mem.unchanged_on_support _ _ _ UNCHANGE1).
    intros SUPINCL1.
    generalize (Mem.unchanged_on_support _ _ _ UNCHANGE3).
    intros SUPINCL3.
    generalize (inject_incr_inv _ _ _ _ _ _ _ DOMIN12 IMGIN12 DOMIN23 DOMIN13' SUPINCL1 INCR13 DISJ13).
    intros (j12' & j23' & m2'_sup & JEQ & INCR12 & INCR23 & SUPINCL2 & DOMIN12' & IMGIN12' & DOMIN23' & INCRDISJ12 & INCRDISJ23 & INCRNOLAP & ADDZERO & ADDEXISTS & ADDSAME).
    subst. cbn in *.
    set (m2' := m2' m1 m2 m1' j12 j23 j12' m2'_sup INJ12 ).
    assert (INJ12' :  Mem.inject j12' m1' m2'). eapply INJ12'; eauto.
    assert (INJ23' :  Mem.inject j23' m2' m3'). eapply INJ23'; eauto.
    set (w1' := injpw j12' m1' m2' INJ12').
    set (w2' := injpw j23' m2' m3' INJ23').
    rename vres2 into vres3.
    exploit compose_meminj_midvalue; eauto.
    intros [vres2 [RES1 RES2]].
    assert (UNC21:Mem.unchanged_on (loc_out_of_reach j12 m1) m2 m2').
    eapply UNCHANGE21; eauto.
    exists (rsr vres2 m2'). split.
    + 
      exists (rsr vres1 m1'). split. cbn. auto.
      exists w1'. cbn. split. constructor; eauto. eapply ROUNC2; eauto.
      eapply MAXPERM2; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      intros. red. unfold compose_meminj.
      rewrite H1. reflexivity.
      constructor; eauto. constructor; eauto.
    + exists (rsr vres2 m2'). split. cbn. econstructor. constructor.
      constructor. eapply ROUNC2; eauto.
      inversion UNC21. eauto.
      eapply MAXPERM2; eauto.
      exists w2'. cbn. split. constructor; eauto. eapply ROUNC2; eauto.
      eapply MAXPERM2; eauto.
      eapply UNCHANGE22; eauto. eapply out_of_reach_trans; eauto.
      econstructor; eauto. constructor; eauto.
Qed.

(* just copy trans_injp_inv_incoming *)
Lemma trans_rs_injp_inv_incoming (I: invariant li_rs) :
  ccref (I @ cc_rs injp) ((I @ cc_rs injp) @ (I @ cc_rs injp)).
Proof.
  red. intros [[se wi] w] se1 se2 q1' q2 [Hse1 Hse2] [q1 [Hq1 Hq2]].
  inv Hse1. inv Hq1. inv Hse2. inv Hq2. inv H6. rename m0 into m1.
  rename m3 into m2. cbn in H4, H5.
  exists (se, (se,wi, (injpw (meminj_dom f) m1 m1 (mem_inject_dom f m1 m2 Hm))),
      (se,wi, (injpw f m1 m2 Hm))). repeat apply conj.
  - constructor. constructor. red. cbn. constructor. auto.
    constructor; eauto. eapply match_stbls_dom; eauto.
    constructor. constructor. auto.
    constructor; eauto.
  - eexists (rsq vf1 sg vargs1 m1). split. eexists. split. constructor. eauto.
    econstructor; cbn; eauto.
    eapply val_inject_dom; eauto.
    eapply val_inject_list_dom; eauto.
    eexists. split. constructor. eauto. constructor; eauto. constructor.
  - intros r1' r3 [r2' [[r1 [Hi1 Hr1]] [r2 [Hi2 Hr2]]]].
    inv Hi1. inv Hi2.
    exists r1. split. red. cbn. constructor. auto.
    clear H6 H8 H0 H.
    destruct Hr1 as [w12' [Hw12' Hr12']]. destruct Hr2 as [w23' [Hw23' Hr23']].
    destruct w12' as [f12' m1' m2' Hm12']. destruct w23' as [f23' m2'' m3' Hm23'].
    inv Hw12'. inv Hw23'. cbn in *.
    inv Hr12'. inv Hr23'. cbn in *. inv H0. inv H27.
    rename m1'0 into m1'. rename m2'0 into m2'. rename m2'1 into m3'.
    eexists (injpw (compose_meminj f12' f23') m1' m3'
               (Mem.inject_compose f12' f23' _ _ _ Hm12' Hm23')
            ).
    repeat apply conj.
    + constructor; eauto.
      * eapply Mem.unchanged_on_implies; eauto.
        intros. red. unfold meminj_dom. rewrite H0. reflexivity.
      * red. intros. unfold compose_meminj.
        erewrite H17. erewrite H25; eauto.
        2: unfold meminj_dom; rewrite H0; reflexivity.
        rewrite Z.add_0_l. reflexivity.
      * intros b1 b2 delta Hb Hb'. unfold compose_meminj in Hb'.
        destruct (f12' b1) as [[bi delta12] | ] eqn:Hb1; try discriminate.
        destruct (f23' bi) as [[xb2 delta23] | ] eqn:Hb2; try discriminate.
        inv Hb'.
        edestruct H18; eauto. unfold meminj_dom. rewrite Hb. auto.
        destruct (f bi) as [[? ?] | ] eqn:Hfbi.
        {
          eapply Mem.valid_block_inject_1 in Hfbi; eauto.
        }
        edestruct H26; eauto.
    + constructor; cbn; eauto with mem.
      eapply Values.val_inject_compose; eauto.
Qed.


Lemma cc_rust_collapse:
  ccref
    (ro_rs @                    (* Self simulation of Rustlight *)
       cc_rs injp @             (* Elaborate drop *)
       (cc_rs inj @ cc_rust_c) @  (* Clightgen: may be changed to injp *)
       cc_compcert)             (* CompCertO *)
    cc_rust_compcert.
Proof.
  unfold cc_compcert, cc_rust_compcert.
  rewrite cc_compose_assoc.
  (* merge top-level injp and inj *)
  rewrite <- (cc_compose_assoc (cc_rs injp)), <- cc_rs_compose. rewrite injp_inj.
  (* move ro to the top *)
  rewrite cc_cainjp__injp_ca.
  rewrite cc_compose_assoc.
  rewrite <- lessdef_c_cklr, cc_compose_assoc, <- (cc_compose_assoc wt_c).
  rewrite (commute_around (wt_c @ lessdef_c)).
  rewrite !(commute_around cc_rust_c).
  rewrite <- !(cc_compose_assoc ro_rs).
  rewrite <- (cc_compose_assoc (ro_rs @ cc_rs injp)).
  rewrite trans_injp_rors_outgoing.
  rewrite cc_compose_assoc.
  (* move wt_c to the top *)
  rewrite <- (cc_compose_assoc cc_rust_c).
  rewrite <- commut_rust_c_wt_lessdef.
  do 2 rewrite <- (cc_compose_assoc (cc_rs injp)).
  rewrite wt_rs_R_refinement.
  rewrite !cc_compose_assoc, <- (cc_compose_assoc lessdef_rs).
  rewrite lessdef_rs_cklr.
  (* merge injp, cc_rust_c and cc_c_asm_injp *)  
  rewrite <- (cc_compose_assoc cc_rust_c), cc_rcca_ra.
  rewrite <- (cc_compose_assoc (cc_rs injp)), cc_injpra_rainjp.
  reflexivity.
Qed.


(* Intuition: the compilation in Rust side (left) can be implementd in
C side (right) because the compilation does not utilize the rust types
(which resides in the signatue of the query), so this refinement
should be correct *)
Lemma injp_rs__rc_injp:
  ccref (cc_rs injp @ cc_rust_c) (cc_rust_c @ injp).
Proof.
  red. intros ((se & w1) & w2) se1 se2 q1 q2 (Hse1 & Hse2) (q2' & (Hq1 & Hq2)).
  inv Hse2. inv Hq2. inv Hq1.
  exists (se1, tt, w1). repeat apply conj.
  - econstructor. simpl. auto.
    auto.
  - econstructor. split. econstructor.
    econstructor; auto.
  - intros r1 r2 (r1' & (Hr1 & Hr2)).
    inv Hr1. destruct Hr2 as (w1' & acc & Hr2). inv Hr2.
    econstructor. split.
    + econstructor. split. eauto.
      econstructor; eauto.
    + econstructor.
Qed.

  
(* ro_rs is defined by copying ro in C side, so it should not utilize
any properties of Rust types to perform optimizations. It can be moved
to (or implemented in) C-side. *)
Lemma ro_rs__rc_ro:
  ccref (ro_rs @ cc_rust_c) (cc_rust_c @ ro).
Proof.
  red. intros ((se & (se' & m)) & w2) se1 se2 q1 q2 (Hse1 & Hse2) (q2' & (Hq1 & Hq2)).
  inv Hse2. inv Hse1. inv Hq2. inv Hq1. inv H0. inv H.
  exists (se2, tt, row se2 m0). repeat apply conj.
  - econstructor; simpl; auto.
    econstructor. auto.
  - econstructor. split.
    econstructor.
    econstructor; eauto. econstructor. auto.
  - intros r1 r2 (r1' & (Hr1 & Hr2)). inv Hr1. inv Hr2.
    inv H. econstructor. split.
    econstructor. econstructor. auto.
    econstructor.
Qed.

    
Lemma cc_rust_expand:
  ccref
    cc_rust_compcert
    (ro_rs @                    (* Self simulation of Rustlight *)
       cc_rs injp @             (* Elaborate drop *)
       (cc_rs injp @ cc_rust_c) @  (* Clightgen: outgoing should be injp *)
       (** may be we should not use cc_compcert because it contains
       some self-simulation invariant which is not belong to the
       compiler *)
       cc_compcert)             (* CompCertO *)
.
Proof.
  unfold cc_rust_compcert, cc_compcert.
  rewrite !cc_compose_assoc.
  (* 1. expand RAinjp *)
  rewrite cc_rainjp_injpra.
  rewrite !cc_compose_assoc.
  rewrite cc_ra_rcca, cc_compose_assoc.
  (* 2. put down an injp *)
  rewrite injp_injp at 1. rewrite cc_rs_compose, cc_compose_assoc.
  (* swap injp⋅rc *)
  rewrite <- (cc_compose_assoc (cc_rs injp) cc_rust_c).
  rewrite injp_rs__rc_injp.
  rewrite cc_compose_assoc.    
  (* 3. put down wt_rs from rust to c *)
  rewrite <- (cc_compose_assoc wt_rs).
  rewrite <- lessdef_rs_cklr at 1.
  rewrite ! cc_compose_assoc, <- (cc_compose_assoc wt_rs).
  rewrite (commute_around (wt_rs @ lessdef_rs)).
  (* 3.1 swap (wt_rs @ lessdef_rs) and cc_rust_c *)
  rewrite <- (cc_compose_assoc (wt_rs @ lessdef_rs)).
  rewrite commut_rust_c_wt_lessdef.
  (* 3.2 absorb lessdef_c into injp *)
  rewrite !cc_compose_assoc. 
  rewrite <- (cc_compose_assoc lessdef_c).
  rewrite lessdef_c_cklr.  
  (* 4. put down (ro⋅injp) from rust to c *)
  rewrite <- (cc_compose_assoc ro_rs).
  rewrite trans_rs_injp_inv_incoming.
  rewrite !cc_compose_assoc.
  (* 4.1 swap injp⋅rc *)
  rewrite <- (cc_compose_assoc (cc_rs injp) cc_rust_c).
  rewrite injp_rs__rc_injp.
  rewrite cc_compose_assoc.    
  (* 4.2 swap ro⋅rc *)
  rewrite <- (cc_compose_assoc ro_rs cc_rust_c).
  rewrite ro_rs__rc_ro.
  rewrite cc_compose_assoc.
  (* 4.3 swap injp and wt_c at c level *)
  rewrite <- (cc_compose_assoc wt_c injp).
  rewrite <- (cc_compose_assoc injp (wt_c @ injp)).
  rewrite wt_R__R_wt.
  (* 4.4 combine two injps in c level *)
  rewrite <- cc_c_compose. rewrite injp_injp2, cc_compose_assoc.
  (* 5. combine injp and ca *)
  rewrite <- (cc_compose_assoc injp). rewrite cc_injpca_cainjp.
  rewrite injp_injp at 1. rewrite cc_rs_compose.
  rewrite cc_compose_assoc.
  reflexivity.
Qed.

(** ** Composition of passes *)

Theorem clight_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  forward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics tp)
  /\ backward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics tp).
Proof.
  intros p tp M. unfold match_prog, pass_match in M; simpl in M.
Ltac DestructM :=
  match goal with
    [ H: exists p, _ /\ _ |- _ ] =>
      let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
      destruct H as (p & M & MM); clear H
  end.
  repeat DestructM. subst tp.
  assert (F: forward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics p20)).
  {
  eapply cc_compcert_merge; eauto.
  rewrite cc_expand. rewrite <- cc_collapse at 1.
  eapply compose_forward_simulations.
    eapply top_ro_selfsim; eassumption.
  eapply compose_forward_simulations.
    eapply SimplLocalsproof.transf_program_correct'; eassumption.
  eapply compose_identity_pass.
    eapply Cshmgenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Cminorgenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Selectionproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply RTLgenproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply RTLrel.semantics_rel.
  eapply compose_forward_simulations.
    unfold match_if in M4. destruct (optim_tailcalls tt).
    eapply Tailcallproof.transf_program_correct; eauto.
    subst. eapply RTLrel.semantics_rel.
  eapply compose_forward_simulations.
    eapply Inliningproof.transf_program_correct; eassumption.
  eapply compose_identity_pass.
    eapply Renumberproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply RTLrel.semantics_rel.
  eapply compose_forward_simulations.
  { unfold match_if in M7. destruct (optim_constprop tt).
    eapply Constpropproof.transf_program_correct; eassumption.
    subst. apply va_interface_selfsim. }
  eapply compose_identity_pass. 
    unfold match_if in M8. destruct (optim_constprop tt).
    eapply Renumberproof.transf_program_correct; eassumption.
    subst. eapply identity_forward_simulation.
  eapply compose_forward_simulations.
  { unfold match_if in M9. destruct (optim_CSE tt).
    eapply CSEproof.transf_program_correct; eassumption.
    subst. apply va_interface_selfsim. }
  eapply compose_forward_simulations.
  { unfold match_if in M10. destruct (optim_redundancy tt).
    eapply deadcode_va_correct.
    eapply Deadcodeproof.transf_program_correct'; eassumption.
    subst. apply va_interface_selfsim. }
  eapply compose_forward_simulations.
    eapply Unusedglobproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Allocproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Tunnelingproof.transf_program_correct; eassumption.
  eapply compose_identity_pass.
    eapply Linearizeproof.transf_program_correct; eassumption.
  eapply compose_identity_pass.
    eapply CleanupLabelsproof.transf_program_correct; eassumption.
  eapply compose_optional_pass; eauto using compose_identity_pass.
    exact Debugvarproof.transf_program_correct.
  eapply compose_forward_simulations.
    rewrite <- cc_stacking_lm, cc_lm_stacking.
    eapply Stackingproof.transf_program_correct with (rao := Asmgenproof0.return_address_offset).
    exact Asmgenproof.return_address_exists.
    eassumption.
  eapply compose_forward_simulations.
    eapply Asmgenproof.transf_program_correct; eassumption.
  apply semantics_asm_rel.
  }
  split. auto.
  apply forward_to_backward_simulation. auto.
  apply Clight.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem c_semantic_preservation:
  forall p tp,
  match_c_prog p tp ->
  backward_simulation cc_compcert cc_compcert (Csem.semantics p) (Asm.semantics tp).
Proof.
  intros p tp (p' & Hp' & Htp). cbn in Hp'.
  rewrite <- (cc_compose_id_left cc_compcert) at 1.
  rewrite <- (cc_compose_id_left cc_compcert) at 2.
  apply compose_backward_simulations with (atomic (Cstrategy.semantics p)).
  - apply factor_backward_simulation.
    + apply Cstrategy.strategy_simulation.
    + apply Csem.semantics_single_events.
    + eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  - apply forward_to_backward_simulation.
    + apply factor_forward_simulation.
      * eapply compose_identity_pass.
        -- apply SimplExprproof.transl_program_correct; eauto.
        -- apply clight_semantic_preservation; eauto.
      * intros. eapply sd_traces. apply Asm.semantics_determinate.
    + apply atomic_receptive.
      apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
  - intros. eapply sd_traces. apply Asm.semantics_determinate.
Qed.

(** * Correctness of the CompCert compiler *)

(** Combining the results above, we obtain semantic preservation for two
  usage scenarios of CompCert: compilation of a single monolithic program,
  and separate compilation of multiple source files followed by linking.

  In the monolithic case, we have a whole C program [p] that is
  compiled in one run of CompCert to a whole Asm program [tp].
  Then, [tp] preserves the semantics of [p], in the sense that there
  exists a backward simulation of the dynamic semantics of [p]
  by the dynamic semantics of [tp]. *)

Theorem transf_c_program_correct:
  forall p tp,
  transf_c_program p = OK tp ->
  backward_simulation cc_compcert cc_compcert (Csem.semantics p) (Asm.semantics tp).
Proof.
  intros. apply c_semantic_preservation. apply transf_c_program_match; auto.
Qed.

(** * Correctness of the Rust compiler *)

(* move it to elsewhere *)
Lemma rustlight_ro_selfsim:
  forall p: (Rustlight.program),
    let sem := Rustlightown.semantics p in
    forward_simulation ro_rs ro_rs sem sem.
Proof.
Admitted.
  
Theorem rustlight_semantic_preservation:
  forall p tp,
  match_prog_rust p tp ->
  forward_simulation cc_rust_compcert cc_rust_compcert (Rustlightown.semantics p) (Asm.semantics tp)
  /\ backward_simulation cc_rust_compcert cc_rust_compcert (Rustlightown.semantics p) (Asm.semantics tp).
Proof.
  intros p tp M. unfold match_prog_rust, pass_match, CompCertO's_passes_rust in M. 
  cbn -[CompCertO's_passes] in M.
  repeat DestructM.
  assert (F: forward_simulation cc_rust_compcert cc_rust_compcert (Rustlightown.semantics p) (Asm.semantics tp)).
  { rewrite cc_rust_expand at 2. rewrite <- cc_rust_collapse at 1.
    do 2 rewrite <- (cc_compose_assoc _ _ cc_compcert).
    rewrite <- (cc_compose_assoc (cc_rs injp) _ cc_compcert).
    rewrite <- (cc_compose_assoc ro_rs _ cc_compcert).
    eapply compose_forward_simulations.
    (* Clight to Asm semantics preservation *)
    2: { eapply clight_semantic_preservation. eauto. }
    (* Rustlight to Clight semantics preservation *)
    eapply compose_forward_simulations. (* Rustlight ro self-sim *)
    eapply rustlight_ro_selfsim.
    eapply compose_identity_pass. (* RustIRgen *)
    eapply RustIRgenProof.transl_program_correct; eauto.
    eapply compose_forward_simulations. (* ElaborateDrop *)
    eapply ElaborateDropProof.transl_program_correct; eauto.
    admit.                      (** TODO: Clightgenproof *)
  }
  split. auto.
  apply forward_to_backward_simulation. auto.
  admit.
  (* apply Rustlightown.semantics_receptive. (** TODO *) *)  
  apply Asm.semantics_determinate.
Admitted.    
    
(*
(** Here is the separate compilation case.  Consider a nonempty list [c_units]
  of C source files (compilation units), [C1 ,,, Cn].  Assume that every
  C compilation unit [Ci] is successfully compiled by CompCert, obtaining
  an Asm compilation unit [Ai].  Let [asm_unit] be the nonempty list
  [A1 ... An].  Further assume that the C units [C1 ... Cn] can be linked
  together to produce a whole C program [c_program].  Then, the generated
  Asm units can be linked together, producing a whole Asm program
  [asm_program].  Moreover, [asm_program] preserves the semantics of
  [c_program], in the sense that there exists a backward simulation of
  the dynamic semantics of [asm_program] by the dynamic semantics of [c_program].
*)

Theorem separate_transf_c_program_correct:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_clight_program cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
   /\ backward_simulation cc_compcert cc_compcert (Clight.semantics1 c_program) (Asm.semantics asm_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog c_units asm_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_clight_program_match; auto. }
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog c_program asm_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply clight_semantic_preservation; auto.
Qed.
*)

(** An example of how the correctness theorem, horizontal composition,
  and assembly linking proofs can be used together. *)

Require Import SmallstepLinking.
Require Import AsmLinking.

Lemma compose_transf_c_program_correct:
  forall p1 p2 spec tp1 tp2 tp,
    compose (Clight.semantics1 p1) (Clight.semantics1 p2) = Some spec ->
    transf_clight_program p1 = OK tp1 ->
    transf_clight_program p2 = OK tp2 ->
    link tp1 tp2 = Some tp ->
    forward_simulation cc_compcert cc_compcert spec (Asm.semantics tp).
Proof.
  intros.
  rewrite <- (cc_compose_id_right cc_compcert) at 1.
  rewrite <- (cc_compose_id_right cc_compcert) at 2.
  eapply compose_forward_simulations.
  2: { unfold compose in H.
       destruct (@link (AST.program unit unit)) as [skel|] eqn:Hskel; try discriminate.
       cbn in *. inv H.
       eapply AsmLinking.asm_linking; eauto. }
  eapply compose_simulation; eauto.
  eapply clight_semantic_preservation; eauto using transf_clight_program_match.
  eapply clight_semantic_preservation; eauto using transf_clight_program_match.
  unfold compose. cbn.
  apply link_erase_program in H2. rewrite H2. cbn. f_equal. f_equal.
  apply Axioms.functional_extensionality. intros [|]; auto.
Qed.
