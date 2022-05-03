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
(*Require Initializers.*)
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
(*Require Unusedglob.*)
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
(*Require Unusedglobproof.*)
Require Allocproof.
Require Tunnelingproof.
Require Linearizeproof.
Require CleanupLabelsproof.
Require Debugvarproof.
Require Stackingproof.
Require Asmgenproof.
(** Command-line flags. *)
Require Import Compopts.

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
(*
  @@@ time "Unused globals" Unusedglob.transform_program
   @@ print (print_RTL 8)
*)
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

(*
Definition transl_init := Initializers.transl_init.
Definition cexec_do_step := Cexec.do_step.
*)

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
(*
  ::: mkpass Unusedglobproof.match_prog
*)
  ::: mkpass Allocproof.match_prog
  ::: mkpass Tunnelingproof.match_prog
  ::: mkpass Linearizeproof.match_prog
  ::: mkpass CleanupLabelsproof.match_prog
  ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
  ::: mkpass Stackingproof.match_prog
  ::: mkpass Asmgenproof.match_prog
  ::: pass_nil _.

(** Composing the [match_prog] relations above, we obtain the relation
  between CompCert C sources and Asm code that characterize CompCert's
  compilation. *)

Definition match_prog: Clight.program -> Asm.program -> Prop :=
  pass_match (compose_passes CompCertO's_passes).

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
  (*
  destruct (Unusedglob.transform_program p13) as [p14|e] eqn:P14; simpl in T; try discriminate.
   *)
  destruct (Allocation.transf_program p13) as [p15|e] eqn:P15; simpl in T; try discriminate.
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
  (*
  exists p14; split. apply Unusedglobproof.transf_program_match; auto.
   *)
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
Require Import VAInject.
Require Import VAExtends.

(** This is the simulation convention for the whole compiler. *)

Definition cc_cklrs : callconv li_c li_c :=
  injp + inj + ext + vainj + vaext.

Definition cc_compcert : callconv li_c li_asm :=
  cc_cklrs^{*} @
  wt_c @ lessdef_c @ cc_c_locset @ cc_locset_mach @ cc_mach_asm @
  cc_asm vainj.

(** We show that the overall simulation convention can be
  rewritten to match the conventions used in CompCertO's passes.
  The following conventions give a flexible characterization for
  early passes. *)

Definition cc_cod : callconv li_c li_c :=
  wt_c @ inj @ vainj.

Definition cc_dom : callconv li_c li_c :=
  cc_cklrs^{*} @ cc_cod.

Lemma cc_compcert_expand:
  ccref
    cc_compcert
    (cc_dom @                                              (* Passes up to Alloc *)
     (wt_c @ cc_c ext @ cc_c_locset) @                     (* Alloc *)
     cc_locset ext @                                       (* Tunneling *)
     (wt_loc @ cc_locset_mach @ cc_mach inj) @             (* Stacking *)
     (cc_mach ext @ cc_mach_asm) @                         (* Asmgen *)
     cc_asm vainj).
Proof.
  unfold cc_compcert, cc_dom, cc_cod.
  rewrite !cc_compose_assoc.
  etransitivity.
  {
    rewrite vainj_vainj, vainj_inj, !cc_asm_compose, !cc_compose_assoc at 1.
    (* the first [vainj] can be used to meet the requirements of frontend passes *)
    rewrite <- (cc_compose_assoc wt_c lessdef_c).
    do 3 rewrite (commute_around _ (R2 := _ vainj)).
    rewrite vainj_vainj, cc_c_compose, (cc_compose_assoc vainj) at 1.
    rewrite vainj_inj, cc_c_compose, (cc_compose_assoc vainj) at 1.
    rewrite (commute_around _ (R2 := _ vainj)).
    rewrite cc_star_absorb_r by eauto with cc.
    (* we also need to duplicate wt_c for alloc *)
    rewrite (inv_dup wt_c), (cc_compose_assoc wt_c), (cc_compose_assoc wt_c).
    rewrite (commute_around (_ @ _) (R2 := inj)).
    rewrite (commute_around (_ @ _) (R2 := vainj)).
    reflexivity.
  }
  repeat (rstep; [rauto | ]).
  etransitivity.
  {
    (* Now we can expand the intermediate [inj] for the rest *)
    rewrite !cc_compose_assoc.
    rewrite <- inj_ext, cc_asm_compose, cc_compose_assoc.
    rewrite <- ext_inj, cc_asm_compose, cc_compose_assoc.
    rewrite <- ext_inj, cc_asm_compose, cc_compose_assoc.
    do 4 rewrite (commute_around cc_mach_asm).
    do 2 rewrite (commute_around cc_locset_mach).
    do 1 rewrite (commute_around cc_c_locset).
    rewrite <- (cc_compose_assoc lessdef_c), lessdef_c_cklr.
    rewrite <- wt_loc_out_of_thin_air, cc_compose_assoc.
    reflexivity.
  }
  reflexivity.
Qed.

Lemma cc_compcert_collapse:
  ccref
    (cc_dom @                                     (* Passes up to Alloc *)
     (wt_c @ cc_c ext @ cc_c_locset) @            (* Alloc *)
     cc_locset ext @                              (* Tunneling *)
     (wt_loc @ cc_locset injp @ cc_locset_mach) @ (* Stacking *)
     (cc_mach ext @ cc_mach_asm) @                (* Asmgen *)
     cc_asm vainj)
    cc_compcert.
Proof.
  rewrite <- wt_loc_out_of_thin_air.
  rewrite <- (cc_compose_assoc wt_loc) at 1.
  rewrite <- (cc_compose_assoc (wt_loc @ _)) at 1.
  rewrite (cc_compose_assoc wt_loc) at 1.
  rewrite (inv_drop (cc_locset injp) wt_loc), (cc_compose_assoc _ wt_loc).
  rewrite wt_loc_out_of_thin_air, !cc_compose_assoc.
  rewrite !(commute_around cc_locset_mach).
  unfold cc_dom, cc_cod. rewrite !cc_compose_assoc.
  rewrite <- (cc_compose_assoc inj).
  rewrite <- (cc_compose_assoc (_ @ _)).
  rewrite <- (cc_compose_assoc wt_c).
  rewrite (inv_drop _ wt_c), !cc_compose_assoc.
  rewrite !(commute_around cc_c_locset).
  rewrite <- (lessdef_c_cklr ext), cc_compose_assoc, <- (cc_compose_assoc wt_c) at 1.
  rewrite !(commute_around (wt_c @ lessdef_c)), cc_compose_assoc.
  rewrite !cc_star_absorb_r by eauto with cc.
  reflexivity.
Qed.

(** To compose the early passes in a flexible and incremental way,
  we maintain a simulation convention of the form [cc_dom -->> cc_cod],
  which is stable under composition with various kinds of passes. *)

Lemma cc_cod_inj:
  ccref cc_cod (cc_c inj @ cc_cod).
Proof.
  unfold cc_cod.
  rewrite inj_inj, cc_c_compose, cc_compose_assoc at 1.
  rewrite <- (lessdef_c_cklr inj), cc_compose_assoc, <- (cc_compose_assoc wt_c) at 1.
  rewrite (commute_around (_ @ _)), cc_compose_assoc.
  rewrite <- (cc_compose_assoc lessdef_c), lessdef_c_cklr.
  reflexivity.
Qed.

Lemma cc_cod_ext:
  ccref cc_cod (cc_c ext @ cc_cod).
Proof.
  unfold cc_cod.
  rewrite <- ext_inj, cc_c_compose, cc_compose_assoc at 1.
  rewrite <- (lessdef_c_cklr ext), cc_compose_assoc, <- (cc_compose_assoc wt_c) at 1.
  rewrite (commute_around (_ @ _)), cc_compose_assoc.
  rewrite <- (cc_compose_assoc lessdef_c), lessdef_c_cklr.
  reflexivity.
Qed.

Lemma cc_cod_wt:
  ccref cc_cod (wt_c @ cc_cod).
Proof.
  unfold cc_cod.
  rewrite (inv_dup wt_c), !cc_compose_assoc at 1.
  reflexivity.
Qed.

Lemma cc_cod_vamatch:
  ccref cc_cod (inj @ vamatch @ ext @ inj @ cc_cod).
Proof.
  unfold cc_cod.
  rewrite vainj_vainj, vainj_inj, !cc_c_compose at 1.
  rewrite !cc_compose_assoc.
  rewrite <- (lessdef_c_cklr inj), cc_compose_assoc, <- (cc_compose_assoc wt_c) at 1.
  do 2 rewrite (commute_around (_ @ _)). rewrite cc_compose_assoc.
  rewrite <- (cc_compose_assoc lessdef_c), lessdef_c_cklr.
  rewrite vainj_va_inj, cc_compose_assoc at 1.
  rewrite <- ext_inj at 2. rewrite cc_c_compose, cc_compose_assoc.
  reflexivity.
Qed.

Lemma cc_dom_injp:
  ccref (cc_c injp @ cc_dom) cc_dom.
Proof.
  unfold cc_dom.
  rewrite cc_star_absorb_l; eauto with cc.
Qed.

Lemma cc_dom_ext:
  ccref (cc_c ext @ cc_dom) cc_dom.
Proof.
  unfold cc_dom.
  rewrite cc_star_absorb_l; eauto with cc.
Qed.

Lemma cc_dom_wt:
  ccref (wt_c @ cc_dom) cc_dom.
Proof.
  unfold cc_dom, cc_cod.
  do 2 rewrite <- cc_compose_assoc at 1. rewrite (cc_compose_assoc wt_c).
  unfold cc_cklrs. rewrite (inv_drop _ wt_c), cc_compose_assoc.
  reflexivity.
Qed.

Lemma cc_dom_vamatch:
  ccref (inj @ vamatch @ ext @ inj @ cc_dom) cc_dom.
Proof.
  rewrite <- (cc_compose_assoc vamatch), <- vaext_va_ext. unfold cc_dom.
  rewrite !cc_star_absorb_l; eauto with cc.
Qed.

(** The following collection of lemmas can then be used to pre-compose
  a variety of passes. *)

Section COMPOSE_C_PASSES.

Context {li} (ccA ccB: callconv li_c li).

Lemma compose_clight_properties prog tsem:
  forward_simulation (cc_dom @ ccA) (cc_cod @ ccB) (Clight.semantics1 prog) tsem ->
  forward_simulation (cc_dom @ ccA) (cc_dom @ ccB) (Clight.semantics1 prog) tsem.
Proof.
  unfold cc_dom. intro.
  rewrite <- cc_star_idemp at 1.
  rewrite !cc_compose_assoc at 1.
  rewrite !cc_compose_assoc in H.
  eapply compose_forward_simulations; eauto.
  eapply cc_star_fsim.
  repeat eapply cc_join_fsim;
    (eapply open_fsim_ccref;
     [ | reflexivity | eapply Clightrel.semantics1_rel];
     eauto with cc).
Qed.

Lemma compose_injection_pass sem bsem tsem:
  forward_simulation (cc_c injp) (cc_c inj) sem bsem ->
  forward_simulation (cc_dom @ ccA) (cc_cod @ ccB) bsem tsem ->
  forward_simulation (cc_dom @ ccA) (cc_cod @ ccB) sem tsem.
Proof.
  intros.
  rewrite <- cc_dom_injp, cc_cod_inj, !cc_compose_assoc.
  eapply compose_forward_simulations; eauto.
Qed.

Lemma compose_extension_pass sem bsem tsem:
  forward_simulation (cc_c ext) (cc_c ext) sem bsem ->
  forward_simulation (cc_dom @ ccA) (cc_cod @ ccB) bsem tsem ->
  forward_simulation (cc_dom @ ccA) (cc_cod @ ccB) sem tsem.
Proof.
  intros.
  rewrite <- cc_dom_ext, cc_cod_ext, !cc_compose_assoc.
  eapply compose_forward_simulations; eauto.
Qed.

Lemma compose_selection_pass sem bsem tsem:
  forward_simulation (wt_c @ cc_c ext) (wt_c @ cc_c ext) sem bsem ->
  forward_simulation (cc_dom @ ccA) (cc_cod @ ccB) bsem tsem ->
  forward_simulation (cc_dom @ ccA) (cc_cod @ ccB) sem tsem.
Proof.
  intros.
  rewrite <- cc_dom_wt, cc_cod_wt, !cc_compose_assoc.
  rewrite <- cc_dom_ext, cc_cod_ext, !cc_compose_assoc.
  rewrite <- !(cc_compose_assoc wt_c).
  eapply compose_forward_simulations; eauto.
Qed.

Lemma compose_va_pass p bp tsem:
  let sem := RTL.semantics p in
  let bsem := RTL.semantics bp in
  forward_simulation (vamatch @ cc_c ext) (vamatch @ cc_c ext) sem bsem ->
  forward_simulation (cc_dom @ ccA) (cc_cod @ ccB) bsem tsem ->
  forward_simulation (cc_dom @ ccA) (cc_cod @ ccB) sem tsem.
Proof.
  intros.
  rewrite <- cc_dom_vamatch, cc_cod_vamatch, !cc_compose_assoc.
  eapply compose_forward_simulations; eauto. { eapply RTLrel.semantics_rel. }
  rewrite <- !(cc_compose_assoc vamatch).
  eapply compose_forward_simulations; eauto.
  eapply compose_forward_simulations; eauto. { eapply RTLrel.semantics_rel. }
Qed.

Lemma compose_backend_passes p tsem:
  let sem := RTL.semantics p in
  RTLtyping.wt_program p ->
  forward_simulation ccA ccB sem tsem ->
  forward_simulation (cc_dom @ ccA) (cc_cod @ ccB) sem tsem.
Proof.
  intros.
  eapply compose_forward_simulations; eauto.
  unfold cc_dom, cc_cod.
  rewrite <- cc_id_star, cc_compose_id_left.
  repeat eapply compose_forward_simulations.
  - eapply preserves_fsim, RTLtyping.rtl_wt; auto.
  - eapply RTLrel.semantics_rel.
  - eapply RTLrel.semantics_rel.
Qed.

End COMPOSE_C_PASSES.

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
  assert (F: forward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics p19)).
  {
  rewrite cc_compcert_expand at 2.
  rewrite <- cc_compcert_collapse at 1.
  eapply compose_clight_properties.
  eapply compose_injection_pass.
    eapply SimplLocalsproof.transf_program_correct; eassumption.
  eapply compose_identity_pass.
    eapply Cshmgenproof.transl_program_correct; eassumption.
  eapply compose_injection_pass.
    eapply Cminorgenproof.transl_program_correct; eassumption.
  eapply compose_selection_pass.
    eapply Selectionproof.transf_program_correct; eassumption.
  eapply compose_extension_pass.
    eapply RTLgenproof.transf_program_correct; eassumption.
  eapply compose_optional_pass; eauto using compose_extension_pass.
    exact Tailcallproof.transf_program_correct.
  eapply compose_injection_pass.
    eapply Inliningproof.transf_program_correct; eassumption.
  eapply compose_identity_pass.
    eapply Renumberproof.transf_program_correct; eassumption.
  eapply compose_optional_pass; eauto using compose_va_pass.
    exact Constpropproof.transf_program_correct.
  eapply compose_optional_pass; eauto using compose_identity_pass.
    exact Renumberproof.transf_program_correct.
  eapply compose_optional_pass; eauto using compose_va_pass.
    exact CSEproof.transf_program_correct.
  eapply compose_optional_pass; eauto using compose_va_pass.
    exact Deadcodeproof.transf_program_correct; eauto.
  eapply compose_backend_passes; eauto using Allocproof.wt_prog.
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
