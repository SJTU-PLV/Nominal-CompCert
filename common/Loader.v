Require Import AST.
Require Import Values.
Require Import Integers.
Require Import LanguageInterface.
Require Import Globalenvs.
Require Import Smallstep.

Definition semantics (L: open_sem li_c li_c) se id m: Smallstep.semantics li_null int :=
  let q := cq (Vptr id Ptrofs.zero) signature_main nil m in
  {|
    step := step (L se q);
    initial_state := initial_state (L se q);
    final_state s r := exists c, final_state (L se q) s c /\ cr_retval c = Vint r;
    at_external _ _ := False;
    after_external _ _ _ := False;
    globalenv := globalenv (L se q);
  |}.

Definition load (L: open_sem li_c li_c): option closed_sem :=
  let se := Genv.globalenv (skel L) in
  match Genv.find_symbol se (prog_main (skel L)), Genv.init_mem (skel L) with
    | Some id, Some m => Some {| csem := semantics L se id m; symbolenv := se |}
    | _, _ => None
  end.
