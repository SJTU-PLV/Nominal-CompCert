Require Import Integers Values Memory.
Require Import Clight.
Require Import InjectFootprint Invariant ValueAnalysis.
Require Import CA Asm CallConv CKLRAlgebra.
Require Import ClientMR Server Serverspec.
Require Import Smallstep Linking SmallstepLinking.
Require Import LanguageInterface.
(** * C-level composed specification *)

Definition result_def_unit :=
  {|
    gvar_info := tt;
    gvar_init := nil;
    gvar_readonly := false;
    gvar_volatile := false |}.

Compute (link (skel (Clight.semantics1 client)) (skel L2)).

Definition linked_skel2 : program unit unit:=
  {|
    prog_defs := (result_id, Gvar result_def_unit) :: (key_id, Gvar key_def_const) ::
                   (request_id, Gfun tt) :: (encrypt_id, Gfun tt) ::
                   (process_id, Gfun tt) :: nil;
    prog_public := encrypt_id :: request_id :: process_id :: result_id ::
                     key_id :: encrypt_id :: process_id :: nil;
    prog_main := 42%positive
  |}.

Compute linked_skel2.

Theorem link_ok2 :
  link (skel (Clight.semantics1 client)) (skel L2) = Some linked_skel2.
Proof. simpl.  unfold erase_program,linked_skel2.  simpl. Transparent Linker_prog. simpl. unfold link_prog. simpl. reflexivity. Qed.


Definition L := fun i : bool => if i then (Clight.semantics1 client) else L2.
Definition composed_spec2 := semantics L linked_skel2.

Theorem link_result :
  compose (Clight.semantics1 client) L2 = Some composed_spec2.
Proof.
  unfold compose. rewrite link_ok2. simpl. reflexivity.
Qed.

