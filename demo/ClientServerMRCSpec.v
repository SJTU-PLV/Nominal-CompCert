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

Definition input_index_def_unit :=
  {|
    gvar_info := tt;
    gvar_init := nil;
    gvar_readonly := false;
    gvar_volatile := false |}.

Compute (link (skel (Clight.semantics1 client)) (skel L2)).

Definition linked_skel2 : program unit unit:=
  {|
    prog_defs := (result_id, Gvar result_def_unit) :: (key_id, Gvar key_def_const) ::
                   (input_id, Gvar input_index_def_unit) ::
                   (encrypt_id, Gfun tt) :: (request_id, Gfun tt) ::
                   (index_id, Gvar input_index_def_unit) :: nil;
    prog_public := encrypt_id :: request_id :: input_id :: result_id :: index_id ::
                     key_id :: encrypt_id :: complete_id :: nil;
    prog_main := 42%positive
  |}.

Compute linked_skel2.

Theorem link_ok2 :
  link (skel (Clight.semantics1 client)) (skel L2) = Some linked_skel2.
Proof. reflexivity. Qed.

Definition L := fun i : bool => if i then (Clight.semantics1 client) else L2.
Definition composed_spec2 := semantics L linked_skel2.

Theorem link_result :
  compose (Clight.semantics1 client) L2 = Some composed_spec2.
Proof.
  unfold compose. rewrite link_ok2. simpl. reflexivity.
Qed.

