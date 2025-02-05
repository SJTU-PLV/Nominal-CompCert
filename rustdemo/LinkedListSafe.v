Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Cop RustOp.
Require Import Ctypes Rusttypes Rustlight.
Require Import LinkedList.
Require Import Values Globalenvs Memory.
Require Import Smallstep Rustlightown SmallstepLinkingSafe.


Local Open Scope error_monad_scope.
Import ListNotations.

Definition linked_list_sem := semantics linked_list_mod.

Section SOUNDNESS.

Context (se : Genv.symtbl).

Let ge := globalenv se linked_list_mod.

Inductive sound_find_cont : cont -> Prop :=
| sound_find_Kstop:
    sound_find_cont Kstop
| sound_find_Kcall: forall k p f e own s,
    sound_find_cont k ->
      (* TODO: specify the statement *)
    sound_find_cont (Kcall p f e own (Kseq s k)).

Definition sound_cont (f: ident) : cont -> Prop :=
  if ident_eq f find then
    sound_find_cont
  else
    fun _ => False.

Inductive call_func (f: ident) : state -> Prop :=
| call_func_intro: forall b ofs vl k m,
    Genv.invert_symbol se b = Some f ->
    (** TODO: some property of k *)
    sound_cont f k ->
    call_func f (Callstate (Vptr b ofs) vl k m).

(* continuation of the returnstate in find function *)
Inductive find_cont_ret : cont -> Prop :=
(* return the current find function *)
| find_return1: forall k,
    sound_find_cont k ->
    find_cont_ret k
(* return from find *)
| find_return2: forall k p f e own s,
    sound_find_cont k ->
    (* TODO: specify the statement *)
    find_cont_ret (Kcall p f e own (Kseq s k))
(* return from process *)
| find_return3: forall k p f e own s,
    sound_find_cont k ->
    (* TODO: specify the statement *)
    find_cont_ret (Kcall p f e own (Kseq s k))
.

(* returnstate in find function *)
Inductive return_find : state -> Prop :=
| return_find_intro: forall k v m,
    find_cont_ret k ->
    return_find (Returnstate v k m).

Inductive sound_state : state -> Prop :=
| 
