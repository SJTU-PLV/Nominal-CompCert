Require Import Coqlib Maps AST Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgram Globalenvs.
Require Import Locations Stacklayout Conventions.
Require Import Linking Errors.
Require Import LocalLib.

(** Global environments using only the symbol table *)

Definition gdef := globdef Asm.fundef unit.

Module Genv.

Section GENV.

(* we use CompCert configuration technique to parameterize instruction type *)
Record t: Type := mkgenv {
  genv_symb: PTree.t (block * ptrofs);        (**r mapping symbol -> block * ptrofs *)
  genv_ext_funs: NMap.t (option external_function);             (**r mapping blocks -> external function defintions *)
  genv_instrs: NMap.t (ptrofs -> option instruction);    (**r mapping block  -> instructions mapping *)

  genv_senv : Globalenvs.Senv.t; (**r symbol env *)
}.

(** ** Lookup functions *)

Definition find_symbol (ge: t) (id: ident) : option (block * ptrofs):=
  PTree.get id ge.(genv_symb).

Definition symbol_address (ge: t) (id: ident) (ofs: ptrofs) : val :=
  match find_symbol ge id with
  | Some (b, o) => Vptr b (Ptrofs.add ofs o)
  | None => Vundef
  end.

Definition find_ext_funct (ge: t) (v:val) : option external_function :=
  match v with
  | Vptr b ofs =>
    if Ptrofs.eq ofs Ptrofs.zero then
      NMap.get _ b ge.(genv_ext_funs)
    else None
  | _ => None
  end.

Lemma symbol_address_offset : forall ge ofs1 b s ofs,
    symbol_address ge s Ptrofs.zero = Vptr b ofs ->
    symbol_address ge s ofs1 = Vptr b (Ptrofs.add ofs ofs1).
Proof.
  unfold symbol_address. intros. 
  destruct (find_symbol ge s) eqn:FSM.
  - 
    destruct p.
    inv H.
    rewrite Ptrofs.add_zero_l. rewrite Ptrofs.add_commut. auto.
  - 
    inv H.
Qed.

Lemma find_sym_to_addr : forall (ge:t) id b ofs,
    find_symbol ge id = Some (b, ofs) ->
    symbol_address ge id Ptrofs.zero = Vptr b ofs.
Proof.
  intros. unfold symbol_address. rewrite H.
  rewrite Ptrofs.add_zero_l. auto.
Qed.

(** Find an instruction at an offset *)
Definition find_instr (ge: t) (v:val) : option instruction :=
  match v with
  | Vptr b ofs => genv_instrs ge b ofs
  | _ => None
  end.

End GENV.

End Genv.
