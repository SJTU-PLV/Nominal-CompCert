Require Import Coqlib Integers AST Memdata Maps.
Require Import Asm Asmgen.
Require Import Errors.
Require Import Memory.
Import ListNotations.

Definition expand_addptrofs dst src n :=
  addptrofs dst src n [].

Definition expand_storeind_ptr src base ofs :=
  storeind_ptr src base ofs [].

(* argument size *)
Definition arg_int_size (ri rf ofs: Z) k : Z*Z*Z :=
  if ri <? 8 then k (ri + 1) rf ofs
  else k ri rf (ofs + 1).

Definition arg_single_size (ri rf ofs:Z) k : Z*Z*Z :=
  if rf <? 8 then k ri (rf+1) ofs
  else arg_int_size ri rf ofs k.

Definition arg_long_size (ri rf ofs: Z) k :Z*Z*Z:=
  if Archi.ptr64 then
    if ri <? 8 then k (ri + 1) rf ofs
    else k ri rf (ofs + 1)
  else
    if ri <? 7 then k (ri + 2) rf ofs
    else if ri =? 7 then k (ri + 1) rf (ofs + 1)
         else k ri rf (align ofs 2 + 2).

Definition arg_double_size (ri rf ofs:Z) k : Z*Z*Z :=
  if rf <? 8 then k ri (rf + 1) ofs
  else arg_long_size ri rf ofs k.

Fixpoint args_size l ri rf ofs :=
  match l with
  | [] => (ri,rf,ofs)
  | Tint :: l
  | Tany32 :: l =>
    arg_int_size ri rf ofs (args_size l)
  | Tsingle :: l =>
    arg_single_size ri rf ofs (args_size l)
  | Tlong :: l =>
    arg_long_size ri rf ofs (args_size l)
  | Tfloat :: l
  | Tany64 :: l =>
    arg_double_size ri rf ofs (args_size l)
  end.

Definition arguments_size sg :=
  let '(ri,_,ofs) := args_size sg.(sig_args) 0 0 0 in
  ri + ofs.

Definition int_param_regs := [X10; X11; X12; X13; X14; X15; X16; X17]. 

Definition wordsize := if Archi.ptr64 then 8 else 4.

Fixpoint save_arguments_rec regs i base_ofs :=
  match regs with
  | [] => []
  | r :: l =>
    expand_storeind_ptr r X2 (Ptrofs.repr (Z.add base_ofs (i * wordsize))) ++ save_arguments_rec l (i+1) base_ofs
  end.
      
Definition save_arguments first_reg base_ofs :=
  let regs := skipn first_reg int_param_regs in
  save_arguments_rec regs 0 base_ofs.

