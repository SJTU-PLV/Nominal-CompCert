Require Import Coqlib Integers AST Memdata Maps.
Require Import Conventions1 Asm Asmgen.
Require Import Errors.
Require Import Memory.
Require Import TargetPrinterAux.
Import ListNotations.

Local Open Scope error_monad_scope.

(** RISCV calling conventions require that some floating point arguments are passed by the integers register but CompCert only reserve these registers in F0-F7. So fix-up code moves the floating-point arguments residing in FP registers need to integer registers or register pairs *)
(* Symmetrically, at function entry points, some floating-point parameter passed in integer registers or register pairs need to be moved to FP registers. *)

Definition move_single_arg fr i :=
  let r := nth i int_param_regs X10 in
  [Pfmvxs r fr].

Definition move_double_arg fr i :=
  let r := nth i int_param_regs X10 in
  if Archi.ptr64 then    
    [Pfmvxd r fr]
  else
    (* use extra space to temporaryly store the double *) 
    let i1 := [Paddiw X2 (X X2) (Int.repr (-16)); Pfsd fr X2 (Ofsimm Ptrofs.zero); Plw r X2 (Ofsimm Ptrofs.zero)] in
    let i2 :=
        if Nat.ltb i 7%nat then
          let r1 := nth (S i) int_param_regs X10 in
          [Plw r1 X2 (Ofsimm (Ptrofs.repr 4))]
        else
          (* 4 bytes in X17, 4 bytes in stack which is reserved by CompCert *)
          [Plw X31 X2 (Ofsimm (Ptrofs.repr 4)); Psw X31 X2 (Ofsimm (Ptrofs.repr 16))] in
    (* recycle the stack *)
    let i3 := [Paddiw X2 (X X2) (Int.repr 16)] in
    i1 ++ i2 ++ i3.

Definition move_single_param fr i :=
  let r := nth i int_param_regs X10 in
  [Pfmvsx fr r].

Definition move_double_param fr i :=
  let r := nth i int_param_regs X10 in
  if Archi.ptr64 then
    [Pfmvdx fr r]
  else
    let i1 := [Paddiw X2 (X X2) (Int.repr (-16)); Psw r X2 (Ofsimm Ptrofs.zero)] in
    let i2 :=
        if Nat.ltb i 7%nat then
          let r1 := nth (S i) int_param_regs X10 in
          [Psw r1 X2 (Ofsimm (Ptrofs.repr 4))]
        else
          [Plw X31 X2 (Ofsimm (Ptrofs.repr 4)); Psw X31 X2 (Ofsimm (Ptrofs.repr 16))] in
    let i3 := [Pfld fr X2 (Ofsimm Ptrofs.zero); Paddiw X2 (X X2) (Int.repr 16)] in
    i1 ++ i2 ++ i3.
                
          
Definition float_extra_index r : option (freg * nat) :=
  match r with
  | Machregs.F0 => Some (F0, 0%nat)
  | Machregs.F1 => Some (F1, 1%nat)
  | Machregs.F2 => Some (F2, 2%nat)
  | Machregs.F3 => Some (F3, 3%nat)
  | Machregs.F4 => Some (F4, 4%nat)
  | Machregs.F5 => Some (F5, 5%nat)
  | Machregs.F6 => Some (F6, 6%nat)
  | Machregs.F7 => Some (F7, 7%nat)
  | _  => None
  end.

Fixpoint fixup_gen (single double: freg -> nat -> list instruction)  (args: list typ)  (locs: list (rpair Locations.loc)) :=
  match args, locs with
  | [],[] => []
  | Tsingle :: args', One (Locations.R r) :: locs' =>
    match float_extra_index r with
    | Some (r, i) => single r i ++ fixup_gen single double args' locs'
    | None => fixup_gen single double args' locs'
    end
  | Tfloat :: args', One (Locations.R r) :: locs'
  | Tany64 :: args', One (Locations.R r) :: locs' =>
    match float_extra_index r with
    | Some (r, i) => double r i ++ fixup_gen single double args' locs'
    | None => fixup_gen single double args' locs'
    end
  | _ :: args', _ :: locs' =>
    fixup_gen single double args' locs'
  | _,_ => []
  end.

Definition fixup_call sg :=
  fixup_gen move_single_arg move_double_arg sg.(sig_args) (loc_arguments sg).

Definition fixup_function_entry sg :=
  fixup_gen move_single_param move_double_param sg.(sig_args) (loc_arguments sg).

Definition transf_instr i :=
  match i with
  | Pjal_r r sg =>
    fixup_call sg ++ [i]
  | Pjal_s symb sg =>
    fixup_call sg ++ [i]
  | Pj_r r sg =>
    if preg_eq r X1 then
      [i]
    else
      fixup_call sg ++ [i]
  | Pj_s symb sg =>
    fixup_call sg ++ [i]
  | _ => [i]
  end.


Definition transf_code (sg: signature) (c: code) : code :=
  concat (map transf_instr c).

Definition transf_function (f: function) :=
  {|
    fn_sig := fn_sig f;
    fn_code := fixup_function_entry (fn_sig f) ++ transf_code f.(fn_sig) (fn_code f);
    fn_stacksize := fn_stacksize f;
  |}.

Definition transf_fundef := AST.transf_fundef transf_function.

Definition transf_program (p: Asm.program) : Asm.program :=
  AST.transform_program transf_fundef p.         


