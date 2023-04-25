Require Import Coqlib Integers AST Memdata Maps.
Require Import Asm Asmgen.
Require Import Errors.
Require Import Memory.
Require Import TargetPrinterAux.
Import ListNotations.

Local Open Scope error_monad_scope.
Close Scope nat_scope.

Definition transf_instr (sg:signature) (i: instruction): list instruction :=
  match i with
  | Pallocframe sz ra_ofs link_ofs =>
    match sg.(sig_cc).(cc_vararg) with
    | Some _ =>
      let i1 := [Pmv X30 X2] in
      let n := arguments_size sg in
      (* determine if registers from x10 to x17 are all used for non-variaidc arguments, otherwise we should alloc extra place to save the variadic arguments to the stack whose starting offset is pass to va_list (since we do not know the exact size of the number of variadic arguments, we should save all the unused registers from x10 to x17) *)      
      let extra_size := if n >=? 8 then 0 else align ((8-n) * wordsize) 16 in
      let full_sz := Z.add sz extra_size in
      let i2 := expand_addptrofs X2 X2 (Ptrofs.repr (-full_sz)) in
      (* store return address of the current function and remove the store ra in the Asmgen.v *)
      let i_ra := expand_storeind_ptr X1 X2 ra_ofs in
      let i3 := expand_storeind_ptr X30 X2 link_ofs in
      (* the starting offset of the va_list. It may be greater than full_sz  *)
      let va_ofs := Z.add full_sz ((n - 8) * wordsize) in
      let i4 := save_arguments (Z.to_nat n) va_ofs in
      i1 ++ i2 ++ i_ra ++ i3 ++ i4
    | None =>
      (* X30 is temporary varaible storing the parent stack pointer *)
      [Pmv X30 X2] ++ expand_addptrofs X2 X2 (Ptrofs.repr (-sz)) ++ expand_storeind_ptr X1 X2 ra_ofs ++ expand_storeind_ptr X30 X2 link_ofs
    end
  | Pfreeframe sz ra_ofs ofs =>
    let extra_sz :=
        match sg.(sig_cc).(cc_vararg) with
        | Some _ =>
          let n := arguments_size sg in
          if n >=? 8 then 0 else align ((8-n) * wordsize) 16
        | None => 0
        end in
    (* load return address *)
    loadind_ptr X2 ra_ofs X1 (expand_addptrofs X2 X2 (Ptrofs.repr (Z.add sz extra_sz)))
  | _ => [i]
  end.

Definition transf_code (sg: signature) (c: code) : code :=
  concat (map (transf_instr sg) c).

Definition transf_function (f: function) :=
  {|
    fn_sig := fn_sig f;
    fn_code := transf_code f.(fn_sig) (fn_code f);
    fn_stacksize := fn_stacksize f;
    (* fn_ofs_link := fn_ofs_link f; *)
  |}.

Definition transf_fundef := AST.transf_fundef transf_function.

Definition transf_program (p: Asm.program) : Asm.program :=
  AST.transform_program transf_fundef p.
