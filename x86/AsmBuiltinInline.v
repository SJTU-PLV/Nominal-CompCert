Require Import Coqlib Integers AST Memdata Maps.
Require Import Events.
Require Import Asm Asmgen.
Require Import Errors.
Require Import Memtype.
Require Import Globalenvs.
Require Import String.
Require Import AsmLabelNew.
Require Import Conventions1.
Require Import Machregs.
Require Import PseudoInstructions.
Import ListNotations.

Local Open Scope error_monad_scope.

Section FUNCTION_SG.

Variables (cur_func: function).
  
Definition option_ffpu := true.

Definition _Plea r addr :=
  if Archi.ptr64 then Pleaq r addr else Pleal r addr.

Definition linear_addr reg ofs := 
  Addrmode (Some reg) None (inl ofs).

Definition global_addr id ofs := 
  Addrmode None None (inr(id, ofs)).

Definition addressing_of_builtin_arg (arg: builtin_arg preg) :res addrmode := 
  match arg with
  | BA (IR r) => OK (linear_addr r 0)
  | BA_addrstack ofs => OK (linear_addr RSP (Ptrofs.unsigned ofs))
  | BA_addrglobal id ofs => OK (global_addr id ofs)
  | BA_addptr (BA (IR r)) (BA_int n) => OK (linear_addr r (Int.unsigned n) )
  | BA_addptr (BA (IR r)) (BA_long n) => OK (linear_addr r (Int64.unsigned n) )
  | _ => Error (msg "addressing_of_builtin_arg: builtin argument not sup
ported")
  end.

Definition offset_addressing a delta :=
  let '(Addrmode base ofs cst) := a in
  let disp :=            
      match cst with
      | inl n => inl (n + delta)
      | inr (id, n) => inr (id, Ptrofs.add n (Ptrofs.repr delta))
      end in
  Addrmode base ofs disp.

(* Handling of memcpy *)

(* Unaligned memory accesses are quite fast on IA32, so use large
   memory accesses regardless of alignment. *)

Fixpoint copy (fuel:nat) (src dst:addrmode) (sz:Z) : res (list instruction) :=
  match fuel with
  | O => OK []
  | S fuel' =>
    if zle 8 sz && Archi.ptr64 then 
      do instrs <- copy fuel' (offset_addressing src 8) (offset_addressing dst 8) (sz - 8);
      OK ([Pmovq_rm RCX src; Pmovq_mr dst RCX] ++ instrs)
    else if zle 8 sz && option_ffpu then 
      do instrs <- copy fuel' (offset_addressing src 8) (offset_addressing dst 8) (sz - 8);
      OK ([Pmovsq_rm XMM7 src; Pmovsq_mr dst XMM7] ++ instrs)
    else if zle 4 sz then 
      do instrs <- copy fuel' (offset_addressing src 4) (offset_addressing dst 4) (sz - 4);
      OK ([Pmovl_rm RCX src; Pmovl_mr dst RCX] ++ instrs)
    else if zle 2 sz then
      do instrs <- copy fuel' (offset_addressing src 2) (offset_addressing dst 2) (sz - 2);
      OK ([Pmovw_rm RCX src; Pmovw_mr dst RCX] ++ instrs)
    else if zle 1 sz then
      do instrs <- copy fuel' (offset_addressing src 1) (offset_addressing dst 1) (sz - 1);
      OK ([Pmovb_rm RCX src; Pmovb_mr dst RCX] ++ instrs)
    else 
      OK []
  end.

Definition expand_builtin_memcpy_small (sz al:Z) (src dst: builtin_arg preg) : res (list instruction) :=
  do asrc <- (addressing_of_builtin_arg src);
  do adst <- (addressing_of_builtin_arg dst);
  copy (Z.to_nat sz) asrc adst sz.

Definition crbit_arg_dec (c1 c2: crbit) : {c1 = c2} + {c1 <> c2}.
  decide equality.
Qed.

Definition builtin_arg_dec (a1 a2: builtin_arg preg) : {a1 = a2} + {a1 <> a2}.
  decide equality; try decide equality; try apply Ptrofs.eq_dec.
  - apply ireg_eq.
  - apply freg_eq.
  - apply crbit_arg_dec.
  - apply Int.eq_dec.
  - apply Int64.eq_dec.
  - apply Floats.Float.eq_dec.
  - apply Floats.Float32.eq_dec.
Qed.

Definition expand_builtin_memcpy_big (sz al:Z) (src dst: builtin_arg preg) : res (list instruction) :=
  do sinstrs <-
      if builtin_arg_dec src (BA (IR RSI)) 
      then OK []
      else (do a <- addressing_of_builtin_arg src;
              OK [_Plea RSI a]);
  do dinstrs <-
      if builtin_arg_dec dst (BA (IR RDI))
      then OK []
      else (do a <- addressing_of_builtin_arg dst;
              OK [_Plea RDI a]);
  let i1 := Pmovl_ri RCX (Int.repr (sz / 4)) in
  let i2 := Prep_movsl in
  let is1 := if zle 2 (sz mod 4) then [Pmovsw] else [] in
  let is2 := if zle 1 (sz mod 2) then [Pmovsb] else [] in
  OK (sinstrs ++ dinstrs ++ [i1; i2] ++ is1 ++ is2).
  
Definition expand_builtin_memcpy (sz al:Z) (args: list (builtin_arg preg)) : res (list instruction) :=
  do r <-
     match args with 
     | [d; s] => OK (d, s) 
     | _ => Error (msg "Error in expanding builtin memcpy: Wrong number of arguments")
     end;
  let '(dst, src) := r in
  if zle sz 32 
  then expand_builtin_memcpy_small sz al src dst
  else expand_builtin_memcpy_big sz al src dst.

Definition expand_builtin_vload_common chunk addr res :=
  match chunk, res with
  | Mint8unsigned, BR(IR res) =>
     OK [Pmovzb_rm res addr]
  | Mint8signed, BR(IR res) =>
     OK [Pmovsb_rm res addr]
  | Mint16unsigned, BR(IR res) =>
     OK [Pmovzw_rm res addr]
  | Mint16signed, BR(IR res) =>
     OK [Pmovsw_rm res addr]
  | Mint32, BR(IR res) =>
     OK [Pmovl_rm res addr]
  | Mint64, BR(IR res) =>
     OK [Pmovq_rm res addr]
  | Mint64, BR_splitlong (BR(IR res1)) (BR(IR res2)) =>
     let addr' := offset_addressing addr 4 in
     if negb (Asmgen.addressing_mentions addr res2) then
       OK [Pmovl_rm res2 addr; Pmovl_rm res1 addr']
     else
       OK [Pmovl_rm res1 addr'; Pmovl_rm res2 addr] 
  | Mfloat32, BR(FR res) =>
     OK [Pmovss_fm res addr]
  | Mfloat64, BR(FR res) =>
     OK [Pmovsd_fm res addr]
  | _, _ =>
    Error [MSG "Error in expand_builtin_vload_common"]
  end.

Definition expand_builtin_vload chunk args res :=
  match args with
  | [addr] =>
    do addr' <- addressing_of_builtin_arg addr;
    expand_builtin_vload_common chunk addr' res
  | _ => Error [MSG "Error in expand_builtin_vload"]
  end.

Definition expand_builtin_vstore_common chunk addr src tmp:=
  match chunk, src with
  | (Mint8signed | Mint8unsigned), BA(IR src) =>
    if Archi.ptr64 || Asmgen.low_ireg src then
      OK [Pmovb_mr addr src]
    else
      OK [Pmov_rr tmp src; Pmovb_mr addr tmp]
  | (Mint16signed | Mint16unsigned), BA(IR src) =>
    OK [Pmovw_mr addr src]
  | Mint32, BA(IR src) =>
    OK [Pmovl_mr addr src]
  | Mint64, BA(IR src) =>
    OK [Pmovq_mr addr src]
  | Mint64, BA_splitlong (BA(IR src1)) (BA(IR src2)) =>
    let addr' := offset_addressing addr 4 in
    OK [Pmovl_mr addr src2; Pmovl_mr addr' src1]
  | Mfloat32, BA(FR src) =>
    OK [Pmovss_mf addr src]
  | Mfloat64, BA(FR src) =>
    OK [Pmovsd_mf addr src]
  | _, _ =>
    Error [MSG "Error in expand_builtin_vstore_common"]
  end.

Definition expand_builtin_vstore chunk args :=
  match args with
  | [addr; src] =>
    do addr' <- addressing_of_builtin_arg addr;
    let tmp := if Asmgen.addressing_mentions addr' RAX
               then RCX
               else RAX in
     expand_builtin_vstore_common chunk addr' src tmp
  | _ => Error [MSG "Error in expand_builtin_vstore"]
  end.

Definition expand_fma args result i132 i213 i231 :=
  match args, result with
  | [BA(FR a1); BA(FR a2); BA(FR a3)], BR(FR result) =>
    if freg_eq result a1 then
      OK [i132 a1 a3 a2] (* a1 * a2 + a3 *) else
      if freg_eq result a2 then
        OK [i213 a2 a1 a3] (* a1 * a2 + a3 *) else
        if freg_eq result a3 then
          OK [i231 a3 a1 a2] (* a1 * a2 + a3 *) else
          (* a1 * a2 + res *)
          OK [Pmovsd_ff result a3; i231 result a1 a2]
  | _, _ => Error [MSG "ill-formed fma builtin"]
  end.

(* Copy from ccelf-no-perm x86/Conventions1.v *)
(** [size_arguments s] returns the number of [Outgoing] slots used
  to call a function with signature [s]. *)

Definition int_param_regs := DI :: SI :: DX :: CX :: R8 :: R9 :: nil.
Definition float_param_regs := X0 :: X1 :: X2 :: X3 :: X4 :: X5 :: X6 :: X7 :: nil.

Fixpoint size_arguments_32
    (tyl: list typ) (ofs: Z) {struct tyl} : Z :=
  match tyl with
  | nil => ofs
  | ty :: tys => size_arguments_32 tys (ofs + typesize ty)
  end.

Fixpoint size_arguments_64 (tyl: list typ) (ir fr ofs: Z) {struct tyl} : Z :=
  match tyl with
  | nil => ofs
  | (Tint | Tlong | Tany32 | Tany64) :: tys =>
      match list_nth_z int_param_regs ir with
      | None => size_arguments_64 tys ir fr (ofs + 2)
      | Some ireg => size_arguments_64 tys (ir + 1) fr ofs
      end
  | (Tfloat | Tsingle) :: tys =>
      match list_nth_z float_param_regs fr with
      | None => size_arguments_64 tys ir fr (ofs + 2)
      | Some freg => size_arguments_64 tys ir (fr + 1) ofs
      end
  end.

Definition size_arguments (s: signature) : Z :=
  if Archi.ptr64
  then size_arguments_64 s.(sig_args) 0 0 0
  else size_arguments_32 s.(sig_args) 0.

(* End Copy *)

Definition expand_builtin_va_start_32 r :=
  if cc_vararg (sig_cc (fn_sig cur_func)) then
    (* fn_stacksize correct? set to 16 *)
    let sz := align (fn_stacksize cur_func) 16 - size_chunk Mptr in
    let t0 := Z.add sz 4 in
    (* let t0 := Z.add (fn_stacksize cur_func) 4 in *)
    (* fix bug: typesize definition different from ccelf-no-perm!! *)
    let t1 := (size_arguments (fn_sig cur_func)) in
    let ofs := Z.add t0 t1 in
    OK [Pleal RAX (linear_addr RSP ofs);
       Pmovl_mr (linear_addr r 0) RAX]
  else
    Error [MSG "Fatal error: va_start used in non-vararg function"].


Fixpoint next_arg_locations ir fr ofs l : (Z*Z*Z) :=
  match l with
  | [] => (ir,fr,ofs)
  | (Tint | Tlong | Tany32 | Tany64) :: l =>
    if Z.ltb ir 6
    then next_arg_locations (ir+1) fr ofs l
    else next_arg_locations ir fr (ofs+8) l
  | (Tfloat | Tsingle) :: l =>
    if Z.ltb fr 8
    then next_arg_locations ir (fr + 1) ofs l
    else next_arg_locations ir fr (ofs + 8) l
  end.


(** follow Asmexpand.ml  *)
Definition expand_builtin_va_start_64 r :=
  if cc_vararg (sig_cc (fn_sig cur_func)) then
    let '(ir,fr,ofs) := next_arg_locations 0 0 0 (cur_func.(fn_sig)).(sig_args) in
    (* function stack size should be the same as the sz var in Pallocframe  *)
    (* follow Asmexpand.ml: why add 8 ? I think that the size has minused 8 in sp_adjustment_elf64 *)
    let (current_function_stacksize, _) := (sp_adjustment_elf64 cur_func.(fn_sig) cur_func.(fn_stacksize)) in
    let current_function_stacksize := current_function_stacksize + 8 in
    let gp_offset := (ir * 8) in
    let fp_offset := (6 * 8 + fr * 16) in
    let overflow_data_area := current_function_stacksize + ofs in
    let reg_save_area := current_function_stacksize - 192 in
    if ireg_eq r RAX then
      Error [MSG "Builtin_va_start_64: r = RAX"]
    else
    OK [Pmovl_ri RAX (Int.repr gp_offset);
       Pmovl_mr (linear_addr r 0) RAX;
       Pmovl_ri RAX (Int.repr fp_offset);
       Pmovl_mr (linear_addr r 4) RAX;
       Pleaq RAX (linear_addr RSP (overflow_data_area));
       Pmovq_mr (linear_addr r 8) RAX;
       Pleaq RAX (linear_addr RSP (reg_save_area));
       Pmovq_mr (linear_addr r 16) RAX]
  else
    Error [MSG "Fatal error: va_start used in non-vararg function"].


    
(* Expand builtin inline assembly *)
Definition expand_builtin_inline name args res :=
  match name,args,res with
  (* Integer arithmetic *)
  | ("__builtin_bswap"%string | "__builtin_bswap32"%string), [BA(IR a1)], BR(IR a2) =>
    let i:= if negb (ireg_eq a1 a2) then
              [Pmov_rr a2 a1] else
              [] in
    OK (i++[Pbswap32 a2])
  | "__builtin_bswap64"%string, [BA(IR a1)], BR(IR a2) =>
    let i:= if negb (ireg_eq a1 a2) then
              [Pmov_rr a2 a1] else
              [] in
    OK (i++[Pbswap64 a2])
  | "__builtin_bswap64"%string, [BA_splitlong (BA(IR ah)) (BA(IR al))],
    BR_splitlong (BR(IR rh)) (BR(IR rl)) =>
    if (ireg_eq ah RAX && ireg_eq al RDX && ireg_eq rh RDX &&
        ireg_eq rl RAX) then
      OK [Pbswap32 RAX; Pbswap32 RDX]
    else
      Error (msg "Error in expanding of builtin: __builtin_bswap64 arguments incorrect")
  | "__builtin_bswap16"%string, [BA(IR a1)], BR(IR a2) =>
    let i:= if negb (ireg_eq a1 a2) then
              [Pmov_rr a2 a1] else
              [] in
    OK (i++[Pbswap16 a2])
  | ("__builtin_clz"%string|"__builtin_clzl"%string), [BA(IR a1)], BR(IR a2) =>
     OK [Pbsrl a2 a1; Pxorl_ri a2 (Int.repr 31)]
  | "__builtin_clzll"%string, [BA(IR a1)], BR(IR a2) =>
    OK [Pbsrq a2 a1; Pxorl_ri a2 (Int.repr 63)]
  | "__builtin_clzll"%string, [BA_splitlong (BA (IR ah)) (BA (IR al))], BR(IR ar) =>
    let lbl1 := new_label tt in
    let lbl2 := new_label tt in
    OK [Ptestl_rr ah ah; Pjcc Cond_e lbl1; Pbsrl ar ah; Pxorl_ri ar (Int.repr 31);
       Pjmp_l lbl2; Plabel lbl1; Pbsrl ar al; Pxorl_ri ar (Int.repr 63); Plabel lbl2]
  | ("__builtin_ctz"%string | "__builtin_ctzl"%string), [BA(IR a1)], BR(IR a2) =>
    OK [Pbsfl a2 a1]
  | "__builtin_ctzll"%string, [BA(IR a1)], BR(IR a2) =>
    OK [Pbsfq a2 a1]
  | "__builtin_ctzll"%string, [BA_splitlong (BA (IR ah)) (BA (IR al))], BR(IR ar) =>
    let lbl1 := new_label tt in
    let lbl2 := new_label tt in
    OK [Ptestl_rr al al; Pjcc Cond_e lbl1; Pbsfl ar al; Pjmp_l lbl2; Plabel lbl1;
       Pbsfl ar ah; Paddl_ri ar (Int.repr 32); Plabel lbl2]
  (* Float arithmetic *)
  | "__builtin_fabs"%string, [BA(FR a1)], BR(FR ar) =>
    let i:= if negb (freg_eq a1 ar) then
              [Pmovsd_ff ar a1] else
              [] in
    OK (i++[Pabsd ar])
  (* This ensuar that need_masks is set to true *)
  | "__builtin_fsqrt"%string, [BA(FR a1)], BR(FR ar)
  | "__builtin_sqrt"%string, [BA(FR a1)], BR(FR ar) =>
    OK [Psqrtsd ar a1]
  | "__builtin_fmax"%string, [BA(FR a1); BA(FR a2)], BR(FR ar) =>
    let i := [Pmovsd_ff ar a1; Pmaxsd ar a2] in
    if freg_eq ar a1 then
      OK ([Pmaxsd ar a2]++i) else
      if freg_eq ar a2 then
        OK ([Pmaxsd ar a1]++i) else
	OK i
  | "__builtin_fmin"%string, [BA(FR a1); BA(FR a2)], BR(FR ar) =>
    let i := [Pmovsd_ff ar a1; Pminsd ar a2] in
    if freg_eq ar a1 then
      OK ([Pminsd ar a2]++i) else
      if freg_eq ar a2 then
        OK ([Pminsd ar a1]++i) else
	OK i
  | "__builtin_fmadd"%string,  _, _ =>
      expand_fma args res
        (fun r1 r2 r3 => Pfmadd132 r1 r2 r3)
        (fun r1 r2 r3 => Pfmadd213 r1 r2 r3)
        (fun r1 r2 r3 => Pfmadd231 r1 r2 r3)
  | "__builtin_fmsub"%string,  _, _ =>
      expand_fma args res
        (fun r1 r2 r3 => Pfmsub132 r1 r2 r3)
        (fun r1 r2 r3 => Pfmsub213 r1 r2 r3)
        (fun r1 r2 r3 => Pfmsub231 r1 r2 r3)
  | "__builtin_fnmadd"%string,  _, _ =>
      expand_fma args res
        (fun r1 r2 r3 => Pfnmadd132 r1 r2 r3)
        (fun r1 r2 r3 => Pfnmadd213 r1 r2 r3)
        (fun r1 r2 r3 => Pfnmadd231 r1 r2 r3)
  | "__builtin_fnmsub"%string,  _, _ =>
      expand_fma args res
        (fun r1 r2 r3 => Pfnmsub132 r1 r2 r3)
        (fun r1 r2 r3 => Pfnmsub213 r1 r2 r3)
        (fun r1 r2 r3 => Pfnmsub231 r1 r2 r3)
  (* 64-bit integer arithmetic *)
  | "__builtin_negl"%string, [BA_splitlong (BA(IR ah)) (BA(IR al))],
    BR_splitlong (BR(IR rh)) (BR(IR rl)) =>
    if (ireg_eq ah RDX && ireg_eq al RAX && ireg_eq rh RDX &&
        ireg_eq rl RAX) then
      OK [Pnegl RAX; Padcl_ri RDX Int.zero; Pnegl RDX]
    else
      Error (msg "Error in expanding of builtin: __builtin_negl arguments incorrect")  
  | "__builtin_addl"%string, [BA_splitlong (BA(IR ah)) (BA(IR al));
                              BA_splitlong (BA(IR bh)) (BA(IR bl))],
    BR_splitlong (BR(IR rh)) (BR(IR rl)) =>
    if (ireg_eq ah RDX && ireg_eq al RAX && ireg_eq bh RCX &&
        ireg_eq bl RBX && ireg_eq rh RDX && ireg_eq rl RAX) then
      OK [Paddl_rr RAX RBX; Padcl_rr RDX RCX]
    else
      Error (msg "Error in expanding of builtin: __builtin_addl arguments incorrect")             
  | "__builtin_subl"%string, [BA_splitlong (BA(IR ah)) (BA(IR al));
                              BA_splitlong (BA(IR bh)) (BA(IR bl))],
    BR_splitlong (BR(IR rh)) (BR(IR rl)) =>
    if (ireg_eq ah RDX && ireg_eq al RAX && ireg_eq bh RCX &&
        ireg_eq bl RBX && ireg_eq rh RDX && ireg_eq rl RAX) then
      OK [Psubl_rr RAX RBX; Psbbl_rr RDX RCX]
    else
      Error (msg "Error in expanding of builtin: __builtin_subl arguments incorrect")
  | "__builtin_mull"%string, [BA(IR a); BA(IR b)],
    BR_splitlong (BR(IR rh)) (BR(IR rl)) =>
    if (ireg_eq a RAX && ireg_eq b RDX && ireg_eq rh RDX &&
        ireg_eq rl RAX) then
      OK [Pmull_r RDX]
    else
      Error (msg "Error in expanding of builtin: __builtin_mull arguments incorrect")
  (* Memory accesses *)
  | "__builtin_read16_reversed"%string, [BA(IR a1)], BR(IR ar) =>
     OK [Pmovzw_rm ar (linear_addr a1 0); Pbswap16 ar]
  | "__builtin_read32_reversed"%string, [BA(IR a1)], BR(IR ar)  =>
     OK [Pmovl_rm ar (linear_addr a1 0); Pbswap32 ar]
  | "__builtin_write16_reversed"%string, [BA(IR a1); BA(IR a2)], _  =>
    let tmp := if ireg_eq a1 RCX then RDX else RCX in
    let i := if negb (ireg_eq a2 tmp) then
               [Pmov_rr tmp a2] else
               [] in
    OK (i++[Pbswap16 tmp; Pmovw_mr (linear_addr a1 0) tmp])
  | "__builtin_write32_reversed"%string, [BA(IR a1); BA(IR a2)], _  =>
    let tmp := if ireg_eq a1 RCX then RDX else RCX in
    let i := if negb (ireg_eq a2 tmp) then
               [Pmov_rr tmp a2] else
               [] in
    OK (i++[Pbswap32 tmp; Pmovl_mr (linear_addr a1 0) tmp])
  (* Vararg stuff *)
  | "__builtin_va_start"%string, [BA(IR a)], _ =>
    if (ireg_eq a RDX) then
      if Archi.ptr64
      then expand_builtin_va_start_64 a
           (* then Error (msg "Error vaarg in x86_64") *)
      else expand_builtin_va_start_32 a       
    else
      Error (msg "Error in expanding of builtin: __builtin_va_start arguments incorrect")
  (* Synchronization *)
  | "__builtin_membar"%string, [], _ =>
    OK []
  (* no operation *)
  | "__builtin_nop"%string, [], _  =>
    OK [Pmov_rr RAX RAX]
  | _ ,_ ,_  =>  Error [MSG "Error in expanding of builtin: " ; MSG name]
  end.

Definition transf_instr (i: instruction): res (list instruction) :=
  match i with
  | Pbuiltin ef args res =>
    match ef with
    | EF_memcpy sz al =>
      expand_builtin_memcpy sz al args
    | EF_builtin name sg =>
      do i <- expand_builtin_inline name args res;
      OK i
    | EF_vload chunk =>
      expand_builtin_vload chunk args res
    | EF_vstore chunk =>
      expand_builtin_vstore chunk args
    | EF_annot (* SANCC *) _ text targs =>
      OK [Pnop]
    | EF_annot_val (* SANCC *) _ text targ =>
      OK [Pnop]
    | EF_inline_asm text sg clob =>
      Error [MSG "Unsupported Builtin Elimination: inline_asm"]
    | EF_debug kind text targs =>
      Error [MSG "Unsupported Builtin Elimination: debug"]
    | _ => Error [MSG "Unsupported Builtin Elimination: unknown"]
    end
  (** 64bit mode variant argument ,set %al=float register number
      follow Asmexpand.ml *)
  | Pjmp_s _ sg
  | Pjmp_r _ sg
  | Pcall_s _ sg
  | Pcall_r _ sg =>
  (*FIXME: add 64bit mode condition*)
    let '(ir, fr, ofs) := next_arg_locations 0 0 0 sg.(sig_args) in
    if (sg.(sig_cc)).(cc_unproto) then
      OK [Pmovl_ri RAX (Int.repr fr);i]
    else
      match (sg.(sig_cc)).(cc_vararg) with
      | Some _ =>                
        OK [Pmovl_ri RAX (Int.repr fr);i]
      | None => OK [i]
      end
  | _ => OK [i]
  end.

Definition acc_transl_instr (r:res code) (i:instruction) :=
  do acc_i <- r;
  do i' <- transf_instr i;
  OK (acc_i ++ i').
  
Definition transl_code (c:code) : res code :=
  do code <- fold_left acc_transl_instr c (OK []);
  OK (code).

End FUNCTION_SG.

Definition transf_function (f: function) : res function :=
  (* make sure that code can not have relative jumps*)
  if func_no_jmp_rel_dec f then
    do tt <-  set_current_function f;
    do fn_code' <- transl_code f (fn_code f);
    OK {|
        fn_sig := fn_sig f;
        fn_code := fn_code';
        fn_stacksize := fn_stacksize f;
        fn_ofs_link := fn_ofs_link f (* SANCC *)
      |}
  else
    Error [MSG "Code contains relative jumps"].

Definition transf_fundef (f: Asm.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Asm.program) : res Asm.program :=
  transform_partial_program transf_fundef p.
