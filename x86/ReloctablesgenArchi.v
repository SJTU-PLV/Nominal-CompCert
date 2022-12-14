Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProg RelocProgram.
Require Import RelocationTypes.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.

(** ** Translation of instructions *)

Definition addrmode_reloc_offset (a:addrmode) : Z :=
  addrmode_size_aux a.

(** Calculate the starting offset of the bytes
    that need to be relocated in an instruction *)
(** To support 64bit, consisder the rex prefix  *)
Definition instr_reloc_offset (i:instruction) : res Z :=
  match i with
  | Pmov_rs r _ => OK (rex_prefix_check_r r + 2)
  | Pcall_s _ _ => OK 1
  | Pjmp_s _ _ | Pjmp_l_rel _ => OK 1
  | Pleal r a
  | Pmovl_rm r a
  | Pmovl_mr a r =>
    let aofs := addrmode_reloc_offset a in
    let rex := rex_prefix_check_ra r a in
    OK (aofs + rex + 1)
  | Pmovb_mr a r
  | Pmovb_rm r a =>
    let aofs := addrmode_reloc_offset a in
    let rex := rex_prefix_check_ra r a in
    if Archi.ptr64 then
      OK (aofs + 2)
    else
      OK (aofs + rex + 1)
  (* | Pmov_rm_a _ a *)
  (* | Pmov_mr_a a _ *)
  | Pjmp_m a 
  | Pfldl_m a
  | Pfstpl_m a
  | Pflds_m a
  | Pfstps_m a =>
    let aofs := addrmode_reloc_offset a in
    let rex := rex_prefix_check_a a in
    OK (aofs + rex + 1)
  | Pmovw_mr a r
  | Pmovw_rm r a
  | Pmovzw_rm r a
  | Pmovsw_rm r a =>
    let aofs := addrmode_reloc_offset a in
    let rex := rex_prefix_check_ra r a in
    OK (aofs + rex + 2)
  | Pmovzb_rm r a
  | Pmovsb_rm r a =>
    let aofs := addrmode_reloc_offset a in
    let rex := rex_prefix_check_ra r a in
    (* 1byte memory to 32bit register *)
    (* if Archi.ptr64 then
      OK (aofs + 3)
    else *)
      OK (aofs + rex + 2)
  | Pxorps_fm r a
  | Pandps_fm r a =>
    let aofs := addrmode_reloc_offset a in
    let rex := rex_prefix_check_fa r a in
    OK (aofs + rex + 2)
  | Pmovsd_fm f a
  | Pmovsd_mf a f
  | Pmovss_fm f a
  | Pmovss_mf a f
  | Pmovsq_rm f a
  | Pmovsq_mr a f
  | Pxorpd_fm f a
  | Pandpd_fm f a =>
    let aofs := addrmode_reloc_offset a in
    let rex := rex_prefix_check_fa f a in
    OK (aofs + rex + 3)
  (* 64bit *)
  | Paddq_rm  _ a 
  | Psubq_rm  _ a 
  | Pandq_rm  _ a 
  | Porq_rm   _ a 
  | Pxorq_rm  _ a 
  | Pcmpq_rm  _ a 
  | Ptestq_rm _ a
  | Pmovq_mr a _
  | Pmovq_rm _ a
  | Pleaq _ a =>
    let aofs := addrmode_reloc_offset a in
    OK (aofs + 2)
  | Pimulq_rm _ a =>
    let aofs := addrmode_reloc_offset a in
    OK (aofs + 3)
  | Pmov_rm_a r a
  | Pmov_mr_a a r =>
    let aofs := addrmode_reloc_offset a in
    if Archi.ptr64 then
      OK (aofs + 2)
    else
      let rex := rex_prefix_check_ra r a in
      OK (aofs + rex + 1)
  | _ => Error [MSG "Calculation of relocation offset failed: Either there is no possible relocation location or the instruction ";
              MSG (instr_to_string i); MSG " is not supported yet by relocation"]
  end.

Section INSTR_SIZE.
  Variable instr_size: instruction -> Z.
  
(** Calculate the addendum of an instruction *)
Definition instr_addendum  (i:instruction) : res Z :=
  do ofs <- instr_reloc_offset i;
  OK (ofs - (instr_size i)).


(** Compute the relocation entry of an instruction with a relative reference *)
Definition compute_instr_rel_relocentry (sofs:Z) (i:instruction) (symb:ident):=
  do iofs <- instr_reloc_offset i;
  do addend <- instr_addendum i;
  OK {| reloc_offset := sofs + iofs; 
          reloc_type := reloc_rel;
          reloc_symb := symb;
          reloc_addend := addend |}.

(** Compute the relocation entry of an instruction with an absolute reference *)
Definition compute_instr_abs_relocentry (sofs:Z) (i:instruction) (addend:Z) (symb:ident)  :=
  do iofs <- instr_reloc_offset i;
  OK {| reloc_offset := sofs + iofs; 
          reloc_type := reloc_abs;
          reloc_symb := symb;
          reloc_addend := addend |}.

(** Compute the relocation entry of an instruciton with 
    an addressing mode whose displacement is (id + offset) *)
Definition compute_instr_disp_relocentry (sofs: Z) (i:instruction) (disp: ident*ptrofs) :=
  let '(symb,addend) := disp in
  if Archi.ptr64 then
    (* rip relative addressing *)
    compute_instr_rel_relocentry sofs i symb
  else
    (* the addend field is useless in 32bit mode *)
    compute_instr_abs_relocentry sofs i 0 symb.

(* move unsupported here *)
Fixpoint ok_builtin_arg {A} (ba: builtin_arg A) : bool :=
  match ba with
  | BA_addrglobal _ _
  | BA_loadglobal _ _ _ => false
  | BA_splitlong ba1 ba2 => ok_builtin_arg ba1 && ok_builtin_arg ba2
  | _ => true
  end.

(* why unsupported ? *)
Definition unsupported i :=
  match i with
  (* | Pmovq_rm _ _ *)
  (* | Pmovq_mr _ _ *)
  | Pmovsd_fm_a _ _
  | Pmovsd_mf_a _ _
  (* | Pleaq _ _ *)
    => true
  | Pbuiltin _ args _ =>
    negb (forallb ok_builtin_arg args)
  | _ => false
  end.


Definition transl_instr (sofs:Z) (i: instruction) : res (option relocentry) :=
  if unsupported i
  then Error [MSG "unsupported instruction: "; MSG (instr_to_string i); MSG " in relocation table generation"]
  else 
  match i with
    Pallocframe _ _ _
  | Pfreeframe _ _ _
  (* | Pload_parent_pointer _ _ _ => Error (msg "Source program contains pseudo instructions") *)
  | Pjmp_l _
  | Pjcc _ _
  | Pjcc2 _ _ _
  | Pjmptbl _ _ => Error (msg "Source program contains jumps to labels")
  | Pjmp_s id sg => 
    if Archi.ptr64 then
      do e <- compute_instr_rel_relocentry sofs i id;
      OK (Some e)
    else
      OK (Some {| reloc_offset := sofs + 1;
            reloc_type := reloc_rel;
            reloc_symb := id;
            reloc_addend := 0 |})

  | Pjmp_m (Addrmode rb ss (inr disp)) =>
    match rb,ss with
    | None,None =>
      do e <- compute_instr_disp_relocentry sofs i disp;
      OK (Some e)
    | _,_ =>
     (* can not use rip-addressing *)
      let (symb,addend) := disp in
      do e <- compute_instr_abs_relocentry sofs i 0 symb;
      OK (Some e)
      end
  | Pcall_s id sg =>
    if Archi.ptr64 then
      do e <- compute_instr_rel_relocentry sofs i id;
      OK (Some e)
    else
     (* 32bit: addend must be 0, because it is useless *)
      OK (Some {| reloc_offset := sofs + 1;
            reloc_type := reloc_rel;
            reloc_symb := id;
            reloc_addend := 0 |})
  | Pmov_rs rd id => 
    do e <- compute_instr_abs_relocentry sofs i 0 id;
    OK (Some e)
  | Pmovl_rm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  (* | Pmovq_rm rd a => *)
  (*   Error [MSG "Relocation failed: "; MSG (instr_to_string i); MSG " not supported yet"]    *)
  | Pmovl_mr (Addrmode rb ss (inr disp)) rs =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  (* | Pmovq_mr a rs => *)
  (*   Error [MSG "Relocation failed: "; MSG (instr_to_string i); MSG " not supported yet"] *)
  | Pmovsd_fm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pmovsd_mf (Addrmode rb ss (inr disp)) r1 =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pmovss_fm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pmovss_mf (Addrmode rb ss (inr disp)) r1 =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pfldl_m (Addrmode rb ss (inr disp)) => (**r [fld] double precision *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pfstpl_m (Addrmode rb ss (inr disp)) => (**r [fstp] double precision *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pflds_m (Addrmode rb ss (inr disp)) => (**r [fld] simple precision *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pfstps_m (Addrmode rb ss (inr disp)) => (**r [fstp] simple precision *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pxorpd_fm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pxorps_fm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pandpd_fm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pandps_fm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
    (** Moves with conversion *)
  | Pmovb_mr (Addrmode rb ss (inr disp)) rs =>    (**r [mov] (8-bit int) *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pmovb_rm rd (Addrmode rb ss (inr disp)) =>    (**r [mov] (8-bit int) *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)       
  | Pmovw_mr (Addrmode rb ss (inr disp)) rs =>    (**r [mov] (16-bit int) *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pmovw_rm rd (Addrmode rb ss (inr disp)) =>    (**r [mov] (16-bit int) *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pmovzb_rm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pmovsb_rm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pmovzw_rm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pmovsw_rm rd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pmovsq_rm frd (Addrmode rb ss (inr disp)) =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pmovsq_mr (Addrmode rb ss (inr disp)) frs =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  (** Integer arithmetic *)
  | Pleal rd (Addrmode rb ss (inr disp))  =>
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  (* | Pleaq rd a => *)
  (*   Error (msg "Relocation failed: instruction not supported yet") *)
  (** saving and restoring registers *)
  | Pmov_rm_a rd (Addrmode rb ss (inr disp)) =>  (**r like [Pmov_rm], using [Many64] chunk *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  | Pmov_mr_a (Addrmode rb ss (inr disp)) rs =>   (**r like [Pmov_mr], using [Many64] chunk *)
    do e <- compute_instr_disp_relocentry sofs i disp;
    OK (Some e)
  (* | Pmovsd_fm_a rd a => (**r like [Pmovsd_fm], using [Many64] chunk *) *)
  (*   Error [MSG "Relocation failed:"; MSG (instr_to_string i); MSG "not supported yet"] *)
  (* | Pmovsd_mf_a a r1 =>  (**r like [Pmovsd_mf], using [Many64] chunk *) *)
  (*   Error [MSG "Relocation failed:"; MSG (instr_to_string i); MSG "not supported yet"] *)
  (* 64bit mode *)
  | Paddq_rm  _ (Addrmode rb ss (inr disp))
  | Psubq_rm  _ (Addrmode rb ss (inr disp))
  | Pimulq_rm _ (Addrmode rb ss (inr disp))
  | Pandq_rm  _ (Addrmode rb ss (inr disp))
  | Porq_rm   _ (Addrmode rb ss (inr disp))
  | Pxorq_rm  _ (Addrmode rb ss (inr disp))
  | Ptestq_rm  _ (Addrmode rb ss (inr disp))
  | Pcmpq_rm  _ (Addrmode rb ss (inr disp))
  | Pmovq_rm  _ (Addrmode rb ss (inr disp))
  | Pmovq_mr (Addrmode rb ss (inr disp)) _
  | Pleaq _ (Addrmode rb ss (inr disp)) =>
     do e <- compute_instr_disp_relocentry sofs i disp;
     OK (Some e)
  | _ =>
    OK None
  end.


End INSTR_SIZE.

(** Eliminate id that needs relocation *)
Definition id_eliminate (i:instruction): instruction:=  
    match i with
  | Pjmp_s id sg =>
     (Pjmp_l_rel 0)
  | Pjmp_m (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pjmp_m (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pcall_s id sg =>
     (Pcall_s xH sg)
  | Pmov_rs rd id =>
     (Pmov_rs rd xH)
  | Pmovl_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovl_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pmovl_mr (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
     (Pmovl_mr (Addrmode rb ss (inl (Ptrofs.signed ptrofs))) rs)
  | Pfldl_m (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pfldl_m (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pfstpl_m (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pfstpl_m (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pflds_m (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pflds_m (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pfstps_m (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pfstps_m (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pmovsd_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovsd_fm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pmovsd_mf (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
     (Pmovsd_mf (Addrmode rb ss (inl (Ptrofs.signed ptrofs))) rs)
  | Pmovss_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovss_fm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pmovss_mf (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
     (Pmovss_mf (Addrmode rb ss (inl (Ptrofs.signed ptrofs))) rs)
  | Pxorpd_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pxorpd_fm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pxorps_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pxorps_fm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pandpd_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pandpd_fm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pandps_fm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pandps_fm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  (** Moves with conversion *)
  | Pmovb_mr (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
     (Pmovb_mr (Addrmode rb ss (inl (Ptrofs.signed ptrofs))) rs)
  | Pmovb_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovb_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pmovw_mr (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
     (Pmovw_mr (Addrmode rb ss (inl (Ptrofs.signed ptrofs))) rs)
  | Pmovw_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovw_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pmovzb_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovzb_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pmovsb_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovsb_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pmovzw_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovzw_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pmovsw_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovsw_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pmovsq_rm rd (Addrmode rb ss (inr disp)) =>
    let '(id, ptrofs) := disp in
     (Pmovsq_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pmovsq_mr (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
     (Pmovsq_mr (Addrmode rb ss (inl (Ptrofs.signed ptrofs))) rs)
  (** Integer arithmetic *)
  | Pleal rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
     (Pleal rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  (** Saving and restoring registers *)
  | Pmov_rm_a rd (Addrmode rb ss (inr disp)) =>  (**r like [Pmov_rm], using [Many64] chunk *)
    let '(id, ptrofs) := disp in
     (Pmov_rm_a rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pmov_mr_a (Addrmode rb ss (inr disp)) rs =>   (**r like [Pmov_mr], using [Many64] chunk *)
    let '(id, ptrofs) := disp in
    (Pmov_mr_a (Addrmode rb ss (inl (Ptrofs.signed ptrofs))) rs)
  | Paddq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Paddq_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Psubq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Psubq_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pimulq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Pimulq_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pandq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Pandq_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Porq_rm rd (Addrmode rb ss (inr disp))  =>    
    let '(id, ptrofs) := disp in
    (Porq_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pxorq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Pxorq_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pcmpq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Pcmpq_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Ptestq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Ptestq_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pmovq_rm rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
    (Pmovq_rm rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | Pmovq_mr (Addrmode rb ss (inr disp)) rs =>
    let '(id, ptrofs) := disp in
    (Pmovq_mr (Addrmode rb ss (inl (Ptrofs.signed ptrofs))) rs)
  | Pleaq rd (Addrmode rb ss (inr disp))  =>
    let '(id, ptrofs) := disp in
     (Pleaq rd (Addrmode rb ss (inl (Ptrofs.signed ptrofs))))
  | _ =>
     i
    end.


Definition transl_init_data (dofs:Z) (d:init_data) : res (option relocentry) :=
  match d with
  | Init_addrof id ofs =>
      let e := {| reloc_offset := dofs;
                  reloc_type := reloc_abs;
                  reloc_symb := id;
                  reloc_addend := 0;
               |} in
      OK (Some e)
  | _ =>
    OK None
  end.
