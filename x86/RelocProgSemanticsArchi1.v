Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgram Globalenvs.
Require Import Locations Stacklayout Conventions.
Require Import Linking Errors.
Require Import RelocProgSemantics Reloctablesgen.
Require Import LocalLib.
Import ListNotations.


Definition rev_id_eliminate (symb: ident) (_ : Z) (i:instruction) :=
   match i with
  | Pjmp_l_rel _ =>
     (Pjmp_s symb signature_main)
  | Pjmp_m (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pjmp_m (Addrmode rb ss (inr (symb,ptrofs))))
  | Pcall_s id sg =>
     (Pcall_s symb sg)
  | Pmov_rs rd id =>
     (Pmov_rs rd symb)
  | Pmovl_rm rd (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pmovl_rm rd (Addrmode rb ss (inr (symb,ptrofs))))
  | Pmovl_mr (Addrmode rb ss (inl disp)) rs =>
    let ptrofs := Ptrofs.repr disp in
     (Pmovl_mr (Addrmode rb ss (inr (symb, ptrofs))) rs)
  | Pfldl_m (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pfldl_m (Addrmode rb ss (inr (symb, ptrofs))))
  | Pfstpl_m (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pfstpl_m (Addrmode rb ss (inr (symb, ptrofs))))
  | Pflds_m (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pflds_m (Addrmode rb ss (inr (symb, ptrofs))))
  | Pfstps_m (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pfstps_m (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovsd_fm rd (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pmovsd_fm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovsd_mf (Addrmode rb ss (inl disp)) rs =>
    let ptrofs := Ptrofs.repr disp in
    (Pmovsd_mf (Addrmode rb ss (inr (symb, ptrofs))) rs)
  | Pmovsd_fm_a rd (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
    (Pmovsd_fm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovsd_mf_a (Addrmode rb ss (inl disp)) rs =>
    let ptrofs := Ptrofs.repr disp in
     (Pmovsd_mf (Addrmode rb ss (inr (symb, ptrofs))) rs)  
  | Pmovss_fm rd (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pmovss_fm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovss_mf (Addrmode rb ss (inl disp)) rs =>
    let ptrofs := Ptrofs.repr disp in
     (Pmovss_mf (Addrmode rb ss (inr (symb, ptrofs))) rs)
  | Pxorpd_fm rd (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pxorpd_fm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pxorps_fm rd (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pxorps_fm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pandpd_fm rd (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pandpd_fm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pandps_fm rd (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pandps_fm rd (Addrmode rb ss (inr (symb, ptrofs))))
  (** Moves with conversion *)
  | Pmovb_mr (Addrmode rb ss (inl disp)) rs =>
    let ptrofs := Ptrofs.repr disp in
     (Pmovb_mr (Addrmode rb ss (inr (symb, ptrofs))) rs)
  | Pmovb_rm rd (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pmovb_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovw_mr (Addrmode rb ss (inl disp)) rs =>
    let ptrofs := Ptrofs.repr disp in
     (Pmovw_mr (Addrmode rb ss (inr (symb, ptrofs))) rs)
  | Pmovw_rm rd (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pmovw_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovzb_rm rd (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pmovzb_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovsb_rm rd (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pmovsb_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovzw_rm rd (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pmovzw_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovsw_rm rd (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pmovsw_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovsq_rm rd (Addrmode rb ss (inl disp)) =>
    let ptrofs := Ptrofs.repr disp in
     (Pmovsq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovsq_mr (Addrmode rb ss (inl disp)) rs =>
    let ptrofs := Ptrofs.repr disp in
     (Pmovsq_mr (Addrmode rb ss (inr (symb, ptrofs))) rs)
  (** Integer arithmetic *)
  | Pleal rd (Addrmode rb ss (inl disp))  =>
    let ptrofs := Ptrofs.repr disp in
     (Pleal rd (Addrmode rb ss (inr (symb, ptrofs))))
  (** Saving and restoring registers *)
  | Pmov_rm_a rd (Addrmode rb ss (inl disp)) =>  (**r like [Pmov_rm], using [Many64] chunk *)
    let ptrofs := Ptrofs.repr disp in
     (Pmov_rm_a rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmov_mr_a (Addrmode rb ss (inl disp)) rs =>   (**r like [Pmov_mr], using [Many64] chunk *)
    let ptrofs := Ptrofs.repr disp in
    (Pmov_mr_a (Addrmode rb ss (inr (symb, ptrofs))) rs)
  | Paddq_rm rd (Addrmode rb ss (inl disp))  =>
    let ptrofs := Ptrofs.repr disp in
    (Paddq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Psubq_rm rd (Addrmode rb ss (inl disp))  =>
    let ptrofs := Ptrofs.repr disp in
    (Psubq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pimulq_rm rd (Addrmode rb ss (inl disp))  =>
    let ptrofs := Ptrofs.repr disp in
    (Pimulq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pandq_rm rd (Addrmode rb ss (inl disp))  =>
    let ptrofs := Ptrofs.repr disp in
    (Pandq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Porq_rm rd (Addrmode rb ss (inl disp))  =>
    let ptrofs := Ptrofs.repr disp in
    (Porq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pxorq_rm rd (Addrmode rb ss (inl disp))  =>
    let ptrofs := Ptrofs.repr disp in
    (Pxorq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pcmpq_rm rd (Addrmode rb ss (inl disp))  =>
    let ptrofs := Ptrofs.repr disp in
    (Pcmpq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Ptestq_rm rd (Addrmode rb ss (inl disp))  =>
    let ptrofs := Ptrofs.repr disp in
    (Ptestq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovq_rm rd (Addrmode rb ss (inl disp))  =>
    let ptrofs := Ptrofs.repr disp in
    (Pmovq_rm rd (Addrmode rb ss (inr (symb, ptrofs))))
  | Pmovq_mr (Addrmode rb ss (inl disp)) rs =>
    let ptrofs := Ptrofs.repr disp in
    (Pmovq_mr (Addrmode rb ss (inr (symb, ptrofs))) rs)
  | Pleaq rd (Addrmode rb ss (inl disp))  =>
    let ptrofs := Ptrofs.repr disp in
     (Pleaq rd (Addrmode rb ss (inr (symb, ptrofs))))
  | _ =>
     i
    end.
