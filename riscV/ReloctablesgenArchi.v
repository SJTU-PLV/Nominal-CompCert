Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProg RelocProgram.
Require Import RelocationTypes.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.

(** ** Generation of relocation entries *)

Definition transl_instr (instr_size: instruction -> Z) (sofs:Z) (i: instruction) : res (option relocentry) :=
  match i with
  (* instructions with raw symbol *)
  | Plui_s _ symb ofs =>
      OK (Some {|reloc_offset := sofs; 
                 reloc_type := R_RISCV_HI20;
                 reloc_symb := symb;
                 reloc_addend := ofs |})
  | Paddi_s _ _ symb ofs =>
      OK (Some {|reloc_offset := sofs; 
                 reloc_type := R_RISCV_LO12_I;
                 reloc_symb := symb;
                 reloc_addend := ofs |})
  | Pjal_ofs _ (inl symb) =>
      OK (Some {|reloc_offset := sofs; 
                 reloc_type := R_RISCV_JAL;
                 reloc_symb := symb;
                 reloc_addend := 0 |})
         
  (* load instructions: I type *)
  | Plb  _ _ (Ofslow symb ofs)
  | Plbu _ _ (Ofslow symb ofs)
  | Plh  _ _ (Ofslow symb ofs)
  | Plhu _ _ (Ofslow symb ofs)
  | Plw  _ _ (Ofslow symb ofs)
  | Pld  _ _ (Ofslow symb ofs)
  | Pfls _ _ (Ofslow symb ofs)
  | Pfld _ _ (Ofslow symb ofs) =>
      OK (Some {|reloc_offset := sofs; 
                 reloc_type := R_RISCV_LO12_I;
                 reloc_symb := symb;
                 reloc_addend := (Ptrofs.signed ofs) |})
               
  (* store instructions: S type *)
  | Psb  _ _ (Ofslow symb ofs)
  | Psh  _ _ (Ofslow symb ofs)
  | Psw  _ _ (Ofslow symb ofs)
  | Psd  _ _ (Ofslow symb ofs)
  | Pfss _ _ (Ofslow symb ofs)
  | Pfsd _ _ (Ofslow symb ofs) =>
      OK (Some {|reloc_offset := sofs; 
                 reloc_type := R_RISCV_LO12_S;
                 reloc_symb := symb;
                 reloc_addend := (Ptrofs.signed ofs)|})
  | _ => OK None
  end.
      
Definition id_eliminate (i:instruction) : instruction :=
  match i with
  | Plui_s rd symb ofs =>
      Plui_s rd xH 0
  | Paddi_s rd rs symb ofs =>
      Paddi_s rd rs xH 0
  | Pjal_ofs rd (inl symb) =>
      Pjal_ofs rd (inr 0)
  | Plb  r1 r2 (Ofslow symb ofs) =>
      Plb  r1 r2 (Ofsimm (Ptrofs.zero))
  | Plbu r1 r2 (Ofslow symb ofs) =>
      Plbu  r1 r2 (Ofsimm (Ptrofs.zero))
  | Plh  r1 r2 (Ofslow symb ofs) =>
      Plh  r1 r2 (Ofsimm (Ptrofs.zero))
  | Plhu r1 r2 (Ofslow symb ofs) =>
      Plhu  r1 r2 (Ofsimm (Ptrofs.zero))
  | Plw  r1 r2 (Ofslow symb ofs) =>
      Plw  r1 r2 (Ofsimm (Ptrofs.zero))
  | Pld  r1 r2 (Ofslow symb ofs) =>
      Pld  r1 r2 (Ofsimm (Ptrofs.zero))
  | Pfls r1 r2 (Ofslow symb ofs) =>
      Pfls  r1 r2 (Ofsimm (Ptrofs.zero))
  | Pfld r1 r2 (Ofslow symb ofs) =>
      Pfld  r1 r2 (Ofsimm (Ptrofs.zero))
  | Psb  r1 r2 (Ofslow symb ofs) =>
      Psb  r1 r2 (Ofsimm (Ptrofs.zero))
  | Psh  r1 r2 (Ofslow symb ofs) =>
      Psh  r1 r2 (Ofsimm (Ptrofs.zero))
  | Psw  r1 r2 (Ofslow symb ofs) =>
      Psw  r1 r2 (Ofsimm (Ptrofs.zero))
  | Psd  r1 r2 (Ofslow symb ofs) =>
      Psd  r1 r2 (Ofsimm (Ptrofs.zero))
  | Pfss r1 r2 (Ofslow symb ofs) =>
      Pfss  r1 r2 (Ofsimm (Ptrofs.zero))
  | Pfsd r1 r2 (Ofslow symb ofs) =>
      Pfsd  r1 r2 (Ofsimm (Ptrofs.zero))
  | _ => i
  end.

(* data relocation *)
Definition transl_init_data (dofs:Z) (d:init_data) : res (option relocentry) :=
  match d with
  | Init_addrof id ofs =>
      let e := {| reloc_offset := dofs;
                  reloc_type := if Archi.ptr64 then R_RISCV_64 else R_RISCV_32;
                  reloc_symb := id;
                  reloc_addend := 0;
               |} in
      OK (Some e)
  | _ =>
    OK None
  end.
