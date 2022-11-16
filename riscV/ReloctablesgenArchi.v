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

Definition transl_instr (sofs:Z) (i: instruction) : res (option relocentry) :=
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
      
