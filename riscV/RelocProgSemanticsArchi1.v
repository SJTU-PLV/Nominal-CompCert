Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgram Globalenvs.
Require Import Locations Stacklayout Conventions.
Require Import Linking Errors.
Require Import RelocProgSemantics Reloctablesgen.
Require Import LocalLib.
Import ListNotations.


Definition rev_id_eliminate (symb: ident) (ofs : Z) (i:instruction) :=
  match i with
  | Pluil rd _ => Plui_s rd symb ofs
  | Pluiw rd _ => Plui_s rd symb ofs
  | Paddil rd rs _ => Paddi_s rd rs symb ofs
  | Paddiw rd rs _ => Paddi_s rd rs symb ofs
  | Pauipc rd (inr _) => Pauipc rd (inl symb)
  | Pjal_ofs rd (inr _) => Pjal_ofs rd (inl symb)
  | Plb  r1 r2 (Ofsimm _) => Plb  r1 r2  (Ofslow symb (Ptrofs.repr ofs))
  | Plbu r1 r2 (Ofsimm _) => Plbu  r1 r2 (Ofslow symb (Ptrofs.repr ofs))
  | Plh  r1 r2 (Ofsimm _) => Plh  r1 r2  (Ofslow symb (Ptrofs.repr ofs))
  | Plhu r1 r2 (Ofsimm _) => Plhu  r1 r2 (Ofslow symb (Ptrofs.repr ofs))
  | Plw  r1 r2 (Ofsimm _) => Plw  r1 r2  (Ofslow symb (Ptrofs.repr ofs))
  | Pld  r1 r2 (Ofsimm _) => Pld  r1 r2  (Ofslow symb (Ptrofs.repr ofs))
  | Pfls r1 r2 (Ofsimm _) => Pfls  r1 r2 (Ofslow symb (Ptrofs.repr ofs))
  | Pfld r1 r2 (Ofsimm _) => Pfld  r1 r2 (Ofslow symb (Ptrofs.repr ofs))
  | Psb  r1 r2 (Ofsimm _) => Psb  r1 r2  (Ofslow symb (Ptrofs.repr ofs))
  | Psh  r1 r2 (Ofsimm _) => Psh  r1 r2  (Ofslow symb (Ptrofs.repr ofs))
  | Psw  r1 r2 (Ofsimm _) => Psw  r1 r2  (Ofslow symb (Ptrofs.repr ofs))
  | Psd  r1 r2 (Ofsimm _) => Psd  r1 r2  (Ofslow symb (Ptrofs.repr ofs))
  | Pfss r1 r2 (Ofsimm _) => Pfss  r1 r2 (Ofslow symb (Ptrofs.repr ofs))
  | Pfsd r1 r2 (Ofsimm _) => Pfsd  r1 r2 (Ofslow symb (Ptrofs.repr ofs))
  | _ => i
  end.
 
 
