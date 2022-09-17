(** * Generation of the relocation table and references to it *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProg RelocProgram ReloctablesgenArchi.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.


Section INSTR_SIZE.
  Variable instr_size: instruction -> Z.

Section WITH_SYMBTBL.

Variable (symbtbl: symbtable).

Let transl_instr:= transl_instr instr_size symbtbl.
      
Definition acc_instrs r i :=
  do (sofs, rtbl) <- r;
  do ri <- transl_instr sofs i;
  match ri with
  | Some r =>
    OK (sofs + instr_size i, rtbl ++ [r])
  | None =>
    OK (sofs + instr_size i, rtbl)
  end.

Definition transl_code (c:code) : res reloctable :=
  do (_, rtbl) <- fold_left acc_instrs c (OK (0, []));
  OK rtbl.

(** ** Translation of global variables *)

Definition transl_init_data (dofs:Z) (d:init_data) : res (option relocentry) :=
  match d with
  | Init_addrof id ofs =>
    match symbtbl!id with
    | None =>
      Error [MSG "Cannot find the index for symbol: "; POS id]
    | Some _ =>
      let e := {| reloc_offset := dofs;
                  reloc_type := reloc_abs;
                  reloc_symb := id;
                  reloc_addend := 0;
               |} in
      OK (Some e)
    end
  | _ =>
    OK None
  end.

(** Tranlsation of a list of initialization data and generate
    relocation entries *)

Definition acc_init_data r d :=
  do (dofs, rtbl) <- r;
  (* let '(dofs, rtbl) := r' in *)
  do ri <- transl_init_data dofs d;
  match ri with
  | Some r =>
    OK (dofs + init_data_size d, rtbl ++ [r])
  | None =>
    OK (dofs + init_data_size d, rtbl)
  end.

Definition transl_init_data_list (l:list init_data) : res reloctable :=
  do rs <-
      fold_left acc_init_data l (OK (0, []));
  let '(_, rtbl) := rs in
  OK rtbl.


(** ** Translation of the program *)
Definition transl_section (id:ident) (sec:section) :=
  match sec with
  | sec_text code =>
    do reltbl <- transl_code code;
    OK reltbl
  | sec_rwdata d =>
    do reltbl <- transl_init_data_list d;
    OK reltbl
  | sec_rodata d =>
    do reltbl <- transl_init_data_list d;
    OK reltbl
  end.

Definition acc_section (reloc_map : res reloctable_map) (id:ident) (sec:section) :=
  do relmap <- reloc_map;
  do reloctbl <- transl_section id sec;
  match reloctbl with
  (* empty checking *)
  | [] => OK relmap
  | _ =>
    OK (PTree.set id reloctbl relmap)
  end.

Definition transl_sectable (stbl: sectable) :=
  PTree.fold acc_section stbl (OK (PTree.empty reloctable)).

End WITH_SYMBTBL.


Definition acc_id_eliminate r i :=
  id_eliminate i :: r.

Definition transl_code' (c:code): code :=
  map id_eliminate c.
  (* rev (fold_left acc_id_eliminate c []). *)    

Definition transl_section' (id:ident) (sec: section) : section :=
  match sec with
  | sec_text code =>
    let c := (transl_code' code) in
    sec_text c
  | _ => sec
  end.


Local Open Scope string_scope.
Definition print_section (s: section) :=
  match s with
  | sec_text _ => "text"
  | sec_rwdata _ => "rwdata"
  | sec_rodata _ => "rodata"
  end.

Definition acc_print_section (acc: string) (sec : section) :=
  String.append acc (print_section sec).

Definition print_sectable (stbl: sectable) :=
  PTree.fold1 acc_print_section stbl "".

Definition transl_sectable' (stbl: sectable): sectable :=
  PTree.map transl_section' stbl.
  
  
Definition transf_program (p:RelocProgram.program) : res program :=
  let map := p.(prog_symbtable) in
  (* if  p.(prog_reloctables) (PTree.empty reloctable) then *)
    do reloc_map <- transl_sectable map (prog_sectable p);
    let sec' := transl_sectable' (prog_sectable p) in
    OK {| prog_defs := prog_defs p;
          prog_public := prog_public p;
          prog_main := prog_main p;
          prog_sectable := sec';
          prog_symbtable := prog_symbtable p;
          prog_reloctables := reloc_map;
          prog_senv := prog_senv p;
       |}
  (* else Error (msg "Relocation table map is not empty before relocation table generation.") *)
.

End INSTR_SIZE.
