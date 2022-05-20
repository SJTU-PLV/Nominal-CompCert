(* *******************  *)
(* Author: Jinhua Wu    *)
(* Date:   Feb 1, 2022 *)
(* Last updated: Jun 19, 2022 by Jinhua Wu *)
(* *******************  *)

(** * Merge sections with same type *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProgram.
Require Import SymbolString.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** Section Merging Pass is ELF dependent, for a general section merging, refer to x86/SectionLinking.v *)

(** merge sections *)

Definition merge_sections (sec1 sec2: section) : res section :=
  match sec1, sec2 with
  (* It should only contain bytes *)
  | sec_text c1, sec_text c2 =>
    OK (sec_text (c1 ++ c2))
  | sec_data d1, sec_data d2 =>
    OK (sec_data (d1 ++ d2))
  | sec_bytes b1, sec_bytes b2 =>
    OK (sec_bytes (b1 ++ b2))
  | _, _ => Error (msg "merge sections of different type")
  end.


Definition transf_relocentry (ofs:Z) (e:relocentry) :=
  Build_relocentry (e.(reloc_offset) + ofs) e.(reloc_type) e.(reloc_symb) e.(reloc_addend).  

Definition merge_reloctables (ofs: Z) (rel1 rel2: reloctable) : reloctable :=
  let rel2' := map (transf_relocentry ofs) rel2 in
  rel1++rel2'.

Definition transf_symbentry (id: ident) (ofs: Z) (e: symbentry) :=
  Build_symbentry e.(symbentry_bind) e.(symbentry_type) (e.(symbentry_value) + ofs) (secindex_normal id) e.(symbentry_size).

(* update symbtable, reconstruct section table and reloc table map *)

Section WITH_SEC_REL_TBL.
  Context (sectbl: sectable) (reltbl:reloctable_map) (sec_id: ident) (symbtype: symbtype).

(* id1 is the special section ident*)
Definition acc_sec (acc: res (section*symbtable*reloctable*Z)) (id2: ident) :=
  do acc' <- acc;
  let '(sec1,symbtbl,reloctbl1,ofs) := acc' in
  match sectbl!id2,symbtbl!id2 with
  | Some sec2, Some e2 =>
    do sec <- merge_sections sec1 sec2;
    let e2' := transf_symbentry sec_id ofs e2 in
    let symbtbl' := PTree.set id2 e2' symbtbl in
    match reltbl!id2 with
    | Some reloctbl2 =>
      let reloctbl := merge_reloctables ofs reloctbl1 reloctbl2 in
      OK (sec,symbtbl',reloctbl,ofs + e2.(symbentry_size))
    | _ =>
      OK (sec,symbtbl',reloctbl1,ofs + e2.(symbentry_size))
    end
  | _,_ => Error (msg "acc_sec in section merging: no id2 in sectbl or symbtbl")
  end.


Definition generate_section (idlist: list ident) (symbtbl: symbtable) : res (section* symbtable * reloctable) :=
    do r <- fold_left acc_sec idlist (OK (sec_bytes [], symbtbl, [], 0));
    let '(sec,symbtbl,reloctbl,ofs) := r in
    let e :=
        {| symbentry_bind := bind_global;
           symbentry_type := symbtype;
           symbentry_value := 0;
           symbentry_secindex := secindex_normal sec_id;
           symbentry_size := ofs |} in
    let symbtbl' := PTree.set sec_id e symbtbl in
    OK (sec,symbtbl',reloctbl).

(* Definition merge_data_sec (idlist: list ident) (symbtbl: symbtable) : res (section* symbtable * reloctable) := *)
(*     do r <- fold_left acc_sec idlist (OK (sec_bytes [], symbtbl, [], 0)); *)
(*     let '(sec,symbtbl,reloctbl,ofs) := r in *)
(*     let e := *)
(*         {| symbentry_bind := bind_global; *)
(*            symbentry_type := symb_rwdata; *)
(*            symbentry_value := 0; *)
(*            symbentry_secindex := secindex_normal sec_id; *)
(*            symbentry_size := ofs |} in *)
(*     let symbtbl' := PTree.set sec_id e symbtbl in *)
(*     OK (sec,symbtbl',reloctbl). *)

(* Definition merge_rodata_sec (idlist: list ident) (symbtbl: symbtable) : res (section* symbtable * reloctable) := *)
(*     do r <- fold_left acc_sec idlist (OK (sec_bytes [], symbtbl, [], 0)); *)
(*     let '(sec,symbtbl,reloctbl,ofs) := r in *)
(*     let e := *)
(*         {| symbentry_bind := bind_global; *)
(*            symbentry_type := symb_rodata; *)
(*            symbentry_value := 0; *)
(*            symbentry_secindex := secindex_normal sec_id; *)
(*            symbentry_size := ofs |} in *)
(*     let symbtbl' := PTree.set sec_id e symbtbl in *)
(*     OK (sec,symbtbl',reloctbl). *)

End WITH_SEC_REL_TBL.

(* All the sections are bytes !!! *)
(* Definition filter_text_id (sectbl: sectable) (id:ident) := *)
(*   match sectbl ! id with *)
(*   | Some sec => *)
(*     match sec with *)
(*     (* all are bytes!!! *) *)
(*     | sec_text _ => true *)
(*     | _ => false *)
(*     end *)
(*   | None => false *)
(*   end. *)

Definition filter_text_id (sectbl: sectable) (symbtbl: symbtable) (id:ident) :=
  match sectbl ! id, symbtbl ! id with
  | Some sec, Some e =>
    match e.(symbentry_type) with
    | symb_func => true 
    | _ => false
    end
  | _, _  => false
  end.

Definition filter_data_id (sectbl: sectable) (symbtbl: symbtable) (id:ident) :=
  match sectbl ! id, symbtbl ! id with
  | Some sec, Some e =>
    match e.(symbentry_type) with
    | symb_rwdata => true 
    | _ => false
    end
  | _, _  => false
  end.

Definition filter_rodata_id (sectbl: sectable) (symbtbl: symbtable) (id:ident) :=
  match sectbl ! id, symbtbl ! id with
  | Some sec, Some e =>
    match e.(symbentry_type) with
    | symb_rodata => true 
    | _ => false
    end
  | _, _  => false
  end.

Definition reloctbl_create (relmap: reloctable_map) (id: ident) (reloctbl: reloctable) :=
  match reloctbl with
  | [] => relmap
  | _ => PTree.set id reloctbl relmap
  end.



Definition transf_program (p: program) : res program :=
  let sectbl := p.(prog_sectable) in
  let symbtbl := p.(prog_symbtable) in
  let reltbl := p.(prog_reloctables) in
  let idlist := map fst (PTree.elements sectbl) in
  let idlist_text := filter (filter_text_id sectbl symbtbl) idlist in
  let idlist_data := filter (filter_data_id sectbl symbtbl) idlist in
  let idlist_rodata := filter (filter_rodata_id sectbl symbtbl) idlist in
  (* create ident *)
  let text_id := create_text_section_ident tt in
  let data_id := create_data_section_ident tt in
  let rodata_id := create_rodata_section_ident tt in
  (* relocation id must identical to section id *)
  (* let text_rel_id := create_text_rel_ident tt in *)
  (* let data_rel_id := create_data_rel_ident tt in *)
  (* let rodata_rel_id := create_rodata_rel_ident tt in *)
  (* transform *)
  do r1 <- generate_section sectbl reltbl text_id symb_func idlist_text symbtbl;
  let '(text_sec, symbtbl1, text_reloctbl) := r1 in
  do r2 <- generate_section sectbl reltbl data_id symb_rwdata idlist_data symbtbl1;
  let '(data_sec, symbtbl2, data_reloctbl) := r2 in
  do r3 <- generate_section sectbl reltbl rodata_id symb_rodata idlist_rodata symbtbl2;
  let '(rodata_sec, symbtbl3, rodata_reloctbl) := r3 in
  let sectbl1 := PTree.set text_id text_sec (PTree.empty section) in
  let sectbl2 := PTree.set data_id data_sec sectbl1 in
  let sectbl3 := PTree.set rodata_id rodata_sec sectbl2 in
  (* relocation table map *)
  let relmap1 := reloctbl_create (PTree.empty reloctable) text_id text_reloctbl in
  let relmap2 := reloctbl_create relmap1 data_id data_reloctbl in
  let relmap3 := reloctbl_create relmap2 rodata_id rodata_reloctbl in
  OK {| prog_defs := p.(prog_defs);
        prog_public := p.(prog_public);
        prog_main := p.(prog_main);
        prog_senv := p.(prog_senv);

        prog_sectable := sectbl3;
        prog_reloctables := relmap3;
        prog_symbtable := symbtbl3 |}.
