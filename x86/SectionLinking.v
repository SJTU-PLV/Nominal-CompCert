(** * Linking sections of same type *)

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

(** merge sections *)

Definition link_section (sec1 sec2: section) : res (ident * section) :=
  match sec1, sec2 with
  | sec_text c1, sec_text c2 =>
    let id := create_section_ident tt in
    OK (id, sec_text (c1 ++ c2))
  | sec_data d1, sec_data d2 =>
    let id := create_section_ident tt in
    OK (id, sec_data (d1 ++ d2))
  | sec_rodata d1, sec_rodata d2 =>
    let id := create_section_ident tt in
    OK (id, sec_rodata (d1 ++ d2))
  | sec_bytes b1, sec_bytes b2 =>
    let id := create_section_ident tt in
    OK (id, sec_bytes (b1 ++ b2))
  | _, _ => Error (msg "link sections of different type")
  end.

Definition transf_sectable (id1 id2: ident) (sec1 sec2: section) (sectbl: sectable) : res (ident * sectable) :=
  do idsec <- link_section sec1 sec2;
  let (id, sec) := idsec in
  let tbl1 := PTree.remove id1 sectbl in
  let tbl2 := PTree.remove id2 tbl1 in
  OK (id, PTree.set id sec tbl2).


Definition transf_relocentry (ofs:Z) (e:relocentry) :=
  Build_relocentry (e.(reloc_offset) + ofs) e.(reloc_type) e.(reloc_symb) e.(reloc_addend).  

Definition link_reloctable (ofs: Z) (rel1 rel2: reloctable) : reloctable :=
  let rel2' := map (transf_relocentry ofs) rel2 in
  rel1++rel2'.

(** Optimized linking: clear redundant symbol entries, and redirect the relocation entry in all relocation table*)
Definition redundant_opt := true.

Section WITH_SYMB_OFS.
  Variable symb new_symb: ident.
  Variable ofs : Z.

Definition redirect_relocentry (e: relocentry) :=
  if ident_eq e.(reloc_symb) symb then
  {| reloc_offset := e.(reloc_offset);
     reloc_type := e.(reloc_type);
     reloc_symb := new_symb;
     reloc_addend := e.(reloc_addend) + ofs |}
  else e.

Definition redirect_reloctable (tbl: reloctable) :=
  map redirect_relocentry tbl.

Definition redirect_reloc_map (m: reloctable_map) :=
  PTree.map1  redirect_reloctable m.

End WITH_SYMB_OFS.


Section WITH_NEW_SYMB.
  Variable e1 e2 : symbentry.
  Variable new_symb: ident.

Definition transf_relocmap (id1 id2 : ident) (reloc_map : reloctable_map) : reloctable_map :=
  match  reloc_map ! id1, reloc_map ! id2 with
  | Some tbl1, Some tbl2 =>
    let ofs := e1.(symbentry_size) in
    let tbl := link_reloctable ofs tbl1 tbl2 in
    PTree.set new_symb tbl reloc_map
  | None, Some tbl2 =>
    let ofs := e1.(symbentry_size) in
    let tbl := link_reloctable ofs [] tbl2 in
    PTree.set new_symb tbl reloc_map
  | _, _ => reloc_map
  end.

(** Transform symbol table, add the new one and updated the two original entries *)
Definition transf_symbtbl (id1 id2 :ident) (symbtbl: symbtable) : symbtable :=
    let e2' := Build_symbentry e2.(symbentry_bind) e2.(symbentry_type) e1.(symbentry_size) (secindex_normal new_symb) e2.(symbentry_size) in
    let e1' := Build_symbentry e1.(symbentry_bind) e1.(symbentry_type) e1.(symbentry_value) (secindex_normal new_symb) e1.(symbentry_size) in
    let e := Build_symbentry e1.(symbentry_bind) e1.(symbentry_type) 0 (secindex_normal new_symb) (e1.(symbentry_size) + e2.(symbentry_size)) in
    let tbl1 := PTree.set id1 e1' symbtbl in
    let tbl2 := PTree.set id2 e2' tbl1 in
    PTree.set new_symb e tbl2.

(** remove the redundant symbol entry *)
Definition transf_symbtbl' (id1 id2 :ident) (symbtbl: symbtable) : symbtable :=
    let e := Build_symbentry e1.(symbentry_bind) e1.(symbentry_type) 0 (secindex_normal new_symb) (e1.(symbentry_size) + e2.(symbentry_size)) in
    let tbl1 := PTree.remove id1 symbtbl in
    let tbl2 := PTree.remove id2 tbl1 in
    PTree.set new_symb e tbl2.

End WITH_NEW_SYMB.

Definition get_section (id:ident) (sectbl:sectable) :res section :=
  match sectbl ! id with
  | Some sec => OK sec
  | None => Error (msg "Section not exists")
  end.

Definition get_symbentry (id:ident) (symtbl: symbtable) : res symbentry :=
  match symtbl ! id with
  | Some e => OK e
  | None => Error (msg "Symbolentry not exists")
  end.

(** Transform program1: input two id and merge their section, symbol entry and reloc table *)
(** return generated new symbol and transformed program *)
Definition transf_program1 (id1 id2: ident) (p: program) : res (ident * program) :=
  if ident_eq id1 id2 then
    Error (msg "link two section with same identity")
  else
    let sec_tbl := p.(prog_sectable) in
    do sec1 <- get_section id1 sec_tbl;
    do sec2 <- get_section id2 sec_tbl;
    do id_sectbl' <- transf_sectable id1 id2 sec1 sec2 sec_tbl;
    let (id, sec_tbl') := id_sectbl' in
    do syme1 <- get_symbentry id1 p.(prog_symbtable);
    do syme2 <- get_symbentry id2 p.(prog_symbtable);
    let reloc_map := transf_relocmap syme1 id id1 id2 p.(prog_reloctables) in
    if redundant_opt then       (* redundant elimination *)
      let symbtbl := transf_symbtbl' syme1 syme2 id id1 id2 p.(prog_symbtable) in
      let reloc_map1 := redirect_reloc_map id2 id syme1.(symbentry_size) (redirect_reloc_map id1 id 0 reloc_map) in
      OK (id,
        {| prog_public := p.(prog_public);
           prog_main := p.(prog_main);
           prog_sectable := sec_tbl';
           prog_symbtable := symbtbl;
           prog_reloctables := reloc_map1;
           prog_senv := p.(prog_senv);
        |})
    else
      let symbtbl := transf_symbtbl syme1 syme2 id id1 id2 p.(prog_symbtable) in
    OK (id,
        {| prog_public := p.(prog_public);
           prog_main := p.(prog_main);
           prog_sectable := sec_tbl';
           prog_symbtable := symbtbl;
           prog_reloctables := reloc_map;
           prog_senv := p.(prog_senv);
        |}).


(** merge section into one section in program p *)
(** id list is the list of id of the same type section*)
Fixpoint merge_sec' (id: ident) (idlist : list ident) (p: program) : res program :=
  match idlist with
  | [] => OK p
  | i :: l' =>
    do sec1 <- get_section id p.(prog_sectable);
    do sec2 <- get_section i p.(prog_sectable);
    do id_prog <- transf_program1 id i p;
    let (id', p') := id_prog in
    merge_sec' id' l' p'
  end.

Definition merge_sec (idlist: list ident) (p: program) :=
  match idlist with
  | [] => OK p
  | id :: l => merge_sec' id l p
  end.

Definition filter_text_id (sectbl: sectable) (id:ident) :=
  match sectbl ! id with
  | Some sec =>
    match sec with
    | sec_text _ => true
    | _ => false
    end
  | None => false
  end.

Definition filter_data_id (sectbl: sectable) (id:ident) :=
  match sectbl ! id with
  | Some sec =>
    match sec with
    | sec_data _ => true
    | _ => false
    end
  | None => false
  end.

Definition filter_rodata_id (sectbl: sectable) (id:ident) :=
  match sectbl ! id with
  | Some sec =>
    match sec with
    | sec_rodata _ => true
    | _ => false
    end
  | None => false
  end.


Definition transf_program (p: program) : res program :=
  let sectbl := p.(prog_sectable) in
  let idlist := map fst (PTree.elements sectbl) in
  let idlist_text := filter (filter_text_id sectbl) idlist in
  let idlist_data := filter (filter_data_id sectbl) idlist in
  let idlist_rodata := filter (filter_rodata_id sectbl) idlist in
  do p1 <- merge_sec idlist_text p;
  do p2 <- merge_sec idlist_data p1;
  merge_sec idlist_text p2.
  
