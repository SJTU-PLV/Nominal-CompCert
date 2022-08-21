Require Import Coqlib Integers AST Maps.
Require Import Events Errors Smallstep Values.
Require Import Asm RelocProg RelocProgramBytes Encode.
Require Import Memdata.
Require Import RelocElf RelocElfgen.
Require Import SymbolString.
Require Import ReloctablesEncode.
Require Import encode.Hex encode.Bits.
Require Import SymbtableEncode SymbtableDecode.
Require Import ReloctablesDecode.
Require Import EncDecRet RelocProgSemantics2.

Import Hex Bits.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope string_byte_scope.

Fixpoint id_from_strtbl_aux (l: list byte) (str: list byte) :=
  match l with
  | b :: l' =>
    if Byte.eq b HB["00"] then
      match string_to_ident str with
      | Some id =>
        OK (id,  l')
      | _ => Error (msg "get id from strtbl error")
      end        
    else id_from_strtbl_aux l' (str++[b])
  | _ => Error (msg "get id from strtbl error")
  end.
  
Definition id_from_strtbl (l: list byte) :=
  id_from_strtbl_aux l [].


Definition get_ptr64 (ef: elf_file) : bool:=
  match ef.(elf_head).(e_class) with
  | ELFCLASS32 => false
  | ELFCLASS64 => true
  | _ => false                   (* default *)
  end.

Section WITH_FLAG.

Variable elf64: bool.


Record decode_elf_state :=
  { dec_sectable : sectable;
    dec_symbtable : symbtable;
    dec_reloctable: reloctable_map;
    dec_shstrtbl: list byte;
    dec_strtbl: list byte
  }.

Definition update_sectable_shstrtbl st id sec shstrtbl :=
  {| dec_sectable := PTree.set id sec st.(dec_sectable);
     dec_symbtable := st.(dec_symbtable);
     dec_reloctable := st.(dec_reloctable);
     dec_shstrtbl := shstrtbl;
     dec_strtbl := st.(dec_strtbl)
  |}.

Definition update_reloctable_shstrtbl st id reloctbl shstrtbl :=
  {| dec_sectable := st.(dec_sectable);
     dec_symbtable := st.(dec_symbtable);
     dec_reloctable := PTree.set id reloctbl st.(dec_reloctable);
     dec_shstrtbl := shstrtbl;
     dec_strtbl := st.(dec_strtbl)
  |}.

(* skip [".strtab"] *)
Definition update_strtbl st strtbl shstrtbl :=
  {| dec_sectable := st.(dec_sectable);
     dec_symbtable := st.(dec_symbtable);
     dec_reloctable := st.(dec_reloctable);
     dec_shstrtbl := shstrtbl;
     dec_strtbl := strtbl
  |}.

(* skip [".symtab"] *)
Definition update_symbtable st symbtbl shstrtbl :=
  {| dec_sectable := st.(dec_sectable);
     dec_symbtable := symbtbl;
     dec_reloctable := st.(dec_reloctable);
     dec_shstrtbl := shstrtbl;
     dec_strtbl := st.(dec_strtbl)
  |}.

Definition acc_index_to_ident (acc: ZTree.t ident * Z) (id: ident) :=
  let (t, idx) := acc in
  (ZTree.set idx id t, idx + 1).

Definition index_to_ident (idl: list ident) (start: Z) :=
  fst (fold_left acc_index_to_ident idl (ZTree.empty ident, start)).



Definition acc_decode_reloctable_section (reloclen: nat) (m: ZTree.t ident) (acc: res (reloctable * list byte * nat)) (b:byte) :=
  do acc' <- acc;
  let '(reloctbl, reloce, len) := acc' in
  if Nat.eq_dec len reloclen then
    do e <- decode_relocentry elf64 m (reloce ++ [b]);
    OK (reloctbl ++ [e], [], 1%nat)
  else
    OK (reloctbl, reloce ++ [b], S len).
  
Definition decode_reloctable_section (l: list byte) (m:ZTree.t ident) :=
  let reloclen := if elf64 then 24%nat else 8%nat in
  do r <- fold_left (acc_decode_reloctable_section reloclen m) l (OK ([], [], 1%nat));
  OK (fst (fst r)).


Definition acc_decode_symbtable_section (symblen: nat) (m: ZTree.t ident) (acc: res (symbtable * list byte * list byte * nat)) (b: byte) :=
  do acc' <- acc;
  let '(symbtbl, strtbl, symbe, len) :=  acc' in
  if Nat.eq_dec len symblen then
    do (id, strtbl') <- id_from_strtbl strtbl;
    if elf64 then
      do e <- decode_symbentry64 (symbe ++ [b]) m;
      OK (PTree.set id e symbtbl, strtbl', [], 1%nat)
    else
      do e <- decode_symbentry32 (symbe ++ [b]) m;
      OK (PTree.set id e symbtbl, strtbl', [], 1%nat)
  else
    OK (symbtbl, strtbl, symbe ++ [b], S len).

Definition decode_symbtable_section (l:list byte) (m:ZTree.t ident) (strtbl: list byte) (symbtbl: symbtable) :=
  let symblen := if elf64 then 24%nat else 16%nat in
  let l := skipn symblen l in   (* skip dummy entry *)
  do r <- fold_left (acc_decode_symbtable_section symblen m) l (OK (PTree.empty symbentry, strtbl, [], 1%nat));
  OK (fst (fst (fst r))).

  
Definition acc_section_header (st: res decode_elf_state) (sec_h: section * section_header) :=
  do st <- st;
  let (sec, h) := sec_h in
  match h.(sh_type) with

  (* code and data *)
  | SHT_PROGBITS =>
    (* get section id *)
    do (id, shstrtbl') <- id_from_strtbl st.(dec_shstrtbl);
    match h.(sh_flags) with
    | [SHF_ALLOC] =>
      OK (update_sectable_shstrtbl st id (sec_rodata sec) shstrtbl')
    | [SHF_ALLOC; SHF_WRITE] =>
      OK (update_sectable_shstrtbl st id (sec_rwdata sec) shstrtbl')
    | [SHF_ALLOC; SHF_EXECINSTR] =>
      OK (update_sectable_shstrtbl st id (sec_text sec) shstrtbl')
    | _ => Error (msg "sh_flag error")
    end
       
  (* restore the strtbl in state*)
  (* shstrtbl impossible, since we removelast the shstrtbl header *)
  | SHT_STRTAB =>
    do (_, shstrtbl') <- take_drop (length strtab_str) st.(dec_shstrtbl);
    OK (update_strtbl st sec shstrtbl')
                  
  (* symbtable *)
  | SHT_SYMTAB =>
    (* get id to index map from sectable: Z -> ident *)
    let idl_sectbl := PTree.elements st.(dec_sectable) in
    let secidl := map fst idl_sectbl in
    let secidxmap := index_to_ident secidl 1 in
    (* iterate symbtable section and strtable simutaneously *)
    do symbtbl <- decode_symbtable_section sec secidxmap st.(dec_strtbl) (PTree.empty symbentry);
    do (_, shstrtbl') <- take_drop (length symtab_str) st.(dec_shstrtbl);
    OK (update_symbtable st symbtbl shstrtbl')
       
  | SHT_REL | SHT_RELA =>
    (* get id to index map from sorted symbol table: Z -> ident *)
    let idl_symbtbl := PTree.elements st.(dec_symbtable) in
    let symbidl := map fst (sort_symbtable idl_symbtbl) in
    let symbidxmap := index_to_ident symbidl 1 in
    do (_, shstrtbl0) <- take_drop (length SB[".rel"]) st.(dec_shstrtbl);
    do (id, shstrtbl') <- id_from_strtbl shstrtbl0;
    do reloctbl <- decode_reloctable_section sec symbidxmap;
    OK (update_reloctable_shstrtbl st id reloctbl shstrtbl')
           
  | _ => Error (msg "unsupported section header")
  end.

End WITH_FLAG.

Definition init_dec_state shstrtbl :=
  {| dec_sectable := PTree.empty RelocProgramBytes.section;
     dec_symbtable := PTree.empty symbentry;
     dec_reloctable := PTree.empty reloctable;
     dec_shstrtbl := shstrtbl;
     dec_strtbl := [] |}.

Definition decode_elf (p: elf_file) : res program :=
  let init := init_dec_state (last p.(elf_sections) []) in
  let elf64 := get_ptr64 p in
  let secs := removelast p.(elf_sections) in
  let hs := tail (removelast p.(elf_section_headers)) in
  do st <- fold_left (acc_section_header elf64) (combine secs hs) (OK init);
  OK (Build_program _ _ _ _ p.(prog_defs) p.(prog_public) p.(prog_main) st.(dec_sectable) st.(dec_symbtable) st.(dec_reloctable) p.(prog_senv)).


Section WITH_INSTR_SIZE.

Variable instr_size : instruction -> Z.
Variable Instr_size : list Instruction -> Z.
  

(* global env *)

Definition empty_elf_file1 (p: elf_file) : program1 :=
  Build_program _ _ _ _ (prog_defs p) [] (prog_main p) (PTree.empty section1) (PTree.empty symbentry) (PTree.empty reloctable) (p.(prog_senv)).
    

Definition globalenv (p: elf_file) :=
  match decode_elf p with
  | OK p'=>                  
    RelocProgSemantics2.globalenv instr_size Instr_size p'
  | _ => RelocProgSemantics.globalenv instr_size (empty_elf_file1 p)
  end.

(* initial state *)

Inductive initial_state (prog: elf_file) (rs: regset) (s: state): Prop :=
| initial_state_intro: forall prog',
    decode_elf prog = OK prog' ->
    RelocProgSemantics2.initial_state instr_size Instr_size prog' rs s ->
    initial_state prog rs s.

(* Semantics *)
Definition semantics (p: elf_file) (rs: regset) :=
  Semantics_gen (RelocProgSemantics.step instr_size)
                (initial_state p rs) RelocProgSemantics.final_state 
                (globalenv p)
                (RelocProgSemantics.Genv.genv_senv (globalenv p)).

(** Determinacy of the semantics. *)

Lemma semantics_determinate: forall p rs, determinate (semantics p rs).
Proof.
  Ltac Equalities :=
    match goal with
    | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
    | _ => idtac
    end.
  intros.
  constructor;simpl;intros.
  -                             (* initial state *)
    inv H;inv H10;Equalities.
    + split. constructor. auto.
    + discriminate.
    + discriminate.
    + assert (vargs0 = vargs) by (eapply RelocProgSemantics.eval_builtin_args_determ; eauto).   
      subst vargs0.      
      exploit external_call_determ. eexact H15. eexact H21. intros [A B].
      split. auto. intros. destruct B; auto. subst. auto.
    + assert (args0 = args) by (eapply Asm.extcall_arguments_determ; eauto). subst args0.
      exploit external_call_determ. eexact H13. eexact H17. intros [A B].
      split. auto. intros. destruct B; auto. subst. auto.
  - red; intros; inv H; simpl.
    lia.
    eapply external_call_trace_length; eauto.
    eapply external_call_trace_length; eauto.
  - (* initial states *)
    inv H; inv H10. inv H13;inv H12. assert (m = m0) by congruence.
    assert (prog' = prog'0) by congruence.
    subst.
    assert (prog'1 = prog'2) by congruence.
    subst.
    inv H15; inv H17.
  assert (m1 = m3 /\ stk = stk0) by intuition congruence. destruct H12; subst.
  assert (m2 = m4) by congruence. subst.
  f_equal.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. red; intros; red; intros. inv H; rewrite H10 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H10. congruence.    
Qed.


Theorem reloc_prog_single_events p rs:
  single_events (semantics p rs).
Proof.
  red. intros.
  inv H; simpl. lia.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
Qed.

Theorem reloc_prog_receptive p rs:
  receptive (semantics p rs).
Proof.
  split.
  - simpl. intros s t1 s1 t2 STEP MT.
    inv STEP.
    inv MT. eexists.
    + eapply RelocProgSemantics.exec_step_internal; eauto.
    + 
      edestruct external_call_receptive as (vres2 & m2 & EC2); eauto.
      eexists. eapply RelocProgSemantics.exec_step_builtin; eauto.
    + edestruct external_call_receptive as (vres2 & m2 & EC2); eauto.
      eexists. eapply RelocProgSemantics.exec_step_external; eauto.
  - eapply reloc_prog_single_events; eauto.  
Qed.

End WITH_INSTR_SIZE.
