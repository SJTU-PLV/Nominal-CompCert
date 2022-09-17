Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProg RelocProgram.
Require Import CheckDef.
Require Import LocalLib.
Require Import SymbtablegenArchi.
Require Globalenvs.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.

Section INSTR_SIZE.

Variable instr_size : instruction -> Z.
Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.


Definition def_size (def: AST.globdef Asm.fundef unit) : Z :=
  match def with
  | AST.Gfun (External e) => 1
  | AST.Gfun (Internal f) => Asm.code_size instr_size (Asm.fn_code f)
  | AST.Gvar v => AST.init_data_list_size (AST.gvar_init v)
  end.

Lemma def_size_pos:
  forall d,
    0 <= def_size d.
Proof.
  unfold def_size. intros.
  destr.
  destr. generalize (code_size_non_neg instr_size instr_size_bound (Asm.fn_code f0)); lia.
  lia.
  generalize (AST.init_data_list_size_pos (AST.gvar_init v)); lia.
Qed.

Definition defs_size (defs: list (AST.globdef Asm.fundef unit)) : Z :=
  fold_right (fun def sz => def_size def + sz) 0 defs.

Lemma defs_size_pos:
  forall defs, 0 <= defs_size defs.
Proof.
  induction defs as [|def defs].
  - cbn. lia.
  - cbn. generalize (def_size_pos def).
    intros. apply OMEGA2; eauto.
Qed.


(** * Generation of symbol table *)


(** ** Compute the symbol table *)

Definition get_bind_ty id :=
  if is_def_local id then bind_local else bind_global.

(** get_symbol_entry takes the ids and the current sizes of data and text sections and 
    a global definition as input, and outputs the corresponding symbol 
entry *)
Definition get_symbentry (id:ident) (def: (AST.globdef Asm.fundef unit)) : symbentry :=
  let bindty := get_bind_ty id in
  match def with
  | (Gvar gvar) =>
    match AST.gvar_init gvar with
    | nil => 
      (** This is an external data symbol *)
      {|
        symbentry_bind := bindty;
        symbentry_type := symb_data;
        symbentry_value := 0;
        symbentry_secindex := secindex_undef;
        symbentry_size := 0;
      |}
    | [Init_space sz] =>
      (** This is an external data symbol in the COMM section *)
      (** TODO: static uninitializd data is also put into this section*)
      {|
        symbentry_bind := bind_global;
        symbentry_type := symb_data;
        symbentry_value := 8 ; (* 8 is a safe alignment for any data *)
        symbentry_secindex := secindex_comm;
        symbentry_size := Z.max sz 0;
      |}
    | _ => match gvar.(gvar_readonly) with
          (** Set section index to the id of the section*)
          | true =>
           (** This is an internal read-only data symbol *)           
           {|
             symbentry_bind := bindty;
             symbentry_type := symb_data;
             symbentry_value := 0; (* section for each def, so offset is zero *)
             symbentry_secindex := secindex_normal id;
             symbentry_size := AST.init_data_list_size (AST.gvar_init gvar);
           |}
         | false =>
           (** This is an internal data symbol *)
           {|
             symbentry_bind := bindty;
             symbentry_type := symb_data;
             symbentry_value := 0;
             symbentry_secindex := secindex_normal id;
             symbentry_size := AST.init_data_list_size (AST.gvar_init gvar);
           |}
         end
    end
  | (Gfun (External ef)) =>
    (** This is an external function symbol *)
    {|
      symbentry_bind := bindty;
      symbentry_type := symb_func;
      symbentry_value := 0;
      symbentry_secindex := secindex_undef;
      symbentry_size := 0;
    |}
  | (Gfun (Internal f)) =>
    {|
      symbentry_bind := bindty;
      symbentry_type := symb_func;
      symbentry_value := 0;
      symbentry_secindex := secindex_normal id;
      symbentry_size := code_size instr_size (fn_code f);
    |}
  end.


Definition acc_symb (stbl: symbtable) 
           (iddef: ident * (AST.globdef Asm.fundef unit)) := 
  let (id, def) := iddef in
  let e := get_symbentry id def in
  PTree.set id e stbl.


(** Generate the symbol and section table *)
Definition gen_symb_table defs :=
  let rstbl :=
      fold_left acc_symb defs (PTree.empty symbentry) in
  rstbl.


(** Create the code section *)
Definition acc_gen_section (acc: sectable) (iddef: ident * (globdef fundef unit)) : sectable :=
  let (id, def) := iddef in
  match def with
  | Gfun (Internal f) => PTree.set id (sec_text (fn_code f)) acc
  | Gvar v =>
    match gvar_init v with
    | [] => acc
    | [Init_space _] => acc
    | _ =>
      if gvar_readonly v then
        PTree.set id (sec_rodata (gvar_init v)) acc
      else
        PTree.set id (sec_rwdata (gvar_init v)) acc
    end
  | _ => acc
  end.

Definition create_sec_table (defs : list (ident * (globdef fundef unit))) : sectable :=
  fold_left acc_gen_section defs (PTree.empty section).

    
Record wf_prog (p:Asm.program) : Prop :=
  {
    wf_prog_norepet_defs: list_norepet (map fst (AST.prog_defs p));
    (* wf_prog_main_exists: main_exists (AST.prog_main p) (AST.prog_defs p); *)
    (* wf_prog_defs_aligned: Forall def_aligned (map snd (AST.prog_defs p)); *)
    wf_prog_no_local_jmps: Forall def_instrs_valid (map snd (AST.prog_defs p));
    (* wf_prog_data_size_aligned: Forall data_size_aligned (map snd (AST.prog_defs p)); *)
  }.

Definition check_wellformedness p : { wf_prog p } + { ~ wf_prog p }.
Proof.
  destruct (list_norepet_dec ident_eq (map fst (AST.prog_defs p))).
  (* destruct (main_exists_dec (AST.prog_main p) (AST.prog_defs p)). *)
  (* destruct (Forall_dec _ def_aligned_dec (map snd (AST.prog_defs p))). *)
  destruct (Forall_dec _ def_instrs_valid_dec (map snd (AST.prog_defs p))).
  (* destruct (Forall_dec _ data_size_aligned_dec (map snd (AST.prog_defs p))). *)
  left; constructor; auto.
  right. inversion 1. apply n. auto.
  (* right. inversion 1. apply n. auto. *)
  right. inversion 1. apply n. auto.
  (* right. inversion 1. apply n. auto. *)
  (* right. inversion 1. apply n. auto. *)
Qed.


(** The full translation *)
Definition transf_program (p:Asm.program) : res program :=
  if check_wellformedness p then
    let symb_tbl := gen_symb_table (AST.prog_defs p) in
    let sec_tbl := create_sec_table (AST.prog_defs p) in
    if zle (defs_size (map snd (AST.prog_defs p))) Ptrofs.max_unsigned then
      OK {| prog_defs := AST.prog_defs p;
            prog_public := AST.prog_public p;
            prog_main := AST.prog_main p;
            prog_sectable := sec_tbl;
            prog_symbtable := symb_tbl;
            prog_reloctables := PTree.empty reloctable;
            prog_senv := Globalenvs.Genv.to_senv (Globalenvs.Genv.globalenv p)
         |}
    else 
      Error (msg "Program too big")
  else
    Error (msg "Program not well-formed").

End INSTR_SIZE.
