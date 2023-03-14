Require Import String.
Require Import Coqlib Errors.
Require Import AST Asm Globalenvs.
Require Import RelocProg RelocProgram RelocElf RelocElfSemantics DecodeRelocElf.

(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.

Definition total_if {A: Type}
          (flag: unit -> bool) (f: A -> A) (prog: A) : A :=
  if flag tt then f prog else prog.

Definition partial_if {A: Type}
          (flag: unit -> bool) (f: A -> res A) (prog: A) : res A :=
  if flag tt then f prog else OK prog.


(* stack requirements *)

Definition fn_stack_requirements (tp: Asm.program) (id: ident) : Z :=
    match Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv tp) (Values.Global id) with
    | Some (Internal f) => Asm.fn_stacksize f
    | _ => 0
    end.

(* CCELF Start *)
Definition reloc_fn_stack_requirements {I D: Type} (tp: RelocProg.program Asm.fundef unit I D) (id:ident) : Z :=
  match List.find (fun '(id',_) => ident_eq id id') (RelocProg.prog_defs tp) with
  | None => 0
  | Some (_, def) =>
    match def with
    | (Gfun (Internal f)) => Asm.fn_stacksize f
    | _ => 0
    end
  end.

Definition elf_fn_stack_requirements (tp: RelocElf.elf_file) (id:ident) : Z :=
  match (RelocElfSemantics.decode_elf tp) with
  | OK p =>
    reloc_fn_stack_requirements p id
  | _ => 0
  end.
  
Definition elf_bytes_stack_requirements (tp: list Integers.Byte.int * Asm.program * Globalenvs.Senv.t)
           (id:ident) : Z :=
  let '(b, p, s) := tp in
  match DecodeRelocElf.decode_elf_file b p s with
  | OK ef => elf_fn_stack_requirements ef id
  | _ => 0
  end.
(* CCELF End *)
