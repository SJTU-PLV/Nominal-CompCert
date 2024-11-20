Require Import Coqlib Errors.
Require Import AST Linking Values Events Globalenvs Memory Smallstep.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers.

Require Import Encrypt.

Inductive state :  Type :=
| Initial (i: int) (r : val) (m : mem)
| Final (m : mem).

Definition genv := Genv.t fundef unit.

Section WITH_SE.
  Context (se:Genv.symtbl).

  Inductive initial_state (ge:genv) : query li_c -> state -> Prop :=
  | initial_state_intro m i b ofs fv
      (FIND: Genv.find_funct ge fv = Some (Internal func_encrypt_b1)):
    initial_state ge (cq fv int_ptr__void_sg ((Vint i) :: (Vptr b ofs) :: nil) m)
      (Initial i (Vptr b ofs) m).

  Inductive final_state: state -> reply li_c -> Prop :=
  | final_state_intro m :
    final_state (Final m) (cr Vundef m).

  Inductive at_external: state -> query li_c -> Prop :=.
  Inductive after_external: state -> reply li_c -> state -> Prop :=.
  
  Inductive step : state -> trace -> state -> Prop :=
  | step_encrypt
      i b ofs m m' key keyb output
      (FINDKEY: Genv.find_symbol se key_id = Some keyb)
      (LOAD: Mem.loadv Mint32 m (Vptr keyb Ptrofs.zero) = Some (Vint key))
      (XOR: output = Int.xor i key)
      (STORE: Mem.storev Many64 m (Vptr b ofs) (Vint output) = Some m'):
      step (Initial i (Vptr b ofs) m) E0 (Final m').


End WITH_SE.

Program Definition L_E : Smallstep.semantics li_c li_c :=
  {|
   Smallstep.skel := erase_program b1;
   Smallstep.state := state;
   Smallstep.activate se :=
     let ge := Genv.globalenv se b1 in
     {|
       Smallstep.step ge := step ge;
       Smallstep.valid_query q := Genv.is_internal ge (cq_vf q);
       Smallstep.initial_state := initial_state ge;
       Smallstep.at_external := at_external;
       Smallstep.after_external := after_external;
       Smallstep.final_state := final_state;
       globalenv := ge;
     |}
  |}.
