Require Import Coqlib Errors.
Require Import AST Linking Values Events Globalenvs Memory Smallstep.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers.

Require Import Server.

(** * pseudo code *)

(*
//L1
int key;
//L2
const int key = 42;
//common
void encrypt (void ( *complete) (int), int input){
  int output = key ^ input;
  complete (output);
}

*)
Inductive state: Type :=
| Call1
    (fptr: val)
    (input: int)
    (m: mem)
| Call2
    (fptr: val)
    (output: int)
    (m: mem)
| Return1
    (m: mem)
| Return2
    (m: mem).

Definition genv := Genv.t fundef unit.

Section WITH_SE.
  Context (se: Genv.symtbl).
  
Inductive initial_state1 (ge:genv) : query li_c -> state -> Prop :=
| initial_state_intro1
    v m i b ofs
    (FIND: Genv.find_funct ge v = Some (Internal func_encrypt_b1)):
  initial_state1 ge (cq v int_fptr__void_sg ((Vptr b ofs) :: (Vint i) :: nil) m) (Call1 (Vptr b ofs) i m).

Inductive initial_state2 (ge:genv) : query li_c -> state -> Prop :=
| initial_state_intro2
    v m i b ofs
    (FIND: Genv.find_funct ge v = Some (Internal func_encrypt_b2)):
    initial_state2 ge (cq v int_fptr__void_sg ((Vptr b ofs) :: (Vint i) :: nil) m) (Call1 (Vptr b ofs) i m).

Inductive at_external (ge:genv): state -> query li_c -> Prop :=
| at_external_intro
    m output b ofs:
    at_external ge (Call2 (Vptr b ofs) output m) (cq (Vptr b ofs) int__void_sg (Vint output :: nil) m).

Inductive after_external: state -> reply li_c -> state -> Prop :=
| after_external_intro
    vf m m' output res:
    after_external (Call2 vf output m) (cr res m') (Return1 m').

Inductive final_state: state -> reply li_c  -> Prop :=
  | final_state_intro
      m:
      final_state (Return2 m) (cr Vundef m).

Inductive step1 : state -> trace -> state -> Prop := 
| step_xor1
    input output m b ofs key keyb
    (FINDKEY: Genv.find_symbol se key_id = Some keyb)
    (LOADKEY: Mem.loadv Mint32 m (Vptr keyb Ptrofs.zero) = Some (Vint key))
    (XOR: output = Int.xor input key):
  step1 (Call1 (Vptr b ofs) input m) E0 (Call2 (Vptr b ofs) output m)
| step_asmret m:
    step1 (Return1 m) E0 (Return2 m).

Inductive step2 : state -> trace -> state -> Prop :=
| step_xor2
    input m b ofs:
  step2 (Call1 (Vptr b ofs) input m) E0 (Call2 (Vptr b ofs) (Int.xor input (Int.repr 42)) m)
| step_asmfree m:
  step2 (Return1 m) E0 (Return2 m).
                                    
End WITH_SE.

Program Definition L1 : Smallstep.semantics li_c li_c :=
  {|
   Smallstep.skel := erase_program b1;
   Smallstep.state := state;
   Smallstep.activate se :=
     let ge := Genv.globalenv se b1 in
     {|
       Smallstep.step ge := step1 ge;
       Smallstep.valid_query q := Genv.is_internal ge (cq_vf q);
       Smallstep.initial_state := initial_state1 ge;
       Smallstep.at_external := at_external ge;
       Smallstep.after_external := after_external;
       Smallstep.final_state := final_state;
       globalenv := ge;
     |}
  |}.

Program Definition L2 : Smallstep.semantics li_c li_c :=
  {|
   Smallstep.skel := erase_program b2;
   Smallstep.state := state;
   Smallstep.activate se :=
     let ge := Genv.globalenv se b2 in
     {|
       Smallstep.step ge := step2;
       Smallstep.valid_query q := Genv.is_internal ge (cq_vf q);
       Smallstep.initial_state := initial_state2 ge;
       Smallstep.at_external := at_external ge;
       Smallstep.after_external := after_external;
       Smallstep.final_state := final_state;
       globalenv := ge;
     |}
  |}.




