Require Import Integers Values Memory.
Require Import Clight.
Require Import InjectFootprint Invariant ValueAnalysis.
Require Import CA Asm CallConv CKLRAlgebra.
Require Import Client Server Serverspec.
Require Import Smallstep Linking SmallstepLinking.

Require Import LanguageInterface.
(** * C-level composed specification *)

Definition result_def_unit :=
  {|
    gvar_info := tt;
    gvar_init := nil;
    gvar_readonly := false;
    gvar_volatile := false |}.

Definition linked_skel1 : program unit unit:=
  {|
    prog_defs := (result_id, Gvar result_def_unit) :: (key_id, Gvar key_def) ::
                   (request_id, Gfun tt) :: (encrypt_id, Gfun tt) ::
                   (process_id, Gfun tt) :: nil;
    prog_public := encrypt_id :: request_id :: process_id :: result_id ::
                     key_id :: encrypt_id :: process_id :: nil;
    prog_main := 42%positive
  |}.

Theorem link_ok :
  link (skel (Clight.semantics1 client)) (skel L1) = Some linked_skel1.
Proof. reflexivity. Qed.

Definition L := fun i : bool => if i then (Clight.semantics1 client) else L1.
Definition composed_spec1 := semantics L linked_skel1.

Theorem link_result :
  compose (Clight.semantics1 client) L1 = Some composed_spec1.
Proof.
  unfold compose. rewrite link_ok. simpl. reflexivity.
Qed.


(** * C-level top specification *)


Inductive state : Type :=
| Callrequest (input : int) (m:mem)
| Callencrypt (input : int) (fptr : val) (m:mem)
| Callprocess (output : int) (m:mem)
| Return (m:mem).

Definition genv := Genv.t unit unit.

Section WITH_SE.
Context (se:Genv.symtbl).

Inductive initial_state : query li_c ->  state -> Prop :=
|initial_process output m fb
   (FIND: Genv.find_symbol se process_id = Some fb):
  initial_state (cq (Vptr fb Ptrofs.zero) int__void_sg ((Vint output) :: nil) m)
    (Callprocess output m)
|initial_encrypt i fb b ofs m
   (FIND: Genv.find_symbol se encrypt_id = Some fb):
  initial_state (cq (Vptr fb Ptrofs.zero) int_fptr__void_sg ((Vint i) :: (Vptr b ofs) :: nil) m)
    (Callencrypt i (Vptr b ofs) m) 
|initial_request i m fb
   (FIND: Genv.find_symbol se request_id = Some fb):
  initial_state (cq (Vptr fb Ptrofs.zero) int__void_sg ((Vint i) :: nil) m) (Callrequest i m).
    
Inductive at_external : state -> query li_c -> Prop :=.
Inductive after_external : state -> c_reply -> state -> Prop := .

Inductive final_state : state -> reply li_c -> Prop :=
|final_process m:
  final_state (Return m) (cr Vundef m).

Definition valid_query (q: query li_c) : bool :=
  match (cq_vf q) with
  |Vptr b ofs =>  if Ptrofs.eq_dec ofs Ptrofs.zero then
                  match Genv.invert_symbol se b with
                  | Some id => (id =? process_id)%positive || (id =? encrypt_id)%positive ||
                                (id =? request_id)%positive
                  | None => false
                  end
                  else false
  |_  => false
  end.

Inductive step : state -> trace -> state -> Prop :=
|step_process output m m' b
  (FIND: Genv.find_symbol se result_id = Some b)
  (SET: Mem.storev Mint32 m (Vptr b Ptrofs.zero) (Vint output) = Some m'):
  step (Callprocess output m) E0 (Return m')
|step_encrypt kb pb key input m output
   (FINDK: Genv.find_symbol se key_id = Some kb)
   (FINDP: Genv.find_symbol se process_id = Some pb)
   (READ: Mem.loadv Mint32 m (Vptr kb Ptrofs.zero) = Some (Vint key))
   (XOR: output = Int.xor input key):
  step (Callencrypt input (Vptr pb Ptrofs.zero) m) E0 (Callprocess output m)
|step_request input pb m
  (FINDP: Genv.find_symbol se process_id = Some pb):
  step (Callrequest input m) E0 (Callencrypt input (Vptr pb Ptrofs.zero) m).

End WITH_SE.

Program Definition top_spec : Smallstep.semantics li_c li_c :=
    {|
      Smallstep.skel := linked_skel1;
      Smallstep.state := state;
      Smallstep.activate se :=
        {|
          Smallstep.step _ := step se;
          Smallstep.valid_query := valid_query se;
          Smallstep.initial_state := initial_state se;
          Smallstep.at_external := at_external;
          Smallstep.after_external := after_external;
          Smallstep.final_state := final_state;
          globalenv := tt;
        |}
    |}.

(** Proof of top_spec -> composed_spec1 *)

Section MS.

Variable w: injp_world.
Variable se tse : Genv.symtbl.

Hypothesis MSTB : match_stbls injp w se tse.

Inductive match_state : state -> Clight.state -> Prop :=
|match_process (j:meminj) m tm input pb j pb'
  (Hm: Mem.inject j m tm)
  (FINDP : Genv.find_symbol se process_id = Some pb)
  (FINJ: j pb = Some (pb',0))
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state (Callprocess input m) (Callstate (Vptr pb Ptrofs.zero) (Vint input :: nil) Kstop tm).

End MS.
  

