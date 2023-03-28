Require Import Integers Values Memory.
Require Import Ctypes Clight.
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

Program Definition top_spec1 : Smallstep.semantics li_c li_c :=
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

Inductive match_client_state : state -> Clight.state -> Prop :=
|match_process (j:meminj) m tm output pb pb'
  (Hm: Mem.inject j m tm)
  (FINDP : Genv.find_symbol se process_id = Some pb)
  (FINJ: j pb = Some (pb',0))
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_client_state (Callprocess output m) (Callstate (Vptr pb' Ptrofs.zero) (Vint output :: nil) Kstop tm)
|match_request (j:meminj) m tm input rb rb'
   (Hm: Mem.inject j m tm)
  (FINDP : Genv.find_symbol se process_id = Some rb)
  (FINJ: j rb = Some (rb',0))
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_client_state (Callrequest input m) (Callstate (Vptr rb' Ptrofs.zero) (Vint input :: nil) Kstop tm).
(*|match_return (j:meminj) m tm
  (Hm: Mem.inject j m tm)
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_client_state (Return m) (Returnstate Vundef Kstop tm). *)

Inductive match_server_state : state -> Serverspec.state -> Prop :=
|match_encrypt (j:meminj) m tm pb pb' input
   (Hm: Mem.inject j m tm)
  (FINDP : Genv.find_symbol se process_id = Some pb)
  (FINJ: j pb = Some (pb',0))
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_server_state (Callencrypt input (Vptr pb Ptrofs.zero) m) (Call1 (Vptr pb' Ptrofs.zero) input tm).

Inductive match_state : state -> list (frame L) -> Prop :=
|match_client_intro s1 s2 k:
   match_client_state s1 s2 ->
   match_state s1 (st L true s2 :: k)
|match_server_intro s1 s2 k:
  match_server_state s1 s2 ->
  match_state s1 (st L false s2 :: k)
|match_return_introc (j:meminj) m tm
  (Hm: Mem.inject j m tm)
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state (Return m) (st L true (Returnstate Vundef Kstop tm) :: nil) 
|match_return_intros (j:meminj) m tm
  (Hm: Mem.inject j m tm)
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state (Return m) (st L false (Return2 tm) :: nil) .

End MS.
  
Lemma top_simulation_L1:
  forward_simulation (cc_c injp) (cc_c injp) top_spec1 composed_spec1.
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *. subst.
  pose (ms := fun s1 s2 => match_state w se1 s1 s2).
  eapply forward_simulation_plus with (match_states := ms).
  destruct w as [f0 m0 tm0 Hm0]; cbn in Hse; inv Hse; subst; cbn in *; eauto.
  - intros. inv H. cbn in *. inv H3.
    unfold valid_query.
    unfold L. simpl.
    unfold SmallstepLinking.valid_query, Smallstep.valid_query.
    cbn.
    inv H0; try congruence; cbn; eauto.
    destruct (Genv.invert_symbol se1 b1) eqn:INV.
    2: {
      unfold Genv.is_internal, Genv.find_funct, Genv.find_funct_ptr.
      rewrite !Genv.find_def_spec.
      assert (Genv.invert_symbol se2 b2 = None).
      destruct (Genv.invert_symbol se2 b2) as [i|] eqn:FIND2; eauto.
      apply Genv.invert_find_symbol in FIND2.
      inv H2.
      eapply mge_symb in FIND2 as FIND1; eauto.
      apply Genv.find_invert_symbol in FIND1. congruence.
      rewrite H0.
      destruct Ptrofs.eq_dec; destruct Ptrofs.eq_dec; eauto.
    }
    apply Genv.invert_find_symbol in INV as FIND.
    assert (delta = 0).
    { inv H2. exploit mge_dom. eapply Genv.genv_symb_range; eauto.
      intros [a b]. rewrite H in b. inv b. reflexivity.
    }
    subst delta.
    destruct (Ptrofs.eq_dec ofs1 Ptrofs.zero).
    2: {
      unfold Genv.is_internal. unfold Genv.find_funct.
      rewrite !pred_dec_false. reflexivity.
      rewrite Ptrofs.add_zero. auto.
      rewrite Ptrofs.add_zero. auto.
    }
    (* unfold Genv.is_internal, Genv.find_funct, Genv.find_funct_ptr.
    cbn. rewrite !Ptrofs.add_zero.
    rewrite pred_dec_true; eauto.
    rewrite pred_dec_true; eauto.
    destruct (peq i 3). subst. cbn.
     *)
    (*true, need lemma about Genv.globalenv construction of genv from symtbl and static definition*)
    admit.
  - intros q1 q2 s1 Hq Hi1. inv Hq. inv H1. inv Hi1; cbn in *.
    + (*process*)
      inv Hse.
      eapply Genv.find_symbol_match in H5 as FIND'; eauto.
      destruct FIND' as [fb' [FINJ FIND']]. inv H.
      inv H0. inv H7. inv H3.
      rewrite FINJ in H4. inv H4. rename b2 into fb'. rewrite Ptrofs.add_zero.
      exists ((st L true (Callstate (Vptr fb' Ptrofs.zero) (Vint output :: nil) Kstop m2)) :: nil).
      split. split.
      -- cbn. admit. (*same lemma as above*)
      -- cbn.
         set (gec := (Clight.globalenv se2
       {|
       Ctypes.prog_defs := global_definitions_client;
       Ctypes.prog_public := public_idents_client;
       Ctypes.prog_main := main_id;
       Ctypes.prog_types := composites;
       Ctypes.prog_comp_env := Maps.PTree.empty Ctypes.composite;
       Ctypes.prog_comp_env_eq := eq_refl |})).
       assert (FINDP: Genv.find_funct gec (Vptr fb' Ptrofs.zero) = Some (Ctypes.Internal func_process)).
       admit.
       (* Compute type_of_function func_process. *)
       set (targs := (Ctypes.Tcons
            (Ctypes.Tint Ctypes.I32 Ctypes.Signed
                         {| Ctypes.attr_volatile := false; Ctypes.attr_alignas := None |}) Ctypes.Tnil)).
       assert (Ctypes.signature_of_type targs Ctypes.Tvoid cc_default = int__void_sg).
       reflexivity.
       rewrite <- H.
       econstructor; eauto.
       constructor; cbn; eauto. constructor; eauto. constructor.
      -- constructor. econstructor; eauto.
         reflexivity.
    + (*encrypt*)
      admit.
    + (*requese*)
      admit.
  - intros s1 s2 r1 Hms Hf1. inv Hf1. inv Hms;
      try inv H; cbn in *.
    + (*final of server*)
    exists (cr Vundef tm). split. cbn.
    constructor. constructor.
    eexists. split. eauto. constructor; eauto. constructor.
    +  exists (cr Vundef tm). split. cbn.
    constructor. constructor.
    eexists. split. eauto. constructor; eauto. constructor.
  - intros. cbn in *. inv H0.
  - (*step*)
    intros. inv H; inv H0; inv H; cbn.
    + (*process*)
      admit.
    + (*encrypt*)
      admit.
    + (*request*)
      admit.
  - constructor. intros. inv H.
Admitted.


