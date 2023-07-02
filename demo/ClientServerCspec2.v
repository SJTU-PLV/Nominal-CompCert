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

Definition linked_skel2 : program unit unit:=
  {|
    prog_defs := (result_id, Gvar result_def_unit) :: (key_id, Gvar key_def_const) ::
                   (request_id, Gfun tt) :: (encrypt_id, Gfun tt) ::
                   (process_id, Gfun tt) :: nil;
    prog_public := encrypt_id :: request_id :: process_id :: result_id ::
                     key_id :: encrypt_id :: process_id :: nil;
    prog_main := 42%positive
  |}.

Theorem link_ok2 :
  link (skel (Clight.semantics1 client)) (skel L2) = Some linked_skel2.
Proof. reflexivity. Qed.


Definition L := fun i : bool => if i then (Clight.semantics1 client) else L2.
Definition composed_spec2 := semantics L linked_skel2.

Theorem link_result :
  compose (Clight.semantics1 client) L2 = Some composed_spec2.
Proof.
  unfold compose. rewrite link_ok2. simpl. reflexivity.
Qed.


(** * C-level top specification *)


Inductive state : Type :=
| Callrequest (input : int) (m:mem)
| Callencrypt (flag: bool) (input : int) (fptr : val) (m:mem)
| Callprocess (flag: bool) (retv: option int) (sp : block) (m:mem)
              (*flag = true means internally invoked, need to free the sp
               flag = false means externally invoked.*)
| Return (retv : option int) (m:mem).

Definition genv := Genv.t unit unit.

Section WITH_SE.
Context (se:Genv.symtbl).

Definition int__int_sg : signature := mksignature (AST.Tint :: nil) Tint cc_default.

Inductive initial_state : query li_c ->  state -> Prop :=
|initial_process sp m fb
   (FIND: Genv.find_symbol se process_id = Some fb):
  initial_state (cq (Vptr fb Ptrofs.zero) intptr__void_sg ((Vptr sp Ptrofs.zero) :: nil) m)
    (Callprocess false None sp m)
|initial_encrypt i fb b ofs m
   (FIND: Genv.find_symbol se encrypt_id = Some fb):
  initial_state (cq (Vptr fb Ptrofs.zero) int_fptr__void_sg ((Vint i) :: (Vptr b ofs) :: nil) m)
    (Callencrypt false i (Vptr b ofs) m) 
|initial_request i m fb
   (FIND: Genv.find_symbol se request_id = Some fb):
  initial_state (cq (Vptr fb Ptrofs.zero) int__int_sg ((Vint i) :: nil) m) (Callrequest i m).
    
Inductive at_external : state -> query li_c -> Prop :=.
Inductive after_external : state -> c_reply -> state -> Prop := .

Inductive final_state : state -> reply li_c -> Prop :=
|final_None m:
  final_state (Return None m) (cr Vundef m)
|final_input i m:
  final_state (Return (Some i) m) (cr (Vint i) m).

Definition valid_query (q: query li_c) : bool :=
  match (cq_vf q) with
  |Vptr b ofs =>  if Ptrofs.eq_dec ofs Ptrofs.zero then
                  match Genv.invert_symbol se b with
                  | Some 3%positive | Some  1%positive | Some 6%positive => true
                  (* => (id =? process_id)%positive || (id =? encrypt_id)%positive ||
                                (id =? request_id)%positive *)
                  | _ => false
                  end
                  else false
  |_  => false
  end.

Definition ret_value : option int -> val :=
  fun oi =>
    match oi with
    |Some i => Vint i
    |None => Vundef
    end.

Definition choose_oi (flag: bool) (i : int) : option int :=
  if flag then Some i else None.

Inductive step : state -> trace -> state -> Prop :=
|step_process_false output m m' b sp oi
  (FIND: Genv.find_symbol se result_id = Some b)
  (READ: Mem.loadv Mint32 m (Vptr sp Ptrofs.zero) = Some (Vint output))
  (SET: Mem.storev Mint32 m (Vptr b Ptrofs.zero) (Vint output) = Some m'):
  step (Callprocess false oi sp m) E0 (Return oi m')
|step_process_true output m m' b sp m'' oi
  (FIND: Genv.find_symbol se result_id = Some b)
  (READ: Mem.loadv Mint32 m (Vptr sp Ptrofs.zero) = Some (Vint output))
  (SET: Mem.storev Mint32 m (Vptr b Ptrofs.zero) (Vint output) = Some m')
  (FREE: Mem.free m' sp 0 8 = Some m'' ):
  step (Callprocess true oi sp m) E0 (Return oi m'')
|step_encrypt kb pb key input m output m' m'' sp oi (flag : bool)
   (FINDK: Genv.find_symbol se key_id = Some kb)
   (FINDP: Genv.find_symbol se process_id = Some pb)
   (XOR: output = Int.xor input key)
   (ALLOC: Mem.alloc m 0 8 = (m',sp))
   (READ: Mem.loadv Mint32 m' (Vptr kb Ptrofs.zero) = Some (Vint key))
   (STORE: Mem.storev Many64 m' (Vptr sp Ptrofs.zero) (Vint output) = Some m'')
   (CHOOOSE: oi = if flag then Some input else None)
  :
  step (Callencrypt flag input (Vptr pb Ptrofs.zero) m) E0 (Callprocess true oi sp m'')
|step_request input pb m eb
   (FINDP: Genv.find_symbol se process_id = Some pb)
   (FINDE: Genv.find_symbol se encrypt_id = Some eb):
  step (Callrequest input m) E0 (Callencrypt true input (Vptr pb Ptrofs.zero) m).

End WITH_SE.

Program Definition top_spec2 : Smallstep.semantics li_c li_c :=
    {|
      Smallstep.skel := linked_skel2;
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

(** Top invariant of top_spec2*)

Section RO.

Variable se : Genv.symtbl.
Variable m0 : mem.

Inductive sound_state : state -> Prop :=
| sound_Callrequest : forall i m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Callrequest i m)
| sound_Callencrypt : forall vf i m b,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Callencrypt b i vf m)
| sound_Callprocess : forall b i m oi,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Callprocess b oi i m)
| sound_Return : forall m oi,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Return oi m).
End RO.

Definition ro_inv '(row se0 m0) := sound_state se0 m0.

Lemma spec2_ro : preserves top_spec2 ro ro ro_inv.
Proof.
  intros [se0 m0] se1 Hse Hw. cbn in Hw. subst.
  split; cbn in *.
  - intros. inv H0; inv H.
    + simpl in SET. apply ro_acc_store in SET.
      constructor; eauto.
      eapply ro_acc_trans; eauto.
      eapply ro_acc_sound; eauto.
    + simpl in SET. apply ro_acc_store in SET.
      apply ro_acc_free in FREE.
      constructor; eauto.
      eapply ro_acc_trans; eauto.
      eapply ro_acc_trans; eauto.
      eapply ro_acc_sound; eauto.
      eapply ro_acc_trans; eauto.
    + assert (ro_acc m m'').
      simpl in STORE.
      eapply ro_acc_trans. eapply ro_acc_alloc; eauto.
      eapply ro_acc_store; eauto.
      constructor; eauto.
      eapply ro_acc_trans; eauto.
      eapply ro_acc_sound; eauto.
    + constructor; eauto.
  - intros. inv H. inv H0. constructor; eauto.
    eapply ro_acc_refl.
    constructor; eauto. eapply ro_acc_refl.
    constructor; eauto. eapply ro_acc_refl.
  - intros. inv H0.
  - intros. inv H0; inv H; constructor; eauto.
Qed.

Theorem top2_ro :
  forward_simulation ro ro top_spec2 top_spec2.
Proof.
  eapply preserves_fsim. eapply spec2_ro; eauto.
Qed.

Definition wt_inv : (Genv.symtbl * signature) -> state -> Prop :=
  fun a b => proj_sig_res (snd a) = Tint.

Lemma spec2_wt : preserves top_spec2 wt_c wt_c wt_inv.
Proof.
  intros [se0 sg] se1 Hse Hw. cbn in Hw. subst.
  split; cbn in *.
  - intros. inv H0; inv H;
    unfold wt_inv; simpl; eauto.
  - intros. inv H. inv H0. constructor; eauto.
    constructor. constructor.
  - intros. inv H0.
  - intros. inv H0; inv H. constructor; eauto.
    simpl. rewrite H1. eauto.
Qed.

Theorem top2_wt : forward_simulation wt_c wt_c top_spec2 top_spec2.
Proof.
  eapply preserves_fsim. eapply spec2_wt; eauto.
Qed.



(** Proof of top_spec -> composed_spec1 *)

Section MS.

Variable w: injp_world.
Variable se tse : Genv.symtbl.

Let tge1 := Clight.globalenv tse client.
Let tge2 := Genv.globalenv tse b2.

Hypothesis MSTB : match_stbls injp w se tse.
(*
Inductive match_client_state : state -> Clight.state -> Prop :=
|match_process (j:meminj) m tm output pb pb'
  (Hm: Mem.inject j m tm)
  (FINDP : Genv.find_symbol se process_id = Some pb)
  (FINJ: j pb = Some (pb',0))
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_client_state (Callprocess output m) (Callstate (Vptr pb' Ptrofs.zero) (Vint output :: nil) Kstop tm)
|match_request (j:meminj) m tm input rb rb'
   (Hm: Mem.inject j m tm)
  (FINDP : Genv.find_symbol se request_id = Some rb)
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
 *)

Inductive match_state : state -> list (frame L) -> Prop :=
|match_return_introc (j:meminj) m tm oi
  (Hm: Mem.inject j m tm)
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state (Return oi m) (st L true (Returnstate (ret_value oi) Kstop tm) :: nil)
|match_return_intros (j:meminj) m tm
  (Hm: Mem.inject j m tm)
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state (Return None m) ((st L false (Return2 tm)) :: nil)
|match_request_intro
  (j:meminj) m tm input rb rb'
  (Hm: Mem.inject j m tm)
  (FINDP : Genv.find_symbol se request_id = Some rb)
  (FINJ: j rb = Some (rb',0))
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state (Callrequest input m)
    ((st L true (Callstate (Vptr rb' Ptrofs.zero) (Vint input :: nil) Kstop tm))  :: nil)
|match_encrypt_intro1 (j:meminj) m tm v tv input
  (Hm: Mem.inject j m tm)
  (* (FINDP : Genv.find_symbol se process_id = Some pb) *)
  (VINJ: Val.inject j v tv)
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state  (Callencrypt false input v m)
    ((st L false (Call1 tv input tm)) ::nil)
|match_encrypt_intro2 (j:meminj) m tm tm' input vf args v tv sp le tm0 tm1 tm2 m0 f Hm0 Hm1
   (Hm: Mem.inject j m tm)
   (*(FINDP : Genv.find_symbol se process_id = Some pb)
   (FINJ: j pb = Some (pb',0)) *)
   (VINJ: Val.inject j v tv)
   (INJP1: injp_acc w (injpw f m0 tm0 Hm0))
   (ALLOC: Mem.alloc tm0 0 4 = (tm1, sp))
   (STORE: Mem.storev Mint32 tm1 (Vptr sp Ptrofs.zero) (Vint input) = Some tm2)
   (INJP : injp_acc (injpw f m0 tm2 Hm1) (injpw j m tm Hm)):
  match_state  (Callencrypt true input v m)
    ((st L false (Call1 tv input tm)) ::
       (st L true (Callstate vf args (Kcall None func_request ((Maps.PTree.set i_id (sp, Ctypesdefs.tint) empty_env)) le (Kseq (Sreturn (Some (Evar i_id Ctypesdefs.tint))) Kstop)) tm')) ::nil)
|match_process_intro1 (j:meminj) m tm sb sb' pb pb' delta
  (Hm: Mem.inject j m tm)
  (FINDP : Genv.find_symbol se process_id = Some pb)
  (FINJ: j pb = Some (pb',0))
  (SPINJ: j sb = Some (sb',delta))
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state (Callprocess false None sb m)
    ((st L true(Callstate (Vptr pb' Ptrofs.zero) ((Vptr sb' (Ptrofs.repr delta)) :: nil) Kstop tm)):: nil)
|match_process_intro2 (j:meminj) m tm  pb pb' vf tm' sb sb'
  (Hm: Mem.inject j m tm)
  (FINDP : Genv.find_symbol se process_id = Some pb)
  (FINJ: j pb = Some (pb',0))
  (SPINJ: j sb = Some (sb',0))
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state (Callprocess true None sb m)
    ((st L true(Callstate (Vptr pb' Ptrofs.zero) ((Vptr sb' Ptrofs.zero) :: nil) Kstop tm)) ::
       (st L false (Call2 vf sb' tm')) :: nil)
|match_process_intro3 (j:meminj) m tm  pb pb' vf tm' vf' args tm'' sp le i tm0 tm1 tm2 m0 f Hm0 Hm1 sb sb'
  (Hm: Mem.inject j m tm)
  (FINDP : Genv.find_symbol se process_id = Some pb)
  (FINJ: j pb = Some (pb',0))
  (SPINJ: j sb = Some (sb',0))
  (SPFRESH: ~ Mem.valid_block tm1 sb')
  (INJP1: injp_acc w (injpw f m0 tm0 Hm0))
  (ALLOC: Mem.alloc tm0 0 4 = (tm1, sp))
  (STORE: Mem.storev Mint32 tm1 (Vptr sp Ptrofs.zero) (Vint i) = Some tm2)
  (INJP : injp_acc (injpw f m0 tm2 Hm1) (injpw j m tm Hm)):
  match_state (Callprocess true (Some i) sb m)
    ((st L true(Callstate (Vptr pb' Ptrofs.zero) ((Vptr sb' Ptrofs.zero) :: nil) Kstop tm)) ::
       (st L false (Call2 vf sb' tm')) ::
        (st L true (Callstate vf' args (Kcall None func_request ((Maps.PTree.set i_id (sp, Ctypesdefs.tint) empty_env)) le (Kseq (Sreturn (Some (Evar i_id Ctypesdefs.tint))) Kstop)) tm'')) :: nil).

Lemma find_request:
  forall rb rb' j,
    Genv.match_stbls j se tse ->
    Genv.find_symbol se request_id = Some rb ->
    j rb = Some (rb',0) ->
    Genv.find_funct tge1 (Vptr rb' Ptrofs.zero) = Some (Ctypes.Internal func_request).
Proof.
  intros. cbn. rewrite pred_dec_true; eauto.
  unfold global_definitions_client. unfold Genv.find_funct_ptr.
  rewrite Genv.find_def_spec.
  eapply Genv.find_symbol_match in H; eauto.
  destruct H as [tb' [A B]]. rewrite A in H1. inv H1.
  apply Genv.find_invert_symbol in B. cbn.
  rewrite B. rewrite Maps.PTree.gso.
  rewrite Maps.PTree.gso.
  rewrite Maps.PTree.gss. reflexivity.
  unfold request_id, process_id. congruence.
  unfold request_id, result_id. congruence.
Qed.

Lemma find_process:
  forall rb rb' j,
    Genv.match_stbls j se tse ->
    Genv.find_symbol se process_id = Some rb ->
    j rb = Some (rb',0) ->
    Genv.find_funct tge1 (Vptr rb' Ptrofs.zero) = Some (Ctypes.Internal func_process).
Proof.
  intros. cbn. rewrite pred_dec_true; eauto.
  unfold global_definitions_client. unfold Genv.find_funct_ptr.
  rewrite Genv.find_def_spec.
  eapply Genv.find_symbol_match in H; eauto.
  destruct H as [tb' [A B]]. rewrite A in H1. inv H1.
  apply Genv.find_invert_symbol in B. cbn.
  rewrite B. rewrite Maps.PTree.gso.
  rewrite Maps.PTree.gss. reflexivity.
  unfold result_id, process_id. congruence.
Qed.

Lemma find_encrypt:
  forall rb rb' j,
    Genv.match_stbls j se tse ->
    Genv.find_symbol se encrypt_id = Some rb ->
    j rb = Some (rb',0) ->
    Genv.find_funct tge2 (Vptr rb' Ptrofs.zero) = Some (Internal func_encrypt_b2).
Proof.
  intros. cbn. rewrite pred_dec_true; eauto.
  unfold global_definitions_client. unfold Genv.find_funct_ptr.
  unfold tge2.
  rewrite Genv.find_def_spec.
  eapply Genv.find_symbol_match in H; eauto.
  destruct H as [tb' [A B]]. rewrite A in H1. inv H1.
  apply Genv.find_invert_symbol in B. cbn.
  rewrite B. rewrite Maps.PTree.gso.
  rewrite Maps.PTree.gss. reflexivity.
  unfold encrypt_id, complete_id. congruence.
Qed.

Lemma find_encrypt_1:
  forall rb rb' j,
    Genv.match_stbls j se tse ->
    Genv.find_symbol se encrypt_id = Some rb ->
    j rb = Some (rb',0) ->
    Genv.find_funct tge1 (Vptr rb' Ptrofs.zero) = Some (func_encrypt_external).
Proof.
  intros. cbn. rewrite pred_dec_true; eauto.
  unfold global_definitions_client. unfold Genv.find_funct_ptr.
  unfold tge2.
  rewrite Genv.find_def_spec.
  eapply Genv.find_symbol_match in H; eauto.
  destruct H as [tb' [A B]]. rewrite A in H1. inv H1.
  apply Genv.find_invert_symbol in B. cbn.
  rewrite B.
  rewrite Maps.PTree.gso.
  rewrite Maps.PTree.gso.
  rewrite Maps.PTree.gso.
  rewrite Maps.PTree.gss. reflexivity.
  unfold encrypt_id, request_id. congruence.
  unfold encrypt_id, process_id. congruence.
  unfold encrypt_id, result_id. congruence.
Qed.
  

Lemma find_encrypt':
  forall rb j,
    Genv.match_stbls j se tse ->
    Genv.find_symbol se encrypt_id = Some rb ->
    exists rb', j rb = Some (rb',0) /\ Genv.find_symbol tge2 encrypt_id = Some rb' /\
    Genv.find_funct tge2 (Vptr rb' Ptrofs.zero) = Some (Internal func_encrypt_b2).
Proof.
  intros. eapply Genv.find_symbol_match in H as F; eauto.
  destruct F as [rb' [A B]].
  exists rb'. split. eauto. split. eauto.
  eapply find_encrypt; eauto.
Qed.

Lemma find_process':
  forall rb j,
    Genv.match_stbls j se tse ->
    Genv.find_symbol se process_id = Some rb ->
    exists rb', j rb = Some (rb',0) /\ Genv.find_symbol tge2 process_id = Some rb' /\
    Genv.find_funct tge1 (Vptr rb' Ptrofs.zero) = Some (Ctypes.Internal func_process).
Proof.
  intros. eapply Genv.find_symbol_match in H as F; eauto.
  destruct F as [rb' [A B]].
  exists rb'. split. eauto. split. eauto.
  eapply find_process; eauto.
Qed.


Lemma find_keyid:
  forall rb j,
    Genv.match_stbls j se tse ->
    Genv.find_symbol se key_id = Some rb ->
    exists rb', j rb = Some (rb', 0) /\ Genv.find_symbol tge2 key_id = Some rb'.
Proof.
  intros. eapply Genv.find_symbol_match in H as F;eauto. 
Qed.

Lemma find_process_server:
  forall rb',
  Genv.find_symbol tge2 process_id = Some rb' ->
  Genv.find_funct tge2 (Vptr rb' (Ptrofs.repr 0)) =
    Some (External (EF_external "complete" intptr__void_sg)).
Proof.
  intros. simpl in *.
  unfold Ptrofs.zero. destruct Ptrofs.eq_dec;try congruence.
  eapply Genv.find_funct_ptr_iff. unfold Genv.find_def.
  unfold tge2. simpl.
  unfold Genv.find_symbol in H.
  unfold Genv.add_globdef.
  unfold Maps.PTree.prev. simpl.
  unfold process_id in *. rewrite H.
  unfold NMap.get. rewrite NMap.gss.
  auto.
Qed.
  
End MS.




Lemma maxv:
  Ptrofs.max_unsigned = 18446744073709551615.
Proof.
  unfold Ptrofs.max_unsigned. unfold Ptrofs.modulus. unfold Ptrofs.wordsize.
  unfold two_power_nat. unfold Wordsize_Ptrofs.wordsize.
  replace Archi.ptr64 with true by reflexivity. reflexivity.
Qed.



Lemma exec_process_mem_false:
  forall stb tb sm sm1 m output j ssb sb d,
    Mem.loadv Mint32 sm (Vptr ssb Ptrofs.zero) = Some (Vint output) ->
    Mem.storev Mint32 sm (Vptr stb Ptrofs.zero) (Vint output) = Some sm1 ->
    Mem.inject j sm m ->
    j stb = Some (tb,0) ->
    j ssb = Some (sb,d) ->
    exists m1 m2 m3 m4 sp,
      Mem.alloc m 0 8 = (m1, sp) /\
        Mem.storev Mptr m1 (Vptr sp Ptrofs.zero) (Vptr sb (Ptrofs.repr d)) = Some m2 /\
        Mem.loadv Mint32 m2 (Vptr sb (Ptrofs.repr d)) = Some (Vint output) /\
        Mem.storev Mint32 m2 (Vptr tb Ptrofs.zero) (Vint output) = Some m3 /\
        Mem.free m3 sp 0 8 = Some m4 /\
        Mem.unchanged_on (fun b ofs => b = tb -> ~ 0 <= ofs < 4) m m4 /\
        Mem.inject j sm1 m4.
Proof.
  intros.
  destruct (Mem.alloc m 0 8) as [tm' sp] eqn: ALLOC.
  generalize (Mem.perm_alloc_2 _ _ _ _ _ ALLOC). intro PERMSP.
  apply Mem.fresh_block_alloc in ALLOC as FRESH.
  (* store varibale *)
  assert (STORE: {tm''| Mem.store Mptr tm' sp (Ptrofs.unsigned Ptrofs.zero) (Vptr sb (Ptrofs.repr d)) = Some tm''}).
  apply Mem.valid_access_store.
  red. split. red. intros. rewrite Ptrofs.unsigned_zero in H4. simpl in H4.
  exploit PERMSP. instantiate (1:= ofs). unfold Mptr in H4.
  replace Archi.ptr64 with true in H4 by reflexivity. simpl in H4. lia.
   eauto with mem.
  red. exists  0. rewrite Ptrofs.unsigned_zero. lia. destruct STORE as [m2 STORE1].
  (* INJ *)
  exploit Mem.alloc_right_inject; eauto. intro INJ1.
  exploit Mem.store_outside_inject; eauto. intros.
  eapply FRESH. eapply Mem.mi_mappedblocks;eauto.
  intros INJ2.
  (* read val*)
  exploit Mem.loadv_inject; eauto.
  intros (v2 & LOAD & VINJ). rewrite Ptrofs.add_zero_l in LOAD.
  inv VINJ.
  (* store val *)
  exploit Mem.store_mapped_inject; eauto.
  intros (m3 & STORE2 & INJ3). rewrite Z.add_0_r in STORE2.
  
  (* free *) 
  assert (FREE:{m4 | Mem.free m3 sp 0 8 = Some m4}).
  eapply Mem.range_perm_free.
  unfold Mem.range_perm. intros.
  eapply Mem.perm_store_1. eauto.
  eapply Mem.perm_store_1. eauto.
  eapply Mem.perm_alloc_2. eauto. auto.
  destruct FREE as [m4  FREE].

  exploit Mem.free_right_inject;eauto. intros.
  eapply FRESH. eapply Mem.mi_mappedblocks;eauto.
  intros INJ4.

  exists tm',m2,m3,m4,sp. repeat apply conj; eauto.
  
  (* unchanged_on alloc and store *)
  assert (UNC1 : Mem.unchanged_on (fun _ _ => True) m tm').
  eapply Mem.alloc_unchanged_on; eauto.
  assert (UNC2: Mem.unchanged_on (fun b ofs => b <> sp) tm' m2).
  eapply Mem.store_unchanged_on; eauto.      

  assert (UNC3 : Mem.unchanged_on (fun b ofs =>(b = tb -> ~ 0<= ofs < 4) ) m2 m3).
  eapply Mem.store_unchanged_on; eauto.
  assert (UNC4: Mem.unchanged_on (fun b ofs => b <> sp) m3 m4).
  eapply Mem.free_unchanged_on; eauto.      

  inv UNC1. inv UNC2. inv UNC3. inv UNC4.
  
  (* unchanged on *)
  econstructor.
  (* support include *)
  eauto with mem.
  (* perm *)
  intros.
  assert (b<>sp).
  intro. subst.
  exploit Mem.fresh_block_alloc. eapply ALLOC. eauto. auto.
  assert (Mem.valid_block tm' b).
  eapply Mem.valid_block_alloc. eapply ALLOC. auto.  
  assert (Mem.valid_block m2 b).
  eapply Mem.store_valid_block_1;eauto.
  assert (Mem.valid_block m3 b).
  eapply Mem.store_valid_block_1;eauto.  
  
  etransitivity. eauto.
  etransitivity. eauto.
  etransitivity. eauto.
  etransitivity. eauto.
  split;auto.
  
  (* contents *)
  intros.
  assert (b<>sp).
  intro. subst. exploit Mem.fresh_block_alloc. eapply ALLOC. eapply Mem.perm_valid_block. eauto.
  auto.
  
  assert (Mem.perm tm' b ofs Cur Readable).
  eapply Mem.perm_alloc_1. eauto. auto.
  assert (Mem.perm m2 b ofs Cur Readable).
  eapply Mem.perm_store_1. eauto. auto.
  assert (Mem.perm m3 b ofs Cur Readable).
  eapply Mem.perm_store_1. eauto. auto.
  assert (Mem.perm m4 b ofs Cur Readable).
  eapply Mem.perm_free_1. eauto. auto.
  auto.

  etransitivity. eapply unchanged_on_contents2;eauto.
  etransitivity. eapply unchanged_on_contents1;eauto.
  etransitivity. eapply unchanged_on_contents0;eauto.
  etransitivity. eapply unchanged_on_contents;eauto.
  auto.
Qed.        

Lemma exec_process_mem_true:
  forall stb tb sm sm1 sm2 m output j ssb sb,
    Mem.loadv Mint32 sm (Vptr ssb Ptrofs.zero) = Some (Vint output) ->
    Mem.storev Mint32 sm (Vptr stb Ptrofs.zero) (Vint output) = Some sm1 ->
    Mem.free sm1 ssb 0 8 = Some sm2 ->
    Mem.inject j sm m ->
    j stb = Some (tb,0) ->
    j ssb = Some (sb,0) ->
    exists m1 m2 m3 m4 m5 sp,
      Mem.alloc m 0 8 = (m1, sp) /\
        Mem.storev Mptr m1 (Vptr sp Ptrofs.zero) (Vptr sb Ptrofs.zero) = Some m2 /\
        Mem.loadv Mint32 m2 (Vptr sb Ptrofs.zero) = Some (Vint output) /\
        Mem.storev Mint32 m2 (Vptr tb Ptrofs.zero) (Vint output) = Some m3 /\
        Mem.free m3 sp 0 8 = Some m4 /\
        Mem.free m4 sb 0 8 = Some m5 /\
        Mem.unchanged_on (fun b ofs => ((b = tb) -> ~ 0 <= ofs < 4) /\ ((b = sb) -> ~ 0<= ofs <8)) m m5 /\
        Mem.inject j sm2 m5.
Proof.
  intros.
  edestruct exec_process_mem_false as (m1 & m2 & m3 & m4 & sp & ALLOC & STORE1 & LOAD & STORE2 &
                                         FREE1 & UNC14 & INJ14); eauto.
  exploit Mem.free_parallel_inject. apply INJ14. eauto. eauto.
  intros (m5 & FREE2 & INJ5). simpl in FREE2.
  exists m1,m2,m3,m4,m5,sp. repeat apply conj; eauto.
  inv UNC14. econstructor.
  - erewrite (Mem.support_free _ _ _ _ _ FREE2). eauto.
  - intros. 
    destruct H5 as [A B].
    etransitivity. eapply unchanged_on_perm; eauto.
    split. eapply Mem.perm_free_1; eauto.
    destruct (eq_block b sb). right. assert (~ 0 <= ofs < 8).
    eapply B; eauto. lia. left. eauto.
    eapply Mem.perm_free_3; eauto.
  - intros. apply Mem.free_result in FREE2.
    assert (Mem.mem_contents m5 = Mem.mem_contents m4).
    rewrite FREE2. reflexivity. rewrite H7. eapply unchanged_on_contents; eauto.
    apply H5.
Qed.

Lemma load_result_Mptr_eq:
    forall v, v <> Vundef -> Val.has_type v Tptr ->
         Val.load_result Mptr v = v.
Proof.
  intros. unfold Mptr. cbn.
  unfold Tptr in H0. replace Archi.ptr64 with true in * by reflexivity.
  destruct v; cbn in *; eauto; try congruence; eauto.
  inv H0. inv H0. inv H0.
Qed.

Lemma exec_process_plus_false:
  forall se2 fb lf m m1 m2 m3 m4 output sp tb sb d,
    Genv.find_symbol se2 result_id = Some tb ->
    Genv.find_funct (Clight.globalenv se2 client) (Vptr fb Ptrofs.zero) = Some (Ctypes.Internal func_process) ->
    Mem.alloc m 0 8 = (m1, sp) ->
    Mem.storev Mptr m1 (Vptr sp Ptrofs.zero) (Vptr sb (Ptrofs.repr d)) = Some m2 ->
    Mem.loadv Mint32 m2 (Vptr sb (Ptrofs.repr d)) = Some (Vint output)  ->
    Mem.storev Mint32 m2 (Vptr tb Ptrofs.zero) (Vint output) = Some m3 ->
    Mem.free m3 sp 0 8 = Some m4 ->          
    plus (fun _ : unit => SmallstepLinking.step L se2) tt
      (st L true (Callstate (Vptr fb Ptrofs.zero) ((Vptr sb (Ptrofs.repr d)) :: nil) Kstop m) :: lf) E0
      (st L true (Returnstate Vundef Kstop m4) :: lf).

Proof.
  intros.
  cbn.
  eexists. econstructor.
  (* one step : enter the process function*)
  econstructor;eauto.
  simpl.                              
  (* step_internal_function *)
  econstructor.
  (* function entry *)           
  simpl. constructor.
  auto. constructor.
  (* alloc variable *)
  simpl. econstructor;eauto.
  econstructor.
  (* bind parameters *)
  econstructor. erewrite Maps.PTree.gss.
  eauto.
  (* assign loc *)
  econstructor. simpl. eauto.
  eauto.
  econstructor. eauto.
  (* the execution of function body *)
  simpl.
  eapply star_step.
  econstructor.
  eapply step_seq.
  eapply star_step. econstructor.
  eapply step_assign.
  (* assign *)
  (* left value *)
  eapply eval_Evar_global.
  auto.
  instantiate (1 := tb).
  simpl. eauto.
  (* right *)
  econstructor. econstructor.
  econstructor. eapply eval_Evar_local.
  erewrite Maps.PTree.gss. eauto.
  eapply deref_loc_value. simpl. reflexivity.
  eapply Mem.load_store_same in H2 as LOAD; eauto.
  rewrite load_result_Mptr_eq in LOAD; eauto. congruence.
  constructor.
  econstructor. simpl. reflexivity. eauto.
  simpl. unfold Cop.sem_cast;simpl;destruct Archi.ptr64;eauto.
  simpl. econstructor. simpl. eauto.
  eauto.
  (* step skip *)
  eapply star_step.
  econstructor. econstructor.
  (* step return *)
  eapply star_step.
  econstructor. econstructor.
  simpl. replace Archi.ptr64 with true by reflexivity.
  (* prove free sp success *)
  rewrite H5. eauto.
  
  (* star refl *)
  eapply star_refl.
  1-5: eauto.
Qed.

Lemma injp_acc_process:
  forall j m tm m' m3 sp output m4 m5 m6 tb b Hm0 Hm1 vp,
    (* Mem.valid_block m1 b -> *)
    j b = Some (tb,0) ->
    Mem.storev Mint32 m (Vptr b Ptrofs.zero) (Vint output) = Some m' ->
    Mem.alloc tm 0 8 = (m3, sp) ->
    Mem.storev Mptr m3 (Vptr sp Ptrofs.zero) (vp) = Some m4 ->
    Mem.storev Mint32 m4 (Vptr tb Ptrofs.zero) (Vint output) = Some m5 ->
    Mem.free m5 sp 0 8 = Some m6 ->
    Mem.unchanged_on (fun (b : block) (ofs : Z) => b = tb -> ~ 0 <= ofs < 4) tm m6 ->
    injp_acc (injpw j m tm Hm0) (injpw j m' m6 Hm1).
Proof.
  intros j  m tm m' m3 sp output m4 m5 m6 tb b Hm0 Hm1 vp.
  intros INJ STORE ALLOC STORE1 STORE2 FREE UNC.
  
  assert (ro_acc tm m6).
  eapply ro_acc_trans. eapply ro_acc_alloc. eauto.
  eapply ro_acc_trans. eapply ro_acc_store. eauto.
  eapply ro_acc_trans. eapply ro_acc_store. eauto.
  eapply ro_acc_free. eauto.
  
  assert (ro_acc m m').
  eapply ro_acc_store. eauto.
  
  inv H. inv H0.
   
  econstructor;eauto.
  (* unchanged on *)
  eapply Mem.unchanged_on_trans. eauto.
  eapply Mem.store_unchanged_on. eauto. simpl. intros.
  unfold loc_unmapped. congruence. eapply Mem.unchanged_on_refl.
  
  (* target memory unchanged on *)
  inv UNC.
  econstructor;eauto.
  (* perm *)
  intros. eapply unchanged_on_perm. intros.
  intro. subst.
  unfold loc_out_of_reach in H0. eapply H0.
  eauto.
  (* perm not decrease *)
  erewrite Z.sub_0_r.
  exploit Mem.store_valid_access_3. eapply STORE.
  unfold Mem.valid_access. rewrite Ptrofs.unsigned_zero. simpl.
  intros (RNGPERM & DIV). eapply Mem.perm_cur.
  eapply Mem.perm_implies with Writable.
  eapply RNGPERM. auto.
  econstructor.
  auto.
  (* unchanged on contents *)
  intros. eapply unchanged_on_contents.
  intros. subst. intro.
  unfold loc_out_of_reach in H0. eapply H0.
  (* the same reasoning as the perm *)
  eauto.
  erewrite Z.sub_0_r. 
  exploit Mem.store_valid_access_3. eapply STORE.
  unfold Mem.valid_access. rewrite Ptrofs.unsigned_zero. simpl.
  intros (RNGPERM & DIV). eapply Mem.perm_cur.
  eapply Mem.perm_implies with Writable.
  eapply RNGPERM. auto.
  econstructor.
  auto.
  econstructor; congruence.
Qed.


Lemma injp_acc_process_true:
  forall j m tm m' m'' m3 sp output m4 m5 m6 m7 tb b Hm0 Hm1 sb tsb,
    j b = Some (tb,0) ->
    j sb = Some (tsb,0) ->
    Mem.storev Mint32 m (Vptr b Ptrofs.zero) (Vint output) = Some m' ->
    Mem.free m' sb 0 8 = Some m'' ->
    Mem.alloc tm 0 8 = (m3, sp) ->
    Mem.storev Mptr m3 (Vptr sp Ptrofs.zero) (Vptr tsb Ptrofs.zero) = Some m4 ->
    Mem.storev Mint32 m4 (Vptr tb Ptrofs.zero) (Vint output) = Some m5 ->
    Mem.free m5 sp 0 8 = Some m6 ->
    Mem.free m6 tsb 0 8 = Some m7 ->
    Mem.unchanged_on (fun b ofs => ((b = tb) -> ~ 0 <= ofs < 4) /\ ((b = tsb) -> ~ 0<= ofs <8)) tm m7 ->
    injp_acc (injpw j m tm Hm0) (injpw j m'' m7 Hm1).
Proof.
 intros j m tm m' m'' m3 sp output m4 m5 m6 m7 tb b Hm0 Hm1 sb tsb.
  intros INJ1 INJ2 STORE FREE ALLOC STORE1 STORE2 FREE1 FREE2 UNC.
  
  assert (ro_acc tm m7).
  eapply ro_acc_trans. eapply ro_acc_alloc. eauto.
  eapply ro_acc_trans. eapply ro_acc_store. eauto.
  eapply ro_acc_trans. eapply ro_acc_store. eauto.
  eapply ro_acc_trans. eapply ro_acc_free. eauto.
  eapply ro_acc_free. eauto.
  
  assert (ro_acc m m'').
  eapply ro_acc_trans.
  eapply ro_acc_store. eauto.
  eapply ro_acc_free. eauto.
  
  inv H. inv H0.
  econstructor;eauto.
  - (* unchanged on *)
  eapply Mem.unchanged_on_trans.
  eapply Mem.store_unchanged_on. eauto. simpl. intros.
  unfold loc_unmapped. congruence.
  eapply Mem.free_unchanged_on. eauto. intros.
  unfold loc_unmapped. congruence.
  
  - eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. split.
    + intro. subst. apply Mem.store_valid_access_3 in STORE as PERM3.
      destruct PERM3 as (RNGPERM & DIV). intro.
      eapply H0; eauto. rewrite Z.sub_0_r.
      red in RNGPERM. exploit RNGPERM. 2: eauto with mem.
      rewrite Ptrofs.unsigned_zero. simpl. lia.
    + intro. subst. apply Mem.free_range_perm in FREE as RNGPERM.
      intro.
      eapply H0; eauto. rewrite Z.sub_0_r. simpl in STORE.
      eapply Mem.perm_store_2; eauto.
      red in RNGPERM. exploit RNGPERM. 2: eauto with mem. lia.
  - constructor; congruence.
Qed.

Lemma top_simulation_L2:
  forward_simulation (cc_c injp) (cc_c injp) top_spec2 composed_spec2.
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn in *. subst.
  pose (ms := fun s1 s2 => match_state w se1 s1 s2).
  eapply forward_simulation_plus with (match_states := ms).
  destruct w as [f0 m0 tm0 Hm0]; cbn in Hse; inv Hse; subst; cbn in *; eauto.
  - intros. inv H. cbn in *. inv H3.
    unfold valid_query.
    unfold L. simpl.
    unfold SmallstepLinking.valid_query.
    unfold Smallstep.valid_query. simpl.
    inv H0; try congruence; simpl; eauto.
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
    unfold Genv.is_internal.
    rewrite !Ptrofs.add_zero. subst ofs1.
    destruct (peq i 3).
    + subst. setoid_rewrite find_process; eauto.
    + destruct (peq i 1).
      ++ subst i. setoid_rewrite find_encrypt; eauto.
         destruct (Genv.find_funct); cbn; eauto.
         destruct fundef_is_internal; reflexivity.
      ++ destruct (peq i 6).
         subst i. setoid_rewrite find_request; eauto.
         (* Tedious work below : find function fails for b2 *)
         simpl. rewrite !pred_dec_true.
         
         unfold Genv.find_funct_ptr.
         assert (FIND_DEF_CLIENT: forall f, Genv.find_def (Genv.globalenv se2 (Ctypes.program_of_program client)) b2 <> Some (Gfun f)).
         { unfold Genv.globalenv. simpl.
           intros.
           unfold Genv.add_globdef.
           (* se2 b2 = i *)
           assert (A: Maps.PTree.get i (Genv.genv_symb se2) = Some b2).
           erewrite <- Genv.mge_symb. 2: eapply H2.
           eauto. eauto.
           (* destruct all the get *)
           repeat destruct Maps.PTree.get eqn:? at 1;unfold Maps.PTree.prev in *; simpl in *.
           1-15 :try assert (NEQ1: b2 <> b) by (unfold not; intros; subst; exploit Genv.genv_vars_inj;[eapply A | eauto | eauto]; intros; congruence);
           try assert (NEQ2: b2 <> b0) by (unfold not; intros; subst; exploit Genv.genv_vars_inj;[eapply A | eauto | eauto]; intros; congruence);
           try assert (NEQ3: b2 <> b3) by (unfold not; intros; subst; exploit Genv.genv_vars_inj;[eapply A | eauto | eauto]; intros; congruence).
           
           1-8: erewrite NMap.gso;eauto.
           1-4, 9-12: try erewrite NMap.gso;eauto.
           1-2,5-6,9-10,13-14: try erewrite NMap.gso;eauto.
           1-16: try erewrite NMap.gi;try congruence.
           1-16: try setoid_rewrite NMap.gsspec.
           1-16: destruct NMap.elt_eq;try congruence.
           1-8: unfold NMap.get;rewrite NMap.gi;congruence. }

         assert (FIND_DEF_SERVER: forall f, Genv.find_def (Genv.globalenv se2 Server.b2) b2 <> Some (Gfun f)).
         { unfold Genv.globalenv. simpl.
           intros.
           unfold Genv.add_globdef.
           (* se2 b2 = i *)
           assert (A: Maps.PTree.get i (Genv.genv_symb se2) = Some b2).
           erewrite <- Genv.mge_symb. 2: eapply H2.
           eauto. eauto.
           (* destruct all the get *)
           repeat destruct Maps.PTree.get eqn:? at 1;unfold Maps.PTree.prev in *; simpl in *.
           1-8 :try assert (NEQ1: b2 <> b) by (unfold not; intros; subst; exploit Genv.genv_vars_inj;[eapply A | eauto | eauto]; intros; congruence);
           try assert (NEQ2: b2 <> b0) by (unfold not; intros; subst; exploit Genv.genv_vars_inj;[eapply A | eauto | eauto]; intros; congruence).
           1-4: erewrite NMap.gso;eauto.
           1-2,5-6: erewrite NMap.gso;eauto.
           2,4,6,8: erewrite NMap.gi;try congruence.
           1-4: try setoid_rewrite NMap.gsspec;destruct NMap.elt_eq;try congruence;
           unfold NMap.get;rewrite NMap.gi;congruence. }


         assert (RHS: match i with
           | 3%positive | 6%positive | 1%positive => true
           | _ => false
                      end = false).
         { destruct i;try congruence;destruct i;try congruence;auto;destruct i;try congruence;auto. }
         rewrite RHS.
         
         destruct Genv.find_def eqn:?. destruct g. specialize (FIND_DEF_CLIENT f). contradiction.
         destruct Genv.find_def eqn:? at 1. destruct g. rewrite Heqo0 in FIND_DEF_SERVER. specialize (FIND_DEF_SERVER f). contradiction.
         auto. auto.
         destruct Genv.find_def eqn:? at 1. destruct g. rewrite Heqo0 in FIND_DEF_SERVER. specialize (FIND_DEF_SERVER f). contradiction.
         auto. auto.

         auto. auto.
         
  - (* initial state *)
    intros q1 q2 s1 Hq Hi1. inv Hq. inv H1. inv Hi1; cbn in *.
    + (*process*)
      inv Hse.
      eapply Genv.find_symbol_match in H5 as FIND'; eauto.
      destruct FIND' as [fb' [FINJ FIND']]. inv H.
      inv H0. inv H7. inv H3.
      rewrite FINJ in H4. inv H4. rename b2 into fb'. rewrite Ptrofs.add_zero.
      exploit find_process; eauto. intro FINDP. rewrite Ptrofs.add_zero_l.
      exists ((st L true (Callstate (Vptr fb' Ptrofs.zero) (Vptr b0 (Ptrofs.repr delta0) :: nil) Kstop m2)) :: nil).
      split. split.
      -- simpl. unfold Genv.is_internal.
         setoid_rewrite find_process; eauto.
      -- simpl.
         set (targs := (Ctypes.Tcons tintp Ctypes.Tnil)).
       assert (Ctypes.signature_of_type targs Ctypes.Tvoid cc_default = intptr__void_sg).
       reflexivity.
       rewrite <- H.
       econstructor; eauto.
       constructor; cbn; eauto. constructor; eauto. constructor.
      -- econstructor; eauto. reflexivity.
    + (*encrypt*)
      inv Hse.
      eapply Genv.find_symbol_match in H5 as FIND'; eauto.
      destruct FIND' as [fb' [FINJ FIND']]. inv H.
      inv H0. inv H7. inv H3. inv H10.
      rewrite FINJ in H4. inv H4. rename b2 into fb'. rewrite Ptrofs.add_zero.
      exploit find_encrypt; eauto. intro FINDE.
      exists ((st L false (Call1 v'0 i m2)) :: nil).
      split. split.
      -- simpl. unfold Genv.is_internal.
         setoid_rewrite find_encrypt; eauto.
      -- simpl. inv H1. econstructor; eauto.
      -- inv H1.
         econstructor; eauto. reflexivity.
    + (*request*)
      inv Hse.
      eapply Genv.find_symbol_match in H5 as FIND'; eauto.
      destruct FIND' as [fb' [FINJ FIND']]. inv H.
      inv H0. inv H7. inv H3.
      rewrite FINJ in H4. inv H4. rename b2 into fb'. rewrite Ptrofs.add_zero.
      exploit find_request; eauto. intro FINDR.
      exists ((st L true (Callstate (Vptr fb' Ptrofs.zero) (Vint i :: nil) Kstop m2)) :: nil).
      split. split.
      -- simpl. unfold Genv.is_internal. setoid_rewrite FINDR. reflexivity.
      -- simpl.
         set (targs := (Ctypes.Tcons Ctypesdefs.tint Ctypes.Tnil)).
         assert (Ctypes.signature_of_type targs Ctypesdefs.tint cc_default = int__int_sg).
         reflexivity.
         rewrite <- H.
         econstructor; eauto.
         constructor; cbn; eauto. constructor; eauto. constructor.
      -- econstructor; eauto. reflexivity.
  - intros s1 s2 r1 Hms Hf1. inv Hf1; inv Hms;
      try inv H; cbn in *.
    + (*final of server*)
    exists (cr Vundef tm). split. cbn.
    constructor. constructor.
    eexists. split. eauto. constructor; eauto. constructor.
    + exists (cr Vundef tm). split. cbn.
    constructor. constructor.
    eexists. split. eauto. constructor; eauto. constructor.
    + exists (cr (Vint i) tm). split. cbn.
    constructor. constructor.
    eexists. split. eauto. constructor; eauto. constructor.
  - intros. cbn in *. inv H0.
  - (*internal steps *)
    intros. inv H; inv H0.
    
    + (*process1*)
      inv Hse. inv INJP.            
      exploit (Genv.find_symbol_match H). eapply FIND.
      intros (tb & FINDP3 & FINDSYMB).
      exploit exec_process_mem_false; eauto. intros (m3 & m4 & m5 & m6 & sp1 & ALLOC &
                                                       LOAD & STORE1 & STORE2 & FREE1 & UNC & INJ).
      (* muliple step in the function of  process *)
      simpl. exists (st L true (Returnstate Vundef Kstop m6) :: nil).      
      split.
      exploit find_process';eauto. intros (rb' & INJP1 & FINDP1 & FINDP2).
      eapply exec_process_plus_false; eauto.      
      eapply H14 in INJP1. rewrite FINJ in INJP1. inv INJP1. auto.
      
      (* match state *)
      econstructor.
      etransitivity. econstructor;eauto.
      instantiate (1:= INJ). instantiate (1:=Hm'0).
      eapply injp_acc_process. eapply H14. eapply FINDP3. 1-6: eauto.
      
    + (*process2*)
      inv Hse. inv INJP.
            
      exploit (Genv.find_symbol_match H). eapply FIND.
      intros (tb & FINDP3 & FINDSYMB).

      exploit exec_process_mem_true; eauto. intros (m3 & m4 & m5 & m6 & m7 & sp1 & ALLOC &
                                                      STORE1 & LOAD & STORE2 & FREE1 & FREE2 & UNC & INJ).
      (* muliple step in the function of  process *)
      simpl. eexists.
      split.
      eapply plus_trans.
      instantiate (1:= (st L true (Returnstate Vundef Kstop m6) :: st L false (Call2 vf sb' tm') :: nil)).
      instantiate (1:= E0).
      exploit find_process';eauto. intros (rb' & INJP1 & FINDP1 & FINDP2).
      eapply exec_process_plus_false; eauto.
      eapply H14 in INJP1. rewrite FINJ in INJP1. inv INJP1. auto.
      (* final state in client *)
      econstructor. eapply step_pop.
      econstructor. econstructor.
      (* return 1 -> return 2 *)
      eapply star_step. econstructor. simpl. eapply step_asmret. eauto.
      eapply star_refl.
      1-3:eauto.

      (* match state *)
      econstructor.
      etransitivity. econstructor;eauto.
      instantiate (1:= INJ). instantiate (1:=Hm'0).
      eapply injp_acc_process_true. eapply H14. eauto.
      all: eauto.
    + (*process3*)
      inv Hse. inv INJP1. inv INJP.
      exploit (Genv.find_symbol_match H). eapply FIND.
      intros (tb & FINDP3 & FINDSYMB).

      assert (NEQB: tb <> sp0).
      { intro. subst. eapply Mem.fresh_block_alloc. eapply ALLOC.
        eapply Mem.valid_block_inject_2. eapply H14. eauto. eauto.
      }

      assert (VALIDSP: Mem.valid_block tm2 sp0).
      { eapply Mem.store_valid_block_1. eapply STORE.
        unfold Mem.valid_block.
        erewrite Mem.support_alloc;eauto.
        exploit Mem.alloc_result. eapply ALLOC. intros. subst. unfold Mem.nextblock.
        eapply Mem.sup_incr_in1.                
      }
            
      exploit exec_process_mem_true. eauto. eapply SET. eauto. eauto. eauto. eauto.
      intros (m3 & m4 & m5 & m6 & m7 &sp1 & ALLOC1 & STORE1 & LOAD & STORE2 & FREE1 & FREE2 & UNC & INJ).
      assert (UNC1: Mem.unchanged_on (fun b _ => b <> sp0) tm0 tm2).  
      { eapply Mem.unchanged_on_trans. eapply Mem.alloc_unchanged_on;eauto.
        econstructor.
        erewrite (Mem.support_store _ _ _ _ _ tm2);eauto.
        intros. split;intros. eapply Mem.perm_store_1. eauto. auto.
        eapply Mem.perm_store_2. eauto. auto.
        intros. exploit Mem.store_mem_contents.
        eapply STORE. intros. rewrite H4. simpl.
        unfold NMap.get.
        erewrite NMap.gso;eauto.        
      }
      
      (* final free in request *)
      assert (TM2FREE: Mem.range_perm tm2 sp0 0 4 Cur Freeable).
      { unfold Mem.range_perm. intros.
        eapply Mem.perm_store_1. eauto.
        exploit Mem.perm_alloc_2. eapply ALLOC. instantiate (1:= ofs).
        lia. eauto.
      } 
      assert (TMFREE: Mem.range_perm tm sp0 0 4 Cur Freeable).
      { unfold Mem.range_perm. intros.
        erewrite  <- Mem.unchanged_on_perm.
        eapply TM2FREE. auto. eauto. unfold loc_out_of_reach. intros.
        intro. eapply Mem.fresh_block_alloc. eapply ALLOC.
        eapply Mem.mi_mappedblocks. eapply Hm'1. eauto.
        auto.
        }
      
      assert ({m8 | Mem.free m7 sp0 0 4 = Some m8}).
      { eapply Mem.range_perm_free. unfold Mem.range_perm. intros.
        erewrite  <- Mem.unchanged_on_perm. eapply TMFREE. eauto. eauto.
        simpl. split. intro. congruence.
        intro. subst. exfalso. apply SPFRESH. eauto with mem.
        eapply Mem.unchanged_on_support;eauto. }
      destruct X as (m8 & FREE3).

      assert (UNC2: Mem.unchanged_on (fun b _ => b<>sp0) m7 m8).
      { eapply Mem.free_unchanged_on;eauto. }
      
      (* muliple step in the function of  process *)
      simpl. eexists.
      split.
      eapply plus_trans.
      instantiate (1:= (st L true (Returnstate Vundef Kstop m6) :: st L false (Call2 vf sb' tm') :: st L true (Callstate vf' args (Kcall None func_request (Maps.PTree.set i_id (sp0, Ctypesdefs.tint) empty_env) le (Kseq (Sreturn (Some (Evar i_id Ctypesdefs.tint))) Kstop)) tm'') :: nil) ).
      instantiate (1:= E0).
      exploit find_process';eauto. intros (rb' & INJP1 & FINDP1 & FINDP2).
      eapply exec_process_plus_false; eauto.
      eapply H14 in INJP1. eapply H22 in INJP1. rewrite FINJ in INJP1. inv INJP1. auto.
      (* final state in client *)
      econstructor. eapply step_pop.
      econstructor. econstructor.
      (* return 1 -> return 2 *)
      eapply star_step. econstructor. simpl. eapply step_asmret. eauto.
      (* final state in server *)
      eapply star_step. eapply step_pop. simpl.  econstructor. simpl. econstructor.
      (* returnstate in client *)
      eapply star_step. econstructor. simpl. econstructor.
      eapply star_step. econstructor. simpl. econstructor.
      eapply star_step. econstructor. simpl. econstructor.
      simpl. econstructor. econstructor.
      rewrite Maps.PTree.gss. reflexivity.
      econstructor. simpl. reflexivity. instantiate (1:= Vint i).
      {
        assert (VALIDtm1: Mem.valid_block tm1 sp0). eauto with mem.
        assert (VALIDtm: Mem.valid_block tm2 sp0).
        eapply Mem.store_valid_block_1; eauto.
        assert (VALIDtm0: Mem.valid_block tm sp0).
        inversion H21. apply unchanged_on_support; eauto.
        apply Mem.fresh_block_alloc in ALLOC as NONVALIDtm0.
        apply Mem.fresh_block_alloc in ALLOC1 as NONVALIDtm0sp1.
        assert (LOADtm: Mem.loadv Mint32 tm (Vptr sp0 Ptrofs.zero) = Some (Vint i)).
        apply Mem.load_store_same in STORE as LOAD1. simpl in *.
        erewrite Mem.load_unchanged_on_1; eauto.
        intros. red. intros. inv Hm'0.
        exploit mi_mappedblocks; eauto.
        assert (sp0 <> sp1). congruence.
        assert (sp0 <> sb'). congruence.
        assert (Mem.unchanged_on (fun b ofs => b = sp0) tm m7).
        eapply Mem.unchanged_on_trans. eapply Mem.alloc_unchanged_on; eauto.
        eapply Mem.unchanged_on_trans. eapply Mem.store_unchanged_on; eauto.
        eapply Mem.unchanged_on_trans. eapply Mem.store_unchanged_on; eauto.
        eapply Mem.unchanged_on_trans. eapply Mem.free_unchanged_on; eauto.
        eapply Mem.free_unchanged_on; eauto.
        simpl. simpl in LOADtm.
        erewrite Mem.load_unchanged_on_1; eauto.
        intros. simpl. reflexivity.
      }
      simpl. unfold Cop.sem_cast;simpl;destruct Archi.ptr64;eauto.
      (* free the argument block in request *)
      simpl.
      rewrite FREE3. eauto.
      (* final *)
      simpl. eapply star_refl.
      1-7:eauto.      

      (* match state: first prove m1~tm2 ~-> m'~m6  *)
      assert (INJP0: injp_acc (injpw j m tm Hm) (injpw j m'' m7 INJ)).
      eapply injp_acc_process_true. eapply H22. eapply H14. eauto.
      all: eauto.
      (* etransitivity. econstructor;eauto.
      instantiate (1:=Hm).
      eapply injp_acc_process. eapply H22. eapply H14. eapply FINDP3. 1-6: eauto.
       *)
      assert (INJP1: injp_acc (injpw f m1 tm2 Hm7) (injpw j m'' m7 INJ)).
      etransitivity. 2: eauto. constructor; eauto.
      inv INJP1.
      (* the reset match_state*)      
      (* m'~m' -> m6~m7*)      
      (* assert (ro_acc m' m'). eapply ro_acc_refl. *)
      (* assert (ro_acc m1 m1). eapply ro_acc_refl. *)
      assert (ro_acc m7 m8). eapply ro_acc_free;eauto.
      assert (ro_acc tm0 m8).
      eapply ro_acc_trans. eapply ro_acc_alloc;eauto.
      eapply ro_acc_trans. eapply ro_acc_store;eauto.
      eapply ro_acc_trans. instantiate (1:=m7). econstructor. auto. eapply Mem.unchanged_on_support.
      eauto. auto. auto.
      
      assert (INJ2: Mem.inject j m'' m8).
      eapply Mem.free_right_inject; eauto. intros.
      (* contradicte by j b1 = Some (sp,delta) , using the inject_separated*)
      (* f b1 = None *)
      destruct (f b1) eqn: FB.      
      destruct p0. eapply H22 in FB as FB1. rewrite FB1 in H4. inv H4.
      exploit Mem.mi_mappedblocks. eapply Hm0. eapply FB. intros.
      eapply Mem.fresh_block_alloc. eapply ALLOC. auto.
      eapply H23;eauto.
            
      inv H2. inv H3.
      econstructor.
      instantiate (1:= INJ2).
      (* (f0,m0,m2) ~-> (f,m1,tm1) *)
      etransitivity. instantiate (1:= injpw f m1 tm0 Hm0).      
      econstructor;eauto.
      (* prove (f,m1,tm0) ~-> (j,m',m7) *)
      (* unchanged_on tm0 m7 *)
      inv H29. inv UNC1. inv UNC2.
      econstructor;eauto.
      econstructor;eauto.
      (* perm *)
      intros.
      assert (b0 <> sp0). { intro. subst. eapply Mem.fresh_block_alloc. eapply ALLOC. auto. }      
      etransitivity.
      eapply unchanged_on_perm0;eauto.
      etransitivity. instantiate (1:= Mem.perm m7 b0 ofs k p).
      eapply unchanged_on_perm. auto. eapply Mem.store_valid_block_1;eauto.
      eapply Mem.valid_block_alloc;eauto.
      (* perm m6 m7 *)
      intros.  eapply unchanged_on_perm1;eauto. eapply unchanged_on_support.
      eapply Mem.store_valid_block_1;eauto.
      eapply Mem.valid_block_alloc;eauto.
      (* contents *)      
      intros.
      assert (b0 <> sp0). { intro. subst. eapply Mem.fresh_block_alloc. eapply ALLOC. eapply Mem.perm_valid_block. eauto. }      
      erewrite unchanged_on_contents1;eauto. erewrite unchanged_on_contents;eauto.
      eapply unchanged_on_perm0;eauto. eapply Mem.perm_valid_block. eauto.
      eapply unchanged_on_perm;eauto.
      eapply Mem.store_valid_block_1;eauto.
      eapply Mem.valid_block_alloc;eauto. eapply Mem.perm_valid_block;eauto.
      eapply unchanged_on_perm0;eauto. eapply Mem.perm_valid_block. eauto.

      (* inject_separated *)
      econstructor;eauto. eapply H23;eauto.
      intro. eapply Mem.valid_block_alloc in H33;eauto.
      eapply Mem.store_valid_block_1 in H33;eauto. eapply H31 in H29. destruct H29.
      congruence. auto.
    + (*encrypt1*)
      inv Hse. exploit find_process';eauto. intros (rb' & A & B & C).
      exploit find_keyid;eauto. intros (kb' & D & E).
      inv VINJ. inv INJP. eapply H15 in A as F.
      rewrite H4 in F. inv F.
      rewrite Ptrofs.add_zero_l. 
      exploit Mem.alloc_parallel_inject; eauto. instantiate (1:= 0). lia.
      instantiate (1:= 8). lia. intros (j' & tm' & tsp & ALLOC' & INJa & INJINCR & SPINJ & INJDIF).
      exploit Mem.store_mapped_inject; eauto.
      intros (tm'' & STORE' & INJ1).
    (* step *)
      eexists. split. econstructor. econstructor.
      simpl.  econstructor. eauto. eauto.

      exploit Mem.load_inject. apply INJa. eauto. eauto.
      intros (v2 & LOAD & INJL). rewrite Ptrofs.unsigned_zero in LOAD.
      simpl in LOAD. inv INJL. eauto. eauto.  simpl. eauto.
      (* at external *)
      eapply star_one. eapply step_push. econstructor. eapply find_process_server;eauto.
      (* valid query *)
      instantiate (1:= true). simpl. unfold Genv.is_internal. fold Ptrofs.zero.
      simpl in C. simpl. destruct Ptrofs.eq_dec;try congruence.
      rewrite C. auto.
      simpl.
      replace (intptr__void_sg) with (Ctypes.signature_of_type (Ctypes.Tcons
            tintp Ctypes.Tnil) Ctypes.Tvoid {| cc_vararg := None; cc_unproto := false; cc_structret := false |}) by auto.
      econstructor. eauto. auto. econstructor. econstructor.
      auto. econstructor.
      simpl. eapply Mem.sup_include_trans. eauto.
      eapply Mem.sup_include_trans.
      eapply Mem.unchanged_on_support. eauto.
      eapply Mem.sup_include_trans. red. intros.
      eapply Mem.valid_block_alloc; eauto.
      erewrite <- Mem.support_store; eauto.
      auto.

    (* match state *)
      econstructor. eauto. 2: eauto. rewrite INJDIF. eauto.
      intro. subst.
      apply Mem.fresh_block_alloc in ALLOC. inv Hm'0.
      apply mi_freeblocks in ALLOC. congruence.
      instantiate (1:= INJ1).
      etransitivity. instantiate (1:= injpw j m tm Hm'0).
      econstructor;eauto.
      etransitivity. instantiate (1:= injpw j' m' tm' INJa).
      eapply injp_acc_alloc; eauto.
      eapply injp_acc_store; eauto.
                        
    + (*encrypt2*)
      inv Hse. exploit find_process';eauto. intros (rb' & A & B & C).
      exploit find_keyid;eauto. intros (kb' & D & E).
      inv VINJ. inv INJP. inv INJP1. eapply H23 in A as F. eapply H15 in F as G.
      rewrite H4 in G. inv G.
      rewrite Ptrofs.add_zero_l. 
      exploit Mem.alloc_parallel_inject. apply Hm'0. eauto. instantiate (1:= 0). lia.
      instantiate (1:= 8). lia. rename tm' into tm'0.
      intros (j' & tm' & tsp & ALLOC' & INJa & INJINCR & SPINJ & INJDIF).
      exploit Mem.store_mapped_inject; eauto.
      intros (tm'' & STORE' & INJ1).
    (* step *)
      eexists. split. econstructor. econstructor.
      simpl.  econstructor. eauto. eauto.
      exploit Mem.load_inject. apply INJa. eauto. eauto.
      intros (v2 & LOAD & INJ2). rewrite Ptrofs.unsigned_zero in LOAD.
      simpl in LOAD. inv INJ2. eauto. eauto. simpl. eauto.
      (* at external *)
      eapply star_one. eapply step_push. econstructor. eapply find_process_server;eauto.
      (* valid query *)
      instantiate (1:= true). simpl. unfold Genv.is_internal. fold Ptrofs.zero.
      simpl in C. simpl. destruct Ptrofs.eq_dec;try congruence.
      rewrite C. auto.
      simpl.
      replace (intptr__void_sg) with (Ctypes.signature_of_type (Ctypes.Tcons
            tintp Ctypes.Tnil) Ctypes.Tvoid {| cc_vararg := None; cc_unproto := false; cc_structret := false |}) by auto.
      econstructor. eauto. auto. econstructor. econstructor.
      auto. econstructor.
      simpl. eapply Mem.sup_include_trans. eauto.
      eapply Mem.sup_include_trans. eapply Mem.unchanged_on_support;eauto.
      eapply Mem.sup_include_trans. eapply Mem.sup_include_incr.
      erewrite <- Mem.support_alloc. 2: eapply ALLOC0.
      eapply Mem.sup_include_trans. erewrite <- Mem.support_store. 2: eauto.
      eapply Mem.unchanged_on_support. eauto.
       eapply Mem.sup_include_trans. red. intros.
      eapply Mem.valid_block_alloc; eauto.
      erewrite <- Mem.support_store; eauto.
      auto.

    (* match state *)
      econstructor. eauto. 2: eauto. rewrite INJDIF. eapply H15. eauto.
      intro. subst.
      apply Mem.fresh_block_alloc in ALLOC. inv Hm'0.
      apply mi_freeblocks in ALLOC. congruence.
      3: eauto. 3: eauto. apply Mem.fresh_block_alloc in ALLOC'.
      intro. apply ALLOC'. inversion H14. eapply unchanged_on_support.
      erewrite Mem.support_store; eauto.
      instantiate (1:= Hm'3).
      econstructor; eauto.
      eauto. eauto.
      instantiate (1:= INJ1).
      instantiate (1:= Hm5).
      transitivity (injpw j m tm Hm'0).
      econstructor;eauto.
      transitivity (injpw j' m' tm' INJa).
      eapply injp_acc_alloc; eauto. eapply injp_acc_store; eauto.
      
    + (*request*)
      destruct (Mem.alloc tm 0 4) as [tm' sp] eqn: ALLOC.
      generalize (Mem.perm_alloc_2 _ _ _ _ _ ALLOC). intro PERMSP.
      apply Mem.fresh_block_alloc in ALLOC as FRESH.
      assert (STORE: {tm''| Mem.store Mint32 tm' sp (Ptrofs.unsigned Ptrofs.zero) (Vint input) = Some tm''}).
      apply Mem.valid_access_store.
      red. split. red. intros. rewrite Ptrofs.unsigned_zero in H. simpl in H.
      unfold Mptr in H. replace Archi.ptr64 with true in H by reflexivity. cbn in H.
      exploit PERMSP. instantiate (1:= ofs). lia. eauto with mem.
      unfold Mptr. replace Archi.ptr64 with true by reflexivity. simpl. rewrite Ptrofs.unsigned_zero.
      red. exists  0. lia. destruct STORE as [m2 STORE1].
      exploit Mem.alloc_right_inject; eauto. intro INJ1.
      exploit Mem.store_outside_inject; eauto. intros.
      inv INJP. inv Hm'0.  exploit mi_mappedblocks; eauto.
      intro INJ2.
      apply Mem.load_store_same in STORE1 as LOAD1. cbn in LOAD1.
      assert (UNC1 : Mem.unchanged_on (fun _ _ => True) tm tm').
      eapply Mem.alloc_unchanged_on; eauto.
      assert (UNC2: Mem.unchanged_on (fun b ofs => b <> sp) tm' m2).
      eapply Mem.store_unchanged_on; eauto.
      exploit (match_stbls_acc injp); eauto.
      intro MSTB. cbn in MSTB. inv MSTB.
      exploit find_encrypt'; eauto. intros [eb' [EBINJ [FINDE1 FINDE2]]].
      exploit find_process'; eauto. intros [pb' [PBINJ [FINDP1 FINDP2]]].
      exploit find_encrypt_1; eauto.
      cbn. eexists. split.
      econstructor.
      (*step1 function entry *)
      econstructor; eauto.
      simpl. constructor.
      instantiate (1:= func_request).
      eapply find_request; eauto.
      (*function_entry*)
      econstructor; simpl.
      constructor; eauto. constructor.
      econstructor; eauto.
      constructor.
      econstructor; eauto. rewrite Maps.PTree.gss. reflexivity.
      econstructor; cbn; eauto.
      econstructor; eauto. reflexivity.
      eapply star_step; eauto.
      (*step2 call*)
      econstructor; eauto.
      simpl. constructor.
      eapply star_step; eauto.
      eapply step_internal.
      econstructor. simpl. reflexivity.
      (*eval_expr*)
      instantiate (1:= Vptr eb' Ptrofs.zero).
      eapply eval_Elvalue.
      eapply eval_Evar_global. rewrite Maps.PTree.gso. reflexivity.
      unfold encrypt_id. unfold i_id. congruence.  eauto.
      eapply deref_loc_reference. eauto.
      (*eval_exprlist*)
      {
        econstructor. econstructor.
        eapply eval_Evar_local; eauto.
        rewrite Maps.PTree.gss. reflexivity.
        econstructor. cbn. reflexivity. eauto.
        cbn. reflexivity.
        econstructor; eauto.
        econstructor. eapply eval_Evar_global.
        rewrite Maps.PTree.gso. reflexivity.
        unfold process_id. unfold i_id. congruence.  eauto.
        eapply deref_loc_reference. eauto. reflexivity.
        econstructor.
      }
      eauto. cbn. reflexivity.
      (*step3 : at_external *)
      eapply star_one. eapply step_push; eauto.
      econstructor; eauto. instantiate (1:= false).
      cbn. unfold Genv.is_internal. rewrite FINDE2. reflexivity.
      constructor; eauto. traceEq.
      simpl.
      (*ms*)
      inv INJP. simpl.
      econstructor. eauto. instantiate (1:= Hm'0).
      econstructor; eauto. eauto. eauto.
      instantiate (1:= INJ2). instantiate (1:= INJ2).
      reflexivity.
  - constructor. intros. inv H.
Qed.
