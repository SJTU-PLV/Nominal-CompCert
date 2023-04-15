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
                  | Some 3%positive | Some  1%positive | Some 6%positive => true
                  (* => (id =? process_id)%positive || (id =? encrypt_id)%positive ||
                                (id =? request_id)%positive *)
                  | _ => false
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
|step_request input pb m eb
   (FINDP: Genv.find_symbol se process_id = Some pb)
   (FINDE: Genv.find_symbol se encrypt_id = Some eb):
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

Let tge1 := Clight.globalenv tse client.
Let tge2 := Genv.globalenv tse b1.

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

Inductive match_state : state -> list (frame L) -> Prop :=
|match_return_introc (j:meminj) m tm
  (Hm: Mem.inject j m tm)
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state (Return m) (st L true (Returnstate Vundef Kstop tm) :: nil) 
|match_return_intros (j:meminj) m tm
  (Hm: Mem.inject j m tm)
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state (Return m) ((st L false (Return2 tm)) :: nil)
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
  match_state  (Callencrypt input v m)
    ((st L false (Call1 tv input tm)) ::nil)
|match_encrypt_intro2 (j:meminj) m tm tm' input vf args cont v tv
   (Hm: Mem.inject j m tm)
  (*(FINDP : Genv.find_symbol se process_id = Some pb)
  (FINJ: j pb = Some (pb',0)) *)
  (VINJ: Val.inject j v tv)
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state  (Callencrypt input v m)
    ((st L false (Call1 tv input tm)) ::
       (st L true (Callstate vf args cont tm')) ::nil)
|match_process_intro1 (j:meminj) m tm output pb pb'
  (Hm: Mem.inject j m tm)
  (FINDP : Genv.find_symbol se process_id = Some pb)
  (FINJ: j pb = Some (pb',0))
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state (Callprocess output m)
    ((st L true(Callstate (Vptr pb' Ptrofs.zero) (Vint output :: nil) Kstop tm)):: nil)
|match_process_intro2 (j:meminj) m tm  pb pb' vf output output' tm'
  (Hm: Mem.inject j m tm)
  (FINDP : Genv.find_symbol se process_id = Some pb)
  (FINJ: j pb = Some (pb',0))
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state (Callprocess output m)
    ((st L true(Callstate (Vptr pb' Ptrofs.zero) (Vint output :: nil) Kstop tm)) ::
       (st L false (Call2 vf output' tm')) :: nil)
|match_process_intro3 (j:meminj) m tm  pb pb' vf output output' tm' vf' args tm''
  (Hm: Mem.inject j m tm)
  (FINDP : Genv.find_symbol se process_id = Some pb)
  (FINJ: j pb = Some (pb',0))
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state (Callprocess output m)
    ((st L true(Callstate (Vptr pb' Ptrofs.zero) (Vint output :: nil) Kstop tm)) ::
       (st L false (Call2 vf output' tm')) ::
        (st L true (Callstate vf' args Kstop tm'')) :: nil).

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
    Genv.find_funct tge2 (Vptr rb' Ptrofs.zero) = Some (Internal func_encrypt_b1).
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
    Genv.find_funct tge2 (Vptr rb' Ptrofs.zero) = Some (Internal func_encrypt_b1).
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


Lemma find_result':
  forall rb j,
    Genv.match_stbls j se tse ->
    Genv.find_symbol se result_id = Some rb ->
    exists rb', j rb = Some (rb', 0) /\ Genv.find_symbol tge2 result_id = Some rb'.
Proof.
  intros. eapply Genv.find_symbol_match in H as F;eauto. 
Qed.


End MS.


Lemma maxv:
  Ptrofs.max_unsigned = 18446744073709551615.
Proof.
  unfold Ptrofs.max_unsigned. unfold Ptrofs.modulus. unfold Ptrofs.wordsize.
  unfold two_power_nat. unfold Wordsize_Ptrofs.wordsize.
  replace Archi.ptr64 with true by reflexivity. reflexivity.
Qed.



Lemma exec_process_mem:
  forall stb tb sm sm1 m output j,
    Mem.storev Mint32 sm (Vptr stb Ptrofs.zero) (Vint output) = Some sm1 ->
    Mem.inject j sm m ->
    j stb = Some (tb,0) ->
    exists m1 m2 m3 m4 sp,
      Mem.alloc m 0 4 = (m1, sp) /\
        Mem.storev Mint32 m1 (Vptr sp Ptrofs.zero) (Vint output) = Some m2 /\
        Mem.storev Mint32 m2 (Vptr tb Ptrofs.zero) (Vint output) = Some m3 /\
        Mem.free m3 sp 0 4 = Some m4 /\
        Mem.unchanged_on (fun b ofs => b = tb -> ~ 0 <= ofs < 4) m m4 /\
        Mem.inject j sm1 m4.
Proof.
  intros.
  destruct (Mem.alloc m 0 4) as [tm' sp] eqn: ALLOC.
  generalize (Mem.perm_alloc_2 _ _ _ _ _ ALLOC). intro PERMSP.
  apply Mem.fresh_block_alloc in ALLOC as FRESH.
  (* store varibale *)
  assert (STORE: {tm''| Mem.store Mint32 tm' sp (Ptrofs.unsigned Ptrofs.zero) (Vint output) = Some tm''}).
  apply Mem.valid_access_store.
  red. split. red. intros. rewrite Ptrofs.unsigned_zero in H2. simpl in H2.
  exploit PERMSP. instantiate (1:= ofs). lia. eauto with mem.
  red. exists  0. rewrite Ptrofs.unsigned_zero. lia. destruct STORE as [m2 STORE1].
  (* store val *)
  
  assert (STORE: {m3 | Mem.store Mint32 m2 tb (Ptrofs.unsigned (Ptrofs.repr 0)) (Vint output)  = Some m3}).
  apply Mem.valid_access_store.
  red. split. red. intros. rewrite Ptrofs.unsigned_repr in H2. simpl in H2.  
  eapply Mem.store_valid_access_1. eauto.
  eapply Mem.valid_access_alloc_other. eauto.
  eapply Mem.valid_access_inject;eauto.
  eapply Mem.store_valid_access_3;eauto.
  rewrite Ptrofs.unsigned_zero. simpl. auto.
  rewrite maxv. lia.
  rewrite Ptrofs.unsigned_repr. simpl. eapply Z.divide_0_r.
  rewrite maxv. lia.
  destruct STORE as ( m3 & STORE2).

  (* free *) 
  assert (FREE:{m4 | Mem.free m3 sp 0 4 = Some m4}).
  eapply Mem.range_perm_free.
  unfold Mem.range_perm. intros.
  eapply Mem.perm_store_1. eauto.
  eapply Mem.perm_store_1. eauto.
  eapply Mem.perm_alloc_2. eauto. auto.
  destruct FREE as [m4  FREE].

  (* inject j sm1 m4 *)
  exploit Mem.alloc_right_inject; eauto. intro INJ1.
  exploit Mem.store_outside_inject; eauto. intros.
  eapply FRESH. eapply Mem.mi_mappedblocks;eauto.
  intros INJ2.

  exploit Mem.store_mapped_inject;eauto.
  intros (n2 & STORE3 & INJ3). rewrite Ptrofs.unsigned_zero in STORE3.
  rewrite Ptrofs.unsigned_repr in STORE2.
  simpl in STORE3. rewrite STORE2 in STORE3. inversion STORE3. rewrite <- H3 in *.
  clear H3.
  exploit Mem.free_right_inject;eauto. intros.
  eapply FRESH. eapply Mem.mi_mappedblocks;eauto.
  intros INJ4.
  2: rewrite maxv;lia.

  exists tm',m2,m3,m4,sp.

  split;auto. split;auto.
  split;auto. split;auto.
  split;auto. 
  
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


Lemma exec_process_plus:
  forall se2 fb lf m m1 m2 m3 m4 output sp tb,
    Genv.find_symbol se2 result_id = Some tb ->
    Genv.find_funct (Clight.globalenv se2 client) (Vptr fb Ptrofs.zero) = Some (Ctypes.Internal func_process) ->
    Mem.alloc m 0 4 = (m1, sp) ->
    Mem.storev Mint32 m1 (Vptr sp Ptrofs.zero) (Vint output) = Some m2 ->
    Mem.storev Mint32 m2 (Vptr tb Ptrofs.zero) (Vint output) = Some m3 ->
    Mem.free m3 sp 0 4 = Some m4 ->          
    plus (fun _ : unit => SmallstepLinking.step L se2) tt
      (st L true (Callstate (Vptr fb Ptrofs.zero) (Vint output :: nil) Kstop m) :: lf) E0
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
  eapply eval_Evar_global.
  auto.
  instantiate (1 := tb).
  simpl. eauto.
  econstructor. econstructor.
  erewrite Maps.PTree.gss. eauto.
  econstructor.
  econstructor.
  eapply Mem.load_store_same;eauto.
  simpl. unfold Cop.sem_cast;simpl;destruct Archi.ptr64;eauto.
  simpl. econstructor. simpl. eauto.
  eauto.
  (* step skip *)
  eapply star_step.
  econstructor. econstructor.
  (* step return *)
  eapply star_step.
  econstructor. econstructor.
  simpl.
  (* prove free sp success *)
  rewrite H4. eauto.
  
  (* star refl *)
  eapply star_refl.
  1-5: eauto.
Qed.


Lemma injp_acc_process:
  forall j m tm m' m3 sp output m4 m5 m6 tb b Hm0 Hm1,
    (* Mem.valid_block m1 b -> *)
    j b = Some (tb,0) ->
    Mem.storev Mint32 m (Vptr b Ptrofs.zero) (Vint output) = Some m' ->
    Mem.alloc tm 0 4 = (m3, sp) ->
    Mem.storev Mint32 m3 (Vptr sp Ptrofs.zero) (Vint output) = Some m4 ->
    Mem.storev Mint32 m4 (Vptr tb Ptrofs.zero) (Vint output) = Some m5 ->
    Mem.free m5 sp 0 4 = Some m6 ->
    Mem.unchanged_on (fun (b : block) (ofs : Z) => b = tb -> ~ 0 <= ofs < 4) tm m6 ->
    injp_acc (injpw j m tm Hm0) (injpw j m' m6 Hm1).
Proof.
  intros j  m tm m' m3 sp output m4 m5 m6 tb b Hm0 Hm1.
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
  econstructor;congruence.
Qed.


  
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

         assert (FIND_DEF_SERVER: forall f, Genv.find_def (Genv.globalenv se2 Server.b1) b2 <> Some (Gfun f)).
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
         
  - intros q1 q2 s1 Hq Hi1. inv Hq. inv H1. inv Hi1; cbn in *.
    + (*process*)
      inv Hse.
      eapply Genv.find_symbol_match in H5 as FIND'; eauto.
      destruct FIND' as [fb' [FINJ FIND']]. inv H.
      inv H0. inv H7. inv H3.
      rewrite FINJ in H4. inv H4. rename b2 into fb'. rewrite Ptrofs.add_zero.
      exploit find_process; eauto. intro FINDP.
      exists ((st L true (Callstate (Vptr fb' Ptrofs.zero) (Vint output :: nil) Kstop m2)) :: nil).
      split. split.
      -- simpl. unfold Genv.is_internal.
         setoid_rewrite find_process; eauto.
      -- simpl.
       set (targs := (Ctypes.Tcons
            (Ctypes.Tint Ctypes.I32 Ctypes.Signed
                         {| Ctypes.attr_volatile := false; Ctypes.attr_alignas := None |}) Ctypes.Tnil)).
       assert (Ctypes.signature_of_type targs Ctypes.Tvoid cc_default = int__void_sg).
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
    + (*requese*)
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
       set (targs := (Ctypes.Tcons
            (Ctypes.Tint Ctypes.I32 Ctypes.Signed
                         {| Ctypes.attr_volatile := false; Ctypes.attr_alignas := None |}) Ctypes.Tnil)).
       assert (Ctypes.signature_of_type targs Ctypes.Tvoid cc_default = int__void_sg).
       reflexivity.
       rewrite <- H.
       econstructor; eauto.
       constructor; cbn; eauto. constructor; eauto. constructor.
      -- econstructor; eauto. reflexivity.
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
    intros. inv H; inv H0.
    
    + (*process1*)
      inv Hse. inv INJP.            
      exploit (Genv.find_symbol_match H). eapply FIND.
      intros (tb & FINDP3 & FINDSYMB).
      exploit exec_process_mem;eauto. intros (m3 & m4 & m5 & m6 & sp & ALLOC & STORE1 & STORE2 & FREE1 & UNC & INJ).

      (* muliple step in the function of  process *)
      simpl. exists (st L true (Returnstate Vundef Kstop m6) :: nil).      
      split.
      exploit find_process';eauto. intros (rb' & INJP1 & FINDP1 & FINDP2).     
      eapply exec_process_plus;eauto.      
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

      exploit exec_process_mem;eauto. intros (m3 & m4 & m5 & m6 & sp & ALLOC & STORE1 & STORE2 & FREE1 & UNC & INJ).
      (* muliple step in the function of  process *)
      simpl. eexists.
      split.
      eapply plus_trans.
      instantiate (1:= (st L true (Returnstate Vundef Kstop m6) :: st L false (Call2 vf output' tm') :: nil)).
      instantiate (1:= E0).
      exploit find_process';eauto. intros (rb' & INJP1 & FINDP1 & FINDP2).     
      eapply exec_process_plus;eauto.
      eapply H14 in INJP1. rewrite FINJ in INJP1. inv INJP1. auto.
      (* final state in client *)
      econstructor. eapply step_pop.
      econstructor. econstructor.
      (* return 1 -> return 2 *)
      eapply star_step. econstructor. simpl. eapply step_asmret.
      eapply star_refl.
      1-3:eauto.

      (* match state *)
      econstructor.
      etransitivity. econstructor;eauto.
      instantiate (1:= INJ). instantiate (1:=Hm'0).
      eapply injp_acc_process. eapply H14. eapply FINDP3. 1-6: eauto.

    + (*process3*)
      inv Hse. inv INJP.            
      exploit (Genv.find_symbol_match H). eapply FIND.
      intros (tb & FINDP3 & FINDSYMB).

      exploit exec_process_mem;eauto. intros (m3 & m4 & m5 & m6 & sp & ALLOC & STORE1 & STORE2 & FREE1 & UNC & INJ).
      (* muliple step in the function of  process *)
      simpl. eexists.
      split.
      eapply plus_trans.
      instantiate (1:= (st L true (Returnstate Vundef Kstop m6) :: st L false (Call2 vf output' tm') :: st L true (Callstate vf' args Kstop tm'') :: nil) ).
      instantiate (1:= E0).
      exploit find_process';eauto. intros (rb' & INJP1 & FINDP1 & FINDP2).     
      eapply exec_process_plus;eauto.
      eapply H14 in INJP1. rewrite FINJ in INJP1. inv INJP1. auto.
      (* final state in client *)
      econstructor. eapply step_pop.
      econstructor. econstructor.
      (* return 1 -> return 2 *)
      eapply star_step. econstructor. simpl. eapply step_asmret.
      (* final state in server *)
      eapply star_step. eapply step_pop. simpl.  econstructor. simpl. econstructor.
      eapply star_refl.
      1-4:eauto.      

      (* match state *)
      econstructor.
      etransitivity. econstructor;eauto.
      instantiate (1:= INJ). instantiate (1:=Hm'0).
      eapply injp_acc_process. eapply H14. eapply FINDP3. 1-6: eauto.

    + (*encrypt1*)
      admit.
    + (*encrypt2*)
      admit.
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
      (*ms*)
      econstructor; eauto.
      etransitivity. eauto.
      instantiate (1:= INJ2).
      assert (ro_acc tm m2).
      eapply ro_acc_trans. eapply ro_acc_alloc; eauto.
      eapply ro_acc_store; eauto.
      inv H0.
      constructor; eauto.
      -- red. intros. eauto.
      -- eapply Mem.unchanged_on_refl.
      -- inv UNC1. inv UNC2. constructor.
      eauto with mem.
      intros. etransitivity. eauto. apply unchanged_on_perm0.
      intro. subst. congruence. eauto with mem.
      intros. etransitivity. apply unchanged_on_contents0.
      intro. subst. apply Mem.perm_valid_block in H7. congruence. eauto with mem.
      eauto.
      -- red. intros. congruence.
  - constructor. intros. inv H.
Admitted.


