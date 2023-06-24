Require Import Integers Values Memory.
Require Import Clight.
Require Import InjectFootprint Invariant ValueAnalysis.
Require Import CA Asm CallConv CKLRAlgebra.
Require Import ClientMR Server Serverspec.
Require Import Smallstep Linking SmallstepLinking.
Require Import LanguageInterface.
(** * C-level composed specification *)

Definition result_def_unit :=
  {|
    gvar_info := tt;
    gvar_init := nil;
    gvar_readonly := false;
    gvar_volatile := false |}.

Definition input_index_def_unit :=
  {|
    gvar_info := tt;
    gvar_init := nil;
    gvar_readonly := false;
    gvar_volatile := false |}.


Definition linked_skel1 : program unit unit:=
  {|
    prog_defs := (result_id, Gvar result_def_unit) :: (key_id, Gvar key_def) ::
                   (input_id, Gvar input_index_def_unit) ::
                   (encrypt_id, Gfun tt) :: (request_id, Gfun tt) ::
                   (index_id, Gvar input_index_def_unit) :: nil;
    prog_public := encrypt_id :: request_id :: input_id :: result_id :: index_id ::
                     key_id :: encrypt_id :: complete_id :: nil;
    prog_main := 42%positive
  |}.

Section WITH_N.

Variable N: Z.  
Hypothesis bound_N: 0 < N < Int.max_signed. 


Let client := client N.
Let func_request := func_request N.

Theorem link_ok1 :
  link (skel (Clight.semantics1 client)) (skel L1) = Some linked_skel1.
Proof. reflexivity. Qed.

Definition L := fun i : bool => if i then (Clight.semantics1 client) else L1.
Definition composed_spec1 := semantics L linked_skel1.

Theorem link_result :
  compose (Clight.semantics1 client) L1 = Some composed_spec1.
Proof.
  unfold compose. rewrite link_ok1. simpl. reflexivity.
Qed.


(** * C-level top specification *)

Inductive state : Type :=
| Callrequest (input : int) (m:mem)
| Callencrypt (input : int) (fptr : val) (m:mem)
| Return (m:mem).

Definition genv := Genv.t unit unit.

Section WITH_SE.
Context (se:Genv.symtbl).

Inductive initial_state : query li_c ->  state -> Prop :=
|initial_request output m fb
   (FIND: Genv.find_symbol se request_id = Some fb):
  initial_state (cq (Vptr fb Ptrofs.zero) int__void_sg ((Vint output) :: nil) m)
    (Callrequest output m)
|initial_encrypt i fb b ofs m
   (FIND: Genv.find_symbol se encrypt_id = Some fb):
  initial_state (cq (Vptr fb Ptrofs.zero) int_fptr__void_sg ((Vint i) :: (Vptr b ofs) :: nil) m)
    (Callencrypt i (Vptr b ofs) m).

Inductive at_external : state -> query li_c -> Prop :=.
Inductive after_external : state -> c_reply -> state -> Prop := .

Inductive final_state : state -> reply li_c -> Prop :=
|final_process m:
  final_state (Return m) (cr Vundef m).

Definition valid_query (q: query li_c) : bool :=
  match (cq_vf q) with
  |Vptr b ofs =>  if Ptrofs.eq_dec ofs Ptrofs.zero then
                  match Genv.invert_symbol se b with
                  | Some 3%positive | Some  1%positive => true
                  | _ => false
                  end
                  else false
  |_  => false
  end.

Definition Nint := (Int.repr N).

Inductive step : state -> trace -> state -> Prop :=
| step_request1 r input rb idb inb eb idx m m'
  (FINDIDX: Genv.find_symbol se index_id = Some idb)
  (FINDREQ: Genv.find_symbol se request_id = Some rb)
  (FINDINPUT: Genv.find_symbol se input_id = Some inb)
  (FINDE: Genv.find_symbol se encrypt_id = Some eb)
  (READIDX: Mem.loadv Mint32 m (Vptr idb Ptrofs.zero) = Some (Vint idx))
  (COND: Int.eq idx Int.zero = true)
  (ADDIDX: Mem.storev Mint32 m (Vptr idb Ptrofs.zero) (Vint (Int.add idx Int.one)) = Some m')
  (READINPUT: Mem.loadv Mint32 m' (Vptr inb (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints idx))) = Some (Vint input)):
  step (Callrequest r m) E0 (Callencrypt input (Vptr rb Ptrofs.zero) m')
| step_request2 r input rb idb inb rsb eb idx m m' m''
  (FINDIDX: Genv.find_symbol se index_id = Some idb)
  (FINDREQ: Genv.find_symbol se request_id = Some rb)
  (FINDINPUT: Genv.find_symbol se input_id = Some inb)
  (FINDRES: Genv.find_symbol se result_id = Some rsb)
  (FINDE: Genv.find_symbol se encrypt_id = Some eb)
  (READIDX: Mem.loadv Mint32 m (Vptr idb Ptrofs.zero) = Some (Vint idx))
  (COND: Int.lt Int.zero idx && Int.lt idx Nint = true)
  (STORERES: Mem.storev Mint32 m (Vptr rsb (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.sub idx (Int.repr 1))))) (Vint r) = Some m')
  (ADDIDX: Mem.storev Mint32 m' (Vptr idb Ptrofs.zero) (Vint (Int.add idx Int.one)) = Some m'')
  (* 4 * (index - 1) *)
  (READINPUT: Mem.loadv Mint32 m'' (Vptr inb (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints idx))) = Some (Vint input)):
  step (Callrequest r m) E0 (Callencrypt input (Vptr rb Ptrofs.zero) m'')
| step_request3 r idb rsb idx m m'
  (FINDIDX: Genv.find_symbol se index_id = Some idb)
  (FINDRES: Genv.find_symbol se result_id = Some rsb)
  (READIDX: Mem.loadv Mint32 m (Vptr idb Ptrofs.zero) = Some (Vint idx))
  (COND: Int.cmp Cge idx Nint = true)
  (STORERES: Mem.storev Mint32 m (Vptr rsb (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.sub idx (Int.repr 1))))) (Vint r) = Some m'):
  step (Callrequest r m) E0 (Return m')
| step_encrypt kb rb key input m output
   (FINDK: Genv.find_symbol se key_id = Some kb)
   (FINDP: Genv.find_symbol se request_id = Some rb)
   (READ: Mem.loadv Mint32 m (Vptr kb Ptrofs.zero) = Some (Vint key))
   (XOR: output = Int.xor input key):
  step (Callencrypt input (Vptr rb Ptrofs.zero) m) E0 (Callrequest output m).

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

Inductive stack_acc (w: injp_world) : injp_world -> list block -> Prop :=
| stack_acc_nil w':
  injp_acc w w' ->
  stack_acc w w' nil
| stack_acc_cons f1 m1 tm1 w1 (Hm1: Mem.inject f1 m1 tm1) lsp tm1' sp Hm1' w2
    (Hm1: Mem.inject f1 m1 tm1)
    (WORLD1: w1 = injpw f1 m1 tm1 Hm1)
    (STKB: stack_acc w w1 lsp)
    (INJP1: injp_acc w w1)
    (ALLOC: Mem.alloc tm1 0 4 = (tm1', sp))
    (INJP2: injp_acc (injpw f1 m1 tm1' Hm1') w2):
  stack_acc w w2 (sp::lsp).
  


Inductive match_kframe_request: list block -> list (frame L) -> Prop :=
| match_kframe_request_nil:
  match_kframe_request nil nil
| match_kframe_request_cons output m fb k lsp:
  match_kframe_encrypt lsp k ->
  match_kframe_request lsp ((st L false (Call2 fb output m)) :: k)
                       
with match_kframe_encrypt : list block -> list (frame L) -> Prop :=
| match_kframe_encrypt_nil:
  match_kframe_encrypt nil nil
| match_kframe_encrypt_cons m fb vargs k sp le lsp:
  match_kframe_request lsp k ->
  match_kframe_encrypt (sp::lsp) (st L true (Callstate fb vargs (Kcall None func_request (Maps.PTree.set r_id (sp, Ctypesdefs.tint) empty_env) le Kstop) m) :: k).

  
  

Inductive match_state: state -> list (frame L) -> Prop :=
| match_request_intro j r rb rb' m tm ks w1 lsp
    (Hm: Mem.inject j m tm)
    (KINJP: stack_acc w w1 lsp)
    (INJP: injp_acc w1 (injpw j m tm Hm))
    (FINDP: Genv.find_symbol se request_id = Some rb)
    (FINJ: j rb = Some (rb',0))
    (KFRM: match_kframe_request lsp ks):
  match_state (Callrequest r m) ((st L true (Callstate (Vptr rb' Ptrofs.zero) (Vint r :: nil) Kstop tm)) :: ks)
| match_encrypt_intro j v tv m tm input ks w1 lsp
    (Hm: Mem.inject j m tm)
    (KINJP: stack_acc w w1 lsp)
    (INJP: injp_acc w1 (injpw j m tm Hm))
    (VINJ: Val.inject j v tv)
    (KFRM: match_kframe_encrypt lsp ks):
  match_state (Callencrypt input v m) ((st L false (Call1 tv input tm)) :: ks)
| match_return_introc j m tm
  (Hm: Mem.inject j m tm)
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state (Return m) (st L true (Returnstate Vundef Kstop tm) :: nil)
|match_return_intros j m tm
  (Hm: Mem.inject j m tm)
  (INJP : injp_acc w (injpw j m tm Hm)):
  match_state (Return m) ((st L false (Return2 tm)) :: nil).

Lemma find_request:
  forall rb rb' j,
    Genv.match_stbls j se tse ->
    Genv.find_symbol se request_id = Some rb ->
    j rb = Some (rb',0) ->
    Genv.find_funct tge1 (Vptr rb' Ptrofs.zero) = Some (Ctypes.Internal func_request).
Proof.
Admitted.

Lemma find_encrypt:
  forall rb rb' j,
    Genv.match_stbls j se tse ->
    Genv.find_symbol se encrypt_id = Some rb ->
    j rb = Some (rb',0) ->
    Genv.find_funct tge2 (Vptr rb' Ptrofs.zero) = Some (Internal func_encrypt_b1).
Proof.
Admitted.

Lemma find_encrypt_1:
  forall rb rb' j,
    Genv.match_stbls j se tse ->
    Genv.find_symbol se encrypt_id = Some rb ->
    j rb = Some (rb',0) ->
    Genv.find_funct tge1 (Vptr rb' Ptrofs.zero) = Some (func_encrypt_external).
Admitted.

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

End MS.


Lemma stack_acc_injp_acc: forall w1 w2 lsp,
    stack_acc w1 w2 lsp ->
    injp_acc w1 w2.
Proof.
  intros. induction H.
  auto.
  etransitivity. eapply IHstack_acc.
  etransitivity. 2: eapply INJP2.
  subst.
  assert (ro_acc m1 m1). eapply ro_acc_refl.
  assert (ro_acc tm1 tm1'). eapply ro_acc_alloc;eauto.
  inv H0. inv H1.
  econstructor; eauto.
  eapply Mem.unchanged_on_refl.
  eapply Mem.alloc_unchanged_on;eauto.
  eapply inject_separated_refl.
Qed.

Lemma stack_acc_compose_injp_acc: forall w1 w2 w3 lsp,
    stack_acc w1 w2 lsp ->
    injp_acc w2 w3 ->
    stack_acc w1 w3 lsp.
Proof.
  intros.
  inv H. econstructor. etransitivity;eauto.
  econstructor;eauto. etransitivity;eauto.
Qed.


Lemma maxv:
  Ptrofs.max_unsigned = 18446744073709551615.
Proof.
  unfold Ptrofs.max_unsigned. unfold Ptrofs.modulus. unfold Ptrofs.wordsize.
  unfold two_power_nat. unfold Wordsize_Ptrofs.wordsize.
  replace Archi.ptr64 with true by reflexivity. reflexivity.
Qed.

Lemma sem_cast_int_int: forall v m,
    Cop.sem_cast (Vint v) Ctypesdefs.tint Ctypesdefs.tint m = Some (Vint v).
Proof.
  intros.
  unfold Cop.sem_cast. simpl.
  destruct Archi.ptr64. simpl. auto.
  destruct Ctypes.intsize_eq;try congruence.
Qed.

Lemma sem_cmp_int_int: forall v1 v2 m c,
    Cop.sem_cmp c (Vint v1) Ctypesdefs.tint (Vint v2) Ctypesdefs.tint m = Some (Val.of_bool (Int.cmp c v1 v2)).
Proof.
  intros. unfold Cop.sem_cmp. simpl.
  unfold Cop.sem_binarith. simpl. repeat rewrite sem_cast_int_int.
  auto.
Qed.

Lemma int_one_not_eq_zero:
  Int.eq Int.one Int.zero = false.
  destruct (Int.eq Int.one Int.zero) eqn:EQ. exfalso.
  eapply Int.one_not_zero. exploit Int.eq_spec. rewrite EQ.
  auto. auto.
Qed.

Lemma ge_N_not_zero: forall idx,
  Int.cmp Cge idx Nint = true ->
  Int.eq idx Int.zero = false.
Admitted.


(* idx == 0 *)
Lemma exec_request_mem1:
  forall ib tib sm sm1 tm idx idx' output j inb ofs input tinb,
    Mem.loadv Mint32 sm (Vptr ib Ptrofs.zero) = Some (Vint idx) ->
    Mem.storev Mint32 sm (Vptr ib Ptrofs.zero) (Vint idx') = Some sm1 ->
    Mem.loadv Mint32 sm1 (Vptr inb ofs) = Some (Vint input) ->
    Mem.inject j sm tm ->
    j ib = Some (tib,0) ->
    exists tm1 tm2 tm3 sp,
      Mem.alloc tm 0 4 = (tm1, sp) /\
        Mem.storev Mint32 tm1 (Vptr sp Ptrofs.zero) (Vint output) = Some tm2 /\
        Mem.storev Mint32 tm2 (Vptr tib Ptrofs.zero) (Vint idx') = Some tm3 /\
        Mem.loadv Mint32  tm2 (Vptr tib Ptrofs.zero) = Some (Vint idx) /\
        Mem.loadv Mint32  tm3 (Vptr tib Ptrofs.zero) = Some (Vint idx') /\
        Mem.loadv Mint32 tm3 (Vptr tinb ofs) = Some (Vint input) /\
        Mem.unchanged_on (fun b ofs => b = tib -> ~ 0 <= ofs < 4) tm tm3 /\
        Mem.inject j sm1 tm3.
Admitted.

(* 0 < index < N *)
Lemma exec_request_mem2:
  forall ib tib sm sm1 sm2 tm idx idx' idx'' output j r ofs1 ofs2 inb tinb input resb tresb,
    Mem.loadv Mint32 sm (Vptr ib Ptrofs.zero) = Some (Vint idx) ->
    Mem.storev Mint32 sm (Vptr resb ofs1) (Vint r) = Some sm1 ->
    Mem.loadv Mint32 sm1 (Vptr ib Ptrofs.zero) = Some (Vint idx') ->
    Mem.storev Mint32 sm1 (Vptr ib Ptrofs.zero) (Vint idx'') = Some sm2 ->
    Mem.loadv Mint32 sm2 (Vptr inb ofs2) = Some (Vint input) ->
    Mem.inject j sm tm ->
    j ib = Some (tib,0) ->
    j inb = Some (tinb,0) ->
    j resb = Some (tresb,0) ->
    exists tm1 tm2 tm3 tm4 sp,
      Mem.alloc tm 0 4 = (tm1, sp) /\
        Mem.storev Mint32 tm1 (Vptr sp Ptrofs.zero) (Vint output) = Some tm2 /\
        Mem.loadv Mint32  tm2 (Vptr tib Ptrofs.zero) = Some (Vint idx) /\
        Mem.loadv Mint32 tm2 (Vptr sp Ptrofs.zero) = Some (Vint r) /\
        Mem.storev Mint32 tm2 (Vptr tresb ofs1) (Vint r) = Some tm3 /\
        Mem.loadv Mint32 tm3 (Vptr tib Ptrofs.zero) = Some (Vint idx') /\
        Mem.storev Mint32 tm3 (Vptr tib Ptrofs.zero) (Vint idx'') = Some tm4 /\
        Mem.loadv Mint32 tm4 (Vptr inb ofs2) = Some (Vint input) /\
        Mem.unchanged_on (fun b ofs => (b = tib -> ~ 0 <= ofs < 4) /\ (b = tresb -> ~ (Ptrofs.signed ofs1) <= ofs < (Ptrofs.signed ofs1) + 4)) tm tm4 /\
        Mem.inject j sm2 tm4.
Admitted.

(* idnex >= N *)
Lemma exec_request_mem3:
  forall ib tib sm sm1 tm idx r j ofs1 resb tresb Hm0,
    Mem.loadv Mint32 sm (Vptr ib Ptrofs.zero) = Some (Vint idx) ->
    Mem.storev Mint32 sm (Vptr resb ofs1) (Vint r) = Some sm1 ->
    j ib = Some (tib,0) ->
    j resb = Some (tresb,0) ->
    exists tm1 tm2 tm3 tm4 sp Hm1,
      Mem.alloc tm 0 4 = (tm1, sp) /\
        Mem.storev Mint32 tm1 (Vptr sp Ptrofs.zero) (Vint r) = Some tm2 /\
        Mem.loadv Mint32  tm2 (Vptr tib Ptrofs.zero) = Some (Vint idx) /\
        Mem.loadv Mint32 tm2 (Vptr sp Ptrofs.zero) = Some (Vint r) /\
        Mem.storev Mint32 tm2 (Vptr tresb ofs1) (Vint r) = Some tm3 /\
        Mem.free tm3 sp 0 4 = Some tm4 /\
        (* Mem.unchanged_on (fun b ofs => b = tresb -> ~ (Ptrofs.signed ofs1) <= ofs < (Ptrofs.signed ofs1 + 4)) tm tm4 /\ *)
        injp_acc (injpw j sm tm Hm0) (injpw j sm1 tm4 Hm1).
Admitted.

Lemma exec_kframe: forall lsp w1 w2 m tm j Hm  ks se,
    stack_acc w1 w2 lsp ->
    injp_acc w2 (injpw j m tm Hm) ->
    match_kframe_request lsp ks ->
    exists tm' Hm' s,
      injp_acc w1 (injpw j m tm' Hm') /\
        star (fun _ : unit => SmallstepLinking.step L se) tt
          (st L true (Returnstate Vundef Kstop tm) :: ks) E0 (s :: nil) /\
        (s = st L true (Returnstate Vundef Kstop tm') \/
           s = st L false (Return1 tm')).
Proof.
  induction lsp;intros.
  (* only returnstate *)
  inv H1.
  exists tm,Hm. eexists.
  split. etransitivity. eapply stack_acc_injp_acc.
  eauto. auto.
  split. eapply star_refl.
  eauto.
  (* returnstate::call2 *)
  inv H2.
  exists tm,Hm. eexists.
  split. etransitivity. eapply stack_acc_injp_acc.
  eauto. auto.
  split. 
  eapply star_step. eapply step_pop. econstructor.
  econstructor. eapply star_refl.
  eauto. eauto.
  
  
  induction H.
  admit.
  
    
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
    simpl. inv H0;try congruence; simpl; eauto.
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
   + subst. setoid_rewrite find_request;eauto. cbn. econstructor;eauto.
   + destruct (peq i 1).
      ++ subst i. setoid_rewrite find_encrypt; eauto.
         destruct (Genv.find_funct); cbn; eauto.
         destruct fundef_is_internal; reflexivity.
         cbn. econstructor;eauto.
      ++ admit.
         
  - intros q1 q2 s1 Hq Hi1. inv Hq. inv H1. inv Hi1; cbn in *.
    + (* initial request *)
      inv Hse.
      eapply Genv.find_symbol_match in H5 as FIND'; eauto.
      destruct FIND' as [fb' [FINJ FIND']]. inv H.
      inv H0. inv H7. inv H3.
      rewrite FINJ in H4. inv H4. rename b2 into fb'. rewrite Ptrofs.add_zero.
      exploit find_request; eauto.  cbn; econstructor;eauto. intro FINDR.
      exists ((st L true (Callstate (Vptr fb' Ptrofs.zero) (Vint output :: nil) Kstop m2)) :: nil).
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
      -- econstructor; eauto. eapply stack_acc_nil.  reflexivity. reflexivity. constructor.
    + (* initial encrypt *)
            inv Hse.
      eapply Genv.find_symbol_match in H5 as FIND'; eauto.
      destruct FIND' as [fb' [FINJ FIND']]. inv H.
      inv H0. inv H7. inv H3. inv H10.
      rewrite FINJ in H4. inv H4. rename b2 into fb'. rewrite Ptrofs.add_zero.
      exploit find_encrypt; eauto. cbn;econstructor;eauto. intro FINDE.
      exists ((st L false (Call1 v'0 i m2)) :: nil).
      split. split.
      -- simpl. unfold Genv.is_internal.
         setoid_rewrite find_encrypt; eauto.
         cbn;econstructor;eauto.
      -- simpl. inv H1. econstructor; eauto.
      -- inv H1.
         econstructor;eauto. eapply stack_acc_nil. reflexivity. reflexivity.
         constructor.
  (* final state *)
  - intros s1 s2 r1 Hms Hf1. inv Hf1. inv Hms;
      try inv H; cbn in *.
    +  exists (cr Vundef tm). split. cbn.
       constructor. constructor.
       eexists. split. eauto. constructor; eauto. constructor.
    + (*final of server*)
      exists (cr Vundef tm). split. cbn.
      constructor. constructor.
      eexists. split. eauto. constructor; eauto. constructor.
  - intros. cbn in *. inv H0.
  (* step *)
  - intros. inv H; inv H0.

    (* request: index == 0 *)
    + generalize Hse. intros Hse2.
      generalize INJP. intros INJP'.
      inv Hse. inv INJP.
      exploit (Genv.find_symbol_match H). eapply FINDP.
      intros (trb & FINDP3 & FINDSYMB).
      rewrite FINDREQ in FINDP. inv FINDP.
      exploit (Genv.find_symbol_match H). eapply FINDIDX.
      intros (tidb & FINDP4 & FINDTIDB).
      exploit (Genv.find_symbol_match H). eapply FINDINPUT.
      intros (tinb & FINDP5 & FINDINB).
      exploit find_encrypt'. eauto. eauto. eapply FINDE.
      intros (teb & FINDP6 & FINDTEB & FINDENC).
            
      (* stack_acc implies injp_acc *)
      exploit stack_acc_injp_acc. eapply KINJP. intro INJP1.
      inv INJP1.
      (* introduce the memory produced by target memory *)
      exploit (exec_request_mem1). eapply READIDX. eapply ADDIDX. eapply READINPUT. eapply Hm. eapply H12. eapply H22.
      eauto. instantiate (2:= r). instantiate (1:= tinb).
      intros (tm1 & tm2 & tm3 & sp & ALLOCTM & STORETM1 & STORETM2 & LOADTM2 & LOADIDXTM3 & LOADINPUTTM3 & UNCTM & INJM').
      (* step1 : evaluate the function entry *)
      simpl. eexists. split.
      eapply plus_star_trans.
      econstructor. econstructor. simpl.      
      (* step_internal *)
      econstructor. eapply find_request;eauto. eapply H22 in FINDP3 as FINDP3'.
      eapply H12 in FINDP3'.
      rewrite FINJ in FINDP3'. inv FINDP3'.  auto.
      (* function entry *)    
      econstructor; simpl.
      constructor; eauto. constructor.
      econstructor; eauto.
      constructor.
      econstructor; eauto. rewrite Maps.PTree.gss. reflexivity.
      econstructor; cbn; eauto.
      econstructor; eauto. reflexivity.
      eapply star_step; eauto.
      (* step2: if else condition *)
      econstructor;simpl.
      econstructor. econstructor. econstructor. eapply eval_Evar_global.
      auto. eauto. econstructor. econstructor.
      (* load index *)
      eauto.
      (* etransitivity. *)
      (* simpl. erewrite Mem.load_store_other. 2: eapply STORETM1. *)
      (* eapply Mem.load_alloc_other;eauto. instantiate (1:= Vint idx). *)
      (* exploit Mem.load_inject. eapply Hm'1. eauto. eauto. *)
      (* rewrite Ptrofs.unsigned_zero. *)
      (* simpl. intros (v2 & ? & ?). inv H3;try congruence. *)
      (* left. unfold not. intro. eapply Mem.fresh_block_alloc. eapply ALLOCTM. *)
      (* subst. eapply Mem.valid_block_inject_2. *)
      (* 2: eapply Hm'1. eapply H12. eapply H22. *)
      (* eapply FINDP4. *)
      (* reflexivity. *)
      econstructor. simpl. erewrite sem_cmp_int_int. simpl. fold Int.zero.
      rewrite COND. eauto. unfold if_index_eq_0.
      simpl. unfold Cop.bool_val. simpl. eauto.
      rewrite int_one_not_eq_zero. simpl.
      (* step3: index plus one *)
      eapply star_step;eauto.
      econstructor;simpl. unfold call_encrypt_indexplus.
      econstructor. eapply star_step;eauto. econstructor;simpl. 
      econstructor.
      eapply eval_Evar_global.
      auto. eauto. econstructor. econstructor.
      eapply eval_Evar_global.
      auto. eauto. econstructor. econstructor.
      eauto.       (* load index *)
      (* evaluate add index *)
      econstructor. simpl. unfold Cop.sem_add. simpl. unfold Cop.sem_binarith.
      simpl. rewrite! sem_cast_int_int. eauto.
      rewrite! sem_cast_int_int. eauto.
      (* store index *)
      econstructor. simpl. eauto.
      fold Int.one. eauto.
      (* step4: call encrypt *)
      eapply star_step;eauto. econstructor. simpl.
      econstructor.
      eapply star_step;eauto. unfold call_encrypt'.
      econstructor. simpl. 
      econstructor. simpl. eauto.
      econstructor. eapply eval_Evar_global. eauto.
      (* find encrypt symbol *) simpl. eauto.
      eapply deref_loc_reference. simpl. auto. (* deref_loc *)
      (* evaluate expression list *)
      econstructor. econstructor. econstructor.
      econstructor. econstructor. eapply eval_Evar_global. auto.
      (* find the block for input *)
      eauto.
      (* eval input *)
      eapply deref_loc_reference. simpl. auto.
      (* input[index - 1]: evaluate index - 1 *)
      econstructor. econstructor. eapply eval_Evar_global.
      auto. eauto. econstructor. simpl. auto. eauto.
      econstructor. simpl. unfold Cop.sem_sub. simpl.
      unfold Cop.sem_binarith. simpl.
      rewrite! sem_cast_int_int. rewrite Int.add_commut.
      rewrite Int.sub_add_l.
      unfold Int.one. rewrite Int.sub_idem. eauto.
      simpl. unfold Cop.sem_add. simpl. rewrite Ptrofs.add_zero_l.
      rewrite Int.add_zero_l. eauto.
      (* evaluate &index + 4* (index - 1) *)
      econstructor. simpl. eauto.
      eauto. simpl. rewrite sem_cast_int_int. eauto.
      (* evaluate request function ptr *)
      econstructor. econstructor.
      eapply eval_Evar_global. auto.
      eauto. eapply deref_loc_reference. simpl. auto.
      simpl. unfold Cop.sem_cast. simpl. eauto.
      econstructor.
      (* find encrypt definition *)
      eapply find_encrypt_1;eauto.
      simpl. eauto.
      (* step5: at external *)
      eapply star_step. eapply step_push.
      simpl. econstructor. eapply find_encrypt_1;eauto.
      instantiate (1:= false). simpl.
      unfold Genv.is_internal. erewrite FINDENC. auto.
      simpl. econstructor. erewrite FINDENC. auto.
      eapply star_refl.
      1-2: eauto.
      eapply star_refl.
      eauto.

      (* match state *)
      assert (INJ1 :Mem.inject j m tm1).
      eapply Mem.alloc_right_inject;eauto.
      econstructor.
      (* stack acc *)
      instantiate (1:= sp::lsp).
      instantiate (1:= injpw j m' tm3 INJM').
      econstructor.
      eapply Hm'1. instantiate (1:= Hm). eauto.
      eapply stack_acc_compose_injp_acc. eauto. eauto.
      etransitivity. eapply stack_acc_injp_acc. eauto. eauto.
      eauto.
      (* (m,tm1,j) ~~> (m',tm3,j) *)
      instantiate (1:= INJ1).
      admit.      
      reflexivity.
      eauto.
      (* match_kframe *)
      inv KFRM. econstructor. econstructor. econstructor.
      econstructor. eauto.
      
    (* request: 0 < index < N *)
    + admit.

    (* request: index >= N, return *)
    + generalize Hse. intros Hse2.
      generalize INJP. intros INJP'.
      inv Hse. inv INJP.
      exploit (Genv.find_symbol_match H). eapply FINDP.
      intros (trb & FINDP3 & FINDSYMB).
      exploit (Genv.find_symbol_match H). eapply FINDIDX.
      intros (tidb & FINDP4 & FINDTIDB).
      exploit (Genv.find_symbol_match H). eapply FINDRES.
      intros (tresb & FINDP5 & FINDRESB).
            
      (* stack_acc implies injp_acc *)
      exploit stack_acc_injp_acc. eapply KINJP. intro INJP1.
      inv INJP1.
      (* introduce the memory produced by target memory *)
      exploit exec_request_mem3. eapply READIDX. eapply STORERES.
      eapply H12. eapply H22. eauto.
      eapply H12. eapply H22. eauto.
      instantiate (2:= tm). instantiate (1:= Hm).
      intros (tm1 & tm2 & tm3 & tm4 & sp & INJTM4 & ALLOCTM & STORETM1 & LOADTM2 & LOADSP & STORETM2 & FREETM3 & INJPTM4).
      (* step1: function entry *)
      simpl. eexists. split.
      eapply plus_star_trans.
      econstructor. econstructor. simpl.      
      (* step_internal *)
      econstructor. eapply find_request;eauto. eapply H22 in FINDP3 as FINDP3'.
      eapply H12 in FINDP3'.
      rewrite FINJ in FINDP3'. inv FINDP3'.  auto.
      (* function entry *)    
      econstructor; simpl.
      constructor; eauto. constructor.
      econstructor; eauto.
      constructor.
      econstructor; eauto. rewrite Maps.PTree.gss. reflexivity.
      econstructor; cbn; eauto.
      econstructor; eauto. reflexivity.
      eapply star_step; eauto.
      (* step2: if(index == 0) *)
      econstructor;simpl.
      econstructor. econstructor. econstructor. eapply eval_Evar_global.
      auto. eauto. econstructor. econstructor.
      (* load index *)
      eauto.
      econstructor. simpl. erewrite sem_cmp_int_int. simpl. fold Int.zero.
      rewrite ge_N_not_zero. eauto. auto.
      simpl. unfold Cop.bool_val. simpl. rewrite Int.eq_true. eauto.
      simpl.
      (* step3: if(0<index<N) *)
      unfold if_index_gt_0_lt_N. eapply star_step;eauto.
      econstructor;simpl. econstructor. econstructor. econstructor.
      econstructor.
      eapply eval_Evar_global. auto. eauto.
      econstructor. simpl. eauto.
      eauto. econstructor. simpl. rewrite sem_cmp_int_int.
      simpl.                    
      eauto. econstructor. econstructor. eapply eval_Evar_global.
      auto. eauto. econstructor. simpl. eauto. eauto.
      econstructor. simpl. rewrite sem_cmp_int_int.
      simpl. simpl in COND. rewrite negb_true_iff in COND.
      unfold Nint in COND. rewrite COND. simpl. eauto.
      eauto. unfold Val.of_bool. destruct Int.lt.
      (* sem_and *)
      simpl. unfold Cop.sem_and. unfold Cop.sem_binarith. unfold Cop.sem_cast. simpl.
      destruct Archi.ptr64 eqn:PTR. simpl. rewrite Int.and_zero. eauto.
      destruct Ctypes.intsize_eq;try congruence. simpl. rewrite Int.and_zero. eauto.
      simpl.
      unfold Cop.sem_and. unfold Cop.sem_binarith. unfold Cop.sem_cast. simpl.
      destruct Archi.ptr64 eqn:PTR. simpl. rewrite Int.and_zero. eauto.
      destruct Ctypes.intsize_eq;try congruence. simpl. rewrite Int.and_zero. eauto.
      simpl. unfold Cop.bool_val. simpl. rewrite Int.eq_true. eauto.
      simpl.
      (* step4: else branch *)
      eapply star_step;eauto. econstructor. simpl.
      (* evaluate result index *)
      econstructor. econstructor.  econstructor.
      econstructor. eapply eval_Evar_global;eauto.
      eapply deref_loc_reference. eauto.
      econstructor. econstructor. eapply eval_Evar_global;eauto.
      econstructor. simpl. eauto.
      eauto. econstructor. simpl.
      unfold Cop.sem_sub. simpl. unfold Cop.sem_binarith. simpl.
      rewrite! sem_cast_int_int. eauto.
      simpl. unfold Cop.sem_add. unfold Cop.sem_binarith. simpl.
      eauto.      
      econstructor. eapply eval_Evar_local. eapply Maps.PTree.gss.
      econstructor. simpl. eauto. eauto.
      simpl. erewrite sem_cast_int_int. eauto.
      econstructor. simpl. eauto.
      rewrite Ptrofs.add_zero_l. eauto.
      (* step5: return state *)
      eapply star_step;eauto. econstructor. simpl.
      econstructor. unfold is_call_cont. auto.
      (* free list *)
      simpl. rewrite FREETM3. eauto.
      (* step6: execute the continuation *)
                
              
               \/
              star (fun _ : unit => SmallstepLinking.step L se2) tt
                (st L true (Returnstate Vundef Kstop tm) :: ks) E0
                (st L true (Returnstate Vundef Kstop tm') :: nil)
              

      eapply star_step
      
Admitted.
                                        
      
End WITH_N.
