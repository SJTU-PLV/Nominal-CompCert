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
| step_request1 r input rb idb inb idx m m'
  (FINDIDX: Genv.find_symbol se index_id = Some idb)
  (FINDREQ: Genv.find_symbol se request_id = Some rb)
  (FINDINPUT: Genv.find_symbol se input_id = Some inb)
  (READIDX: Mem.loadv Mint32 m (Vptr idb Ptrofs.zero) = Some (Vint idx))
  (COND: Int.eq idx Int.zero = true)
  (ADDIDX: Mem.storev Mint32 m (Vptr idb Ptrofs.zero) (Vint (Int.add idx Int.one)) = Some m')
  (READINPUT: Mem.loadv Mint32 m' (Vptr inb (Ptrofs.sub (Ptrofs.of_int idx) (Ptrofs.one))) = Some (Vint input)):
  step (Callrequest r m) E0 (Callencrypt input (Vptr rb Ptrofs.zero) m')
| step_request2 r input rb idb inb rsb idx m m' m''
  (FINDIDX: Genv.find_symbol se index_id = Some idb)
  (FINDREQ: Genv.find_symbol se request_id = Some rb)
  (FINDINPUT: Genv.find_symbol se input_id = Some inb)
  (FINDRES: Genv.find_symbol se result_id = Some rsb)
  (READIDX: Mem.loadv Mint32 m (Vptr idb Ptrofs.zero) = Some (Vint idx))
  (COND: Int.lt Int.zero idx && Int.lt idx Nint = true)
  (STORERES: Mem.storev Mint32 m (Vptr rsb (Ptrofs.sub (Ptrofs.of_int idx) (Ptrofs.one))) (Vint r) = Some m')
  (ADDIDX: Mem.storev Mint32 m' (Vptr idb Ptrofs.zero) (Vint (Int.add idx Int.one)) = Some m'')
  (READINPUT: Mem.loadv Mint32 m'' (Vptr inb (Ptrofs.sub (Ptrofs.of_int idx) (Ptrofs.one))) = Some (Vint input)):
  step (Callrequest r m) E0 (Callencrypt input (Vptr rb Ptrofs.zero) m'')
| step_request3 r idb rsb idx m m'
  (FINDIDX: Genv.find_symbol se index_id = Some idb)
  (FINDRES: Genv.find_symbol se result_id = Some rsb)
  (READIDX: Mem.loadv Mint32 m (Vptr idb Ptrofs.zero) = Some (Vint idx))
  (COND: Int.cmp Cge idx Nint = true)
  (STORERES: Mem.storev Mint32 m (Vptr rsb (Ptrofs.sub (Ptrofs.of_int idx) (Ptrofs.one))) (Vint r) = Some m'):
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

Inductive match_kframe_request : list (frame L) -> Prop :=
| match_kframe_request_nil:
  match_kframe_request nil
| match_kframe_request_call2 output m fb:
  match_kframe_request ((st L false (Call2 fb output m)) :: nil)
| match_kframe_request_cons output m fb1 fb2 vargs k sp le:
  match_kframe_request k ->
  match_kframe_request ((st L false (Call2 fb1 output m)) :: (st L true (Callstate fb2 vargs (Kcall None func_request (Maps.PTree.set r_id (sp, Ctypesdefs.tint) empty_env) le Kstop) m)) :: k).

Inductive match_kframe_encrypt : list (frame L) -> Prop :=
| match_kframe_encrypt_nil:
  match_kframe_encrypt nil
| match_kframe_encrypt_callstate m fb sp le vargs:
  match_kframe_encrypt ((st L true (Callstate fb vargs (Kcall None func_request (Maps.PTree.set r_id (sp, Ctypesdefs.tint) empty_env) le Kstop) m)) :: nil)
| match_kframe_encrypt_cons output m fb1 fb2 vargs k sp le:
  match_kframe_encrypt k ->
  match_kframe_encrypt ((st L true (Callstate fb2 vargs (Kcall None func_request (Maps.PTree.set r_id (sp, Ctypesdefs.tint) empty_env) le Kstop) m)) :: (st L false (Call2 fb1 output m)) :: k).


Inductive match_state: state -> list (frame L) -> Prop :=
| match_request_intro j r rb rb' m tm ks
    (Hm: Mem.inject j m tm)
    (INJP: injp_acc w (injpw j m tm Hm))
    (FINDP: Genv.find_symbol se request_id = Some rb)
    (FINJ: j rb = Some (rb',0))
    (KFRM: match_kframe_request ks):
  match_state (Callrequest r m) ((st L true (Callstate (Vptr rb' Ptrofs.zero) (Vint r :: nil) Kstop tm)) :: ks)
| match_encrypt_intro j v tv m tm input ks
    (Hm: Mem.inject j m tm)
    (INJP: injp_acc w (injpw j m tm Hm))
    (VINJ: Val.inject j v tv)
    (KFRM: match_kframe_encrypt ks):
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
      -- econstructor; eauto. reflexivity. constructor.
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
         econstructor;eauto. reflexivity.
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
  - Admitted.
        
End MS.
End WITH_N.
