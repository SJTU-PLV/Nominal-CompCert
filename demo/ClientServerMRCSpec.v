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
| stack_acc_cons f1 m1 tm1 w1 (Hm1: Mem.inject f1 m1 tm1) lsp tm1' tm1'' sp Hm1' w2 r
    (Hm1: Mem.inject f1 m1 tm1)
    (WORLD1: w1 = injpw f1 m1 tm1 Hm1)
    (STKB: stack_acc w w1 lsp)
    (* (INJP1: injp_acc w w1) *)
    (ALLOC: Mem.alloc tm1 0 4 = (tm1', sp))
    (STORESP: Mem.store Mint32 tm1' sp 0 (Vint r) = Some tm1'')
    (INJP2: injp_acc (injpw f1 m1 tm1'' Hm1') w2):
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

Lemma find_request_server:
  forall rb',
  Genv.find_symbol tge2 request_id = Some rb' ->
  Genv.find_funct tge2 (Vptr rb' (Ptrofs.repr 0)) =
    Some (External (EF_external "complete" int__void_sg)).
Proof.
  intros. simpl in *.
  unfold Ptrofs.zero. destruct Ptrofs.eq_dec;try congruence.
  eapply Genv.find_funct_ptr_iff. unfold Genv.find_def.
  unfold tge2. simpl.
  unfold Genv.find_symbol in H.
  unfold Genv.add_globdef.
  unfold Maps.PTree.prev. simpl.
  unfold request_id in *. rewrite H.
  unfold NMap.get. rewrite NMap.gss.
  auto.
Qed.

End MS.


(* Lemma stack_acc_injp_acc: forall w1 w2 lsp, *)
(*     stack_acc w1 w2 lsp -> *)
(*     injp_acc w1 w2. *)
(* Proof. *)
(*   intros. induction H. *)
(*   auto. *)
(*   etransitivity. eapply IHstack_acc. *)
(*   etransitivity. 2: eapply INJP2. *)
(*   subst. *)
(*   assert (ro_acc m1 m1). eapply ro_acc_refl. *)
(*   assert (ro_acc tm1 tm1''). *)
(*   eapply ro_acc_trans. *)
(*   eapply ro_acc_alloc;eauto. *)
(*   eapply ro_acc_store;eauto. *)
(*   inv H0. inv H1. *)
(*   econstructor; eauto. *)
(*   eapply Mem.unchanged_on_refl. *)
(*   eapply Mem.unchanged_on_trans. *)
(*   eapply Mem.alloc_unchanged_on;eauto. *)
(*   eapply Mem.store_unchanged_on;eauto. simpl. *)
(*   intros. unfold loc_out_of_reach. intro. eapply H7. *)
  
(*   eapply inject_separated_refl. *)
(* Qed. *)

Lemma stack_acc_inject_incr: forall lsp j1 j2 m1 m2 tm1 tm2 Hm Htm,
    stack_acc (injpw j1 m1 m2 Hm) (injpw j2 tm1 tm2 Htm) lsp ->
    inject_incr j1 j2.
Proof.
  induction lsp;intros. inv H. inv H0. eauto.
  inv H.
  inv INJP2.
  eapply inject_incr_trans. 2: eapply H11.
  eapply IHlsp;eauto.
Qed.

Lemma stack_acc_sup_include1: forall lsp j1 j2 m1 m2 tm1 tm2 Hm Htm,
    stack_acc (injpw j1 m1 m2 Hm) (injpw j2 tm1 tm2 Htm) lsp ->
    Mem.sup_include (Mem.support m1) (Mem.support tm1).
Proof.
  induction lsp;intros. inv H. inv H0. eapply H10.
  inv H.
  inv INJP2.
  eapply Mem.sup_include_trans. 2: eapply H9.
  eapply IHlsp;eauto.
Qed.

Lemma stack_acc_sup_include2: forall lsp j1 j2 m1 m2 tm1 tm2 Hm Htm,
    stack_acc (injpw j1 m1 m2 Hm) (injpw j2 tm1 tm2 Htm) lsp ->
    Mem.sup_include (Mem.support m2) (Mem.support tm2).
Proof.
  induction lsp;intros. inv H. inv H0. eapply H11.
  inv H.
  inv INJP2.
  eapply Mem.sup_include_trans.
  eapply IHlsp;eauto.
  eapply Mem.sup_include_trans.
  eapply Mem.sup_include_incr. 
  eapply Mem.sup_include_trans.
  instantiate (1 := Mem.support tm1').
  erewrite <- Mem.support_alloc;eauto.
  eapply Mem.sup_include_trans.
  instantiate (1 := Mem.support tm1'').
  exploit Mem.support_store. eauto. intros.
  rewrite H. eapply Mem.sup_include_refl.
  eapply H10.  
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
    j inb = Some (tinb,0) ->
    exists tm1 sp tm2 tm3 Hm Hm',
      Mem.alloc tm 0 4 = (tm1, sp) /\
        Mem.storev Mint32 tm1 (Vptr sp Ptrofs.zero) (Vint output) = Some tm2 /\
        Mem.storev Mint32 tm2 (Vptr tib Ptrofs.zero) (Vint idx') = Some tm3 /\
        Mem.loadv Mint32  tm2 (Vptr tib Ptrofs.zero) = Some (Vint idx) /\
        Mem.loadv Mint32  tm3 (Vptr tib Ptrofs.zero) = Some (Vint idx') /\
        Mem.loadv Mint32 tm3 (Vptr tinb ofs) = Some (Vint input) /\
        (* Mem.unchanged_on (fun b ofs => b = tib -> ~ 0 <= ofs < 4) tm tm3 /\ *)
        injp_acc (injpw j sm tm2 Hm) (injpw j sm1 tm3 Hm').
Proof.
  intros until tinb.
  intros LOADSM STORESM LOADSM1 INJ INJIB INJINB.
  destruct (Mem.alloc tm 0 4) as [tm1 sp] eqn:ALLOCTM.
  exploit Mem.alloc_right_inject;eauto.
  intros INJ1.
  exists tm1,sp.
  assert (STORETM1: {tm2:mem| Mem.store Mint32 tm1 sp 0 (Vint output) = Some tm2}).
  eapply Mem.valid_access_store. unfold Mem.valid_access.
  split. red. intros.
  eapply Mem.perm_implies.
  eapply Mem.valid_access_alloc_same;eauto.
  lia. simpl. lia. apply Z.divide_0_r.
  constructor. apply Z.divide_0_r.
  destruct STORETM1 as (tm2 & STORETM1).
  exists tm2.
  exploit Mem.store_outside_inject. eapply INJ1.
  2: eapply STORETM1. intros.
  eapply Mem.fresh_block_alloc;eauto.
  eapply Mem.valid_block_inject_2;eauto.
  intros INJ2.
  exploit Mem.store_mapped_inject;eauto.
  intros (tm3 & STORETM2 & INJ3).
  rewrite Z.add_0_l in STORETM2.
  exists tm3, INJ2, INJ3.
  exploit Mem.load_inject. eapply INJ2. eauto. eauto.
  intros (v2 & LOADTM2 & VINJ). inv VINJ.
  exploit Mem.load_store_same. eapply STORETM2.
  simpl. intros LOADTM3.
  exploit Mem.load_inject. eapply INJ3. eauto. eauto.
  intros (v2 & LOADINP & VINJ). inv VINJ.
 rewrite Z.add_0_r in LOADINP.
  simpl. unfold Ptrofs.zero. rewrite Ptrofs.unsigned_repr.
  (do 6 try split);auto.
  (* injp_acc *)
  eapply injp_acc_store;eauto.
  rewrite Z.add_0_r. eauto.
  rewrite maxv. lia.
Qed.

    
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
    exists tm1 sp tm2 tm3 tm4 Hm Hm',
      Mem.alloc tm 0 4 = (tm1, sp) /\
        Mem.storev Mint32 tm1 (Vptr sp Ptrofs.zero) (Vint output) = Some tm2 /\
        Mem.loadv Mint32  tm2 (Vptr tib Ptrofs.zero) = Some (Vint idx) /\
        Mem.loadv Mint32 tm2 (Vptr sp Ptrofs.zero) = Some (Vint r) /\
        Mem.storev Mint32 tm2 (Vptr tresb ofs1) (Vint r) = Some tm3 /\
        Mem.loadv Mint32 tm3 (Vptr tib Ptrofs.zero) = Some (Vint idx') /\
        Mem.storev Mint32 tm3 (Vptr tib Ptrofs.zero) (Vint idx'') = Some tm4 /\
        Mem.loadv Mint32 tm4 (Vptr tinb ofs2) = Some (Vint input) /\
        injp_acc (injpw j sm tm2 Hm) (injpw j sm2 tm4 Hm').
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
Proof.
  intros until Hm0.
  intros LOADSM STORESM INJ1 INJ2.
  destruct (Mem.alloc tm 0 4) as [tm1 sp] eqn: ALLOC.
  exists tm1.
  exploit Mem.alloc_right_inject;eauto. intros INJ3.
  assert (STOREM: {m2: mem | Mem.store Mint32 tm1 sp 0 (Vint r) = Some m2}).
  eapply Mem.valid_access_store. eapply Mem.valid_access_implies.
  eapply Mem.valid_access_alloc_same;eauto. lia. simpl. lia. simpl.
  eapply Z.divide_0_r. econstructor.
  destruct STOREM as (tm2 & STOREM).
  exists tm2.
  (* inject sm tm2 *)
  exploit Mem.store_outside_inject;eauto.
  intros. eapply Mem.fresh_block_alloc;eauto.
  eapply Mem.valid_block_inject_2;eauto.
  intros INJ4.
  (* loadv index from tm2 *)
  exploit Mem.loadv_inject. eapply INJ4. eapply LOADSM.
  eapply Val.inject_ptr;eauto.
  intros (v2 & LOADTM2 & VINJ). inv VINJ.
  (* loadv sp from tm2 *)
  exploit Mem.load_store_same. eapply STOREM.
  intros LOADSPTM2. simpl in LOADSPTM2.
  (* store result *)
  exploit Mem.store_mapped_inject. eapply INJ4.  
  eapply STORESM. eauto. eapply Val.inject_int.
  intros (tm3 & STORERESTM & INJ5).
  exists tm3.
  (* free *)
  assert (FREE: {tm4:mem | Mem.free tm3 sp 0 4 = Some tm4}).
  eapply Mem.range_perm_free.
  unfold Mem.range_perm. intros .
  eapply Mem.perm_store_1;eauto.
  eapply Mem.perm_store_1;eauto.
  eapply Mem.perm_alloc_2;eauto.
  destruct FREE as (tm4 & FREE).
  exists tm4, sp.
  (* inject sm1 tm4 *)
  exploit Mem.free_right_inject. eapply INJ5. eauto.
  intros. eapply Mem.fresh_block_alloc;eauto.
  eapply Mem.valid_block_inject_2;eauto.
  intros INJ6.
  exists INJ6.
  rewrite Z.add_0_r in STORERESTM.
  do 6 (split;eauto). 
  (* injp_acc *)
  assert (RO1: ro_acc sm sm1).
  eapply ro_acc_store;eauto.
  assert (RO2: ro_acc tm tm4).
  eapply ro_acc_trans. eapply ro_acc_alloc;eauto.
  eapply ro_acc_trans. eapply ro_acc_store;eauto.
  eapply ro_acc_trans. eapply ro_acc_store;eauto.
  eapply ro_acc_free;eauto.
  inv RO1. inv RO2.
  econstructor;eauto.
  (* unchanged_on sm sm1 *)
  eapply Mem.store_unchanged_on;eauto.
  simpl. intros. unfold loc_unmapped. congruence.  
  (* unchanged_on tm tm4 *)
  econstructor;eauto.
  (* unchanged_on_perm *)
  intros.
  assert (b<>sp). intro. eapply Mem.fresh_block_alloc;eauto.
  subst. auto.
  eapply iff_trans. split. eapply Mem.perm_alloc_1;eauto.
  intros. eapply Mem.perm_alloc_4;eauto.
  eapply iff_trans. split. eapply Mem.perm_store_1;eauto.
  eapply Mem.perm_store_2;eauto.
  eapply iff_trans. split. eapply Mem.perm_store_1;eauto.
  eapply Mem.perm_store_2;eauto.
  split. eapply Mem.perm_free_1;eauto.
  eapply Mem.perm_free_3;eauto.
  (* mem contents *)
  intros.
  assert (b<>sp). intro. eapply Mem.fresh_block_alloc;eauto.
  subst. eapply Mem.perm_valid_block;eauto.
  assert (PERM1: Mem.perm tm1 b ofs Cur Readable).
  eapply Mem.perm_alloc_1;eauto.
  assert (PERM2: Mem.perm tm2 b ofs Cur Readable).
  eapply Mem.perm_store_1;eauto.
  assert (PERM3: Mem.perm tm3 b ofs Cur Readable).
  eapply Mem.perm_store_1;eauto.
  assert (PERM4: Mem.perm tm4 b ofs Cur Readable).
  eapply Mem.perm_free_1;eauto. 
  etransitivity.
  eapply Mem.free_unchanged_on with (P:= fun b _ => b <> sp);eauto.
  etransitivity.
  eapply Mem.store_unchanged_on;eauto.
  intros. unfold loc_out_of_reach. intro. eapply H9;eauto. 
  rewrite Z.sub_0_r.
  exploit Mem.store_valid_access_3. eapply STORESM.
  unfold Mem.valid_access.
  intros (RNG & DIV).
  eapply Mem.perm_implies. eapply Mem.perm_cur_max.
  eapply RNG. auto.
  econstructor.
  (* contents tm2 tm *)
  etransitivity.
  eapply Mem.store_unchanged_on with (P:= fun b _ => b <> sp);eauto.
  eapply Mem.alloc_unchanged_on;eauto.
  eapply inject_separated_refl.
Qed.  
      
Lemma exec_kframe: forall lsp w1 w2 m tm j Hm  ks se,
    stack_acc w1 w2 lsp ->
    injp_acc w2 (injpw j m tm Hm) ->
    match_kframe_request lsp ks ->
    exists tm' Hm' s,
      injp_acc w1 (injpw j m tm' Hm') /\
        star (fun _ : unit => SmallstepLinking.step L se) tt
          (st L true (Returnstate Vundef Kstop tm) :: ks) E0 (s :: nil) /\
        (s = st L true (Returnstate Vundef Kstop tm') \/
           s = st L false (Return2 tm')).
Proof.
  induction lsp;intros.
  (* only returnstate *)
  inv H1.
  exists tm,Hm. eexists.
  split. inv H. etransitivity. eauto.
  eauto.
  split. eapply star_refl.
  eauto.
  (* returnstate::call2 *)
  inv H. inv H2.
  exists tm,Hm. eexists.
  split. etransitivity. eauto.
  eauto. split.
  eapply star_step. eapply step_pop. econstructor.
  econstructor. eapply star_step. econstructor. simpl.
  econstructor. eapply star_refl.
  eauto. eauto. auto.
  (* induction *)
  inv H1. inv H2. inv H.
  assert (INJP3: injp_acc (injpw f1 m2 tm1'' Hm1') (injpw j m tm Hm)).
  etransitivity;eauto.

  assert (FREE: {tm2:mem | Mem.free tm1'' a 0 4 = Some tm2}).
  eapply Mem.range_perm_free. unfold Mem.range_perm. intros.
  eapply Mem.perm_store_1;eauto. 
  eapply Mem.perm_alloc_2. eauto. auto. destruct FREE as (tm2 & FREE).

  generalize INJP3. intro INJP4.
  inv INJP3.
  exploit Mem.free_mapped_unchanged_on. eapply H12.
  instantiate (1:= a). instantiate (1:=4). instantiate (1:=0).
  intros. unfold loc_out_of_reach. intros.
  (* loc out of reach *)
  intro. eapply Mem.fresh_block_alloc. eauto.
  eapply Mem.valid_block_inject_2. eauto. eauto.
  eauto.
  intros (tm3 & FREE2 & UNC).

  assert (INJ: Mem.inject j m tm3).
  eapply Mem.free_right_inject;eauto.
  intros.
  (* prove f1 b1 = None *)
  destruct (f1 b1) eqn: FB1. destruct p0. eapply H13 in FB1 as FB2.
  rewrite H in FB2. inv FB2.
  eapply Mem.fresh_block_alloc. eauto.
  eapply Mem.valid_block_inject_2. eauto. eauto.
  (* try to prove  a is invalid in tm1' *)
  exploit H14. 2: eapply H. auto.
  intros (INVALID1 & INVALID2). eapply INVALID2.
  unfold Mem.valid_block.
  erewrite Mem.support_store;eauto.
  erewrite Mem.support_alloc;eauto.
  eapply Mem.sup_incr_in. left.
  eapply Mem.alloc_result;eauto.

  assert (RO1: ro_acc m2 m).
  inv INJP4. econstructor. eauto.
  eapply Mem.unchanged_on_support;eauto.
  eauto.
  assert (RO2: ro_acc tm1 tm3).
  eapply ro_acc_trans. eapply ro_acc_alloc;eauto.
  eapply ro_acc_trans. eapply ro_acc_store;eauto.
  eapply ro_acc_trans.
  inv INJP4. econstructor. eauto.
  eapply  Mem.unchanged_on_support;eauto.
  eauto.
  eapply ro_acc_free;eauto.

  inv RO1. inv RO2.
  assert (INJP5: injp_acc (injpw f1 m2 tm1 Hm0) (injpw j m tm3 INJ)).
  inv INJP4.
  econstructor;eauto.
  econstructor.
  (* sup include *)
  eapply Mem.sup_include_trans. instantiate (1 := (Mem.support tm1')).
  exploit Mem.support_alloc. eapply ALLOC. intros. rewrite H15.
  eapply Mem.sup_include_incr. eapply Mem.sup_include_trans.
  instantiate (1 := (Mem.support tm1'')). exploit Mem.support_store.
  eauto. intros SUPTM''. rewrite SUPTM''. eapply Mem.sup_include_refl.
  eapply Mem.sup_include_trans.
  eapply Mem.unchanged_on_support. eauto.
  exploit Mem.support_free. eauto. intros. rewrite H15. eapply Mem.sup_include_refl.
  (* perm *)
  intros.
  assert (b <> a). intro.
  eapply Mem.fresh_block_alloc. eauto. subst. auto.
  split;intros.
  eapply Mem.perm_free_1;eauto.
  erewrite <- Mem.unchanged_on_perm. 2: eauto. 2:auto.
  eapply Mem.perm_store_1;eauto.
  eapply Mem.perm_alloc_1;eauto.
  eapply Mem.store_valid_block_1;eauto.
  eapply Mem.valid_block_alloc;eauto.
  eapply Mem.perm_alloc_4. eapply ALLOC.
  eapply Mem.perm_store_2;eauto.
  eapply Mem.unchanged_on_perm;eauto.
  eapply Mem.store_valid_block_1;eauto.
  eapply Mem.valid_block_alloc;eauto.
  eapply Mem.perm_free_3;eauto.
  auto.
  (* contents *)
  intros.
  assert (b <> a). intro. subst.
  eapply Mem.fresh_block_alloc;eauto. eapply Mem.perm_valid_block;eauto.
  etransitivity.
  eapply Mem.free_unchanged_on. eapply FREE2. instantiate (1 := fun b _ => b <> a).
  intros. intro. congruence.
  simpl. auto.
  eapply H26;eauto.
  eapply Mem.store_valid_block_1;eauto.
  eapply Mem.valid_block_alloc;eauto.
  eapply Mem.perm_valid_block;eauto.
  eapply Mem.perm_store_1;eauto.
  eapply Mem.perm_alloc_1;eauto.
  etransitivity.
  eapply H26;eauto.
  eapply Mem.perm_store_1;eauto.
  eapply Mem.perm_alloc_1;eauto.
  etransitivity.
  eapply Mem.store_unchanged_on. eauto. instantiate (1 := fun b _ => b <> a).
  intros. simpl. congruence.
  simpl. auto. eapply Mem.perm_alloc_1;eauto.
  eapply Mem.alloc_unchanged_on;eauto.

  (* inject separated *)
  unfold inject_separated. intros.
  split.
  eapply H28;eauto.
  intro. eapply Mem.valid_block_alloc in H17;eauto.
  eapply H28;eauto.
  eapply Mem.store_valid_block_1;eauto.

  (* use I.H. *)
  exploit IHlsp. eauto.
  eapply INJP5. eauto. instantiate (1 := se).
  intros (tm' & Hm' & s & INJP6 & EXEC & TOPS).
  exists tm', Hm', s.
  split;auto.
  split;auto.
  (* exit function *)
  eapply star_step. eapply step_pop.
  econstructor. simpl.
  econstructor.
  eapply star_step. econstructor. simpl.
  econstructor. 
  eapply star_step. eapply step_pop.
  econstructor. simpl.
  econstructor.
  eapply star_step. econstructor. simpl.
  econstructor. 
  eapply star_step. econstructor. simpl.
  econstructor. simpl. auto.
  (* free list *)
  simpl. rewrite FREE2. eauto.
  (* final *)
  eapply EXEC.
  all: eauto.
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
    + subst. setoid_rewrite find_request with (w:= injpw f0 m1 m2 Hm0);eauto.
      cbn. econstructor;eauto.     
   + destruct (peq i 1).
     ++ subst i.
        exploit find_encrypt. 2: eauto.
        instantiate (1 := injpw f0 m1 m2 Hm0). simpl.
        econstructor;eauto. eauto. eauto. intros.
        rewrite H0.
        unfold fundef_is_internal. simpl. eapply orb_true_r.
      ++ admit.
        
  - intros q1 q2 s1 Hq Hi1. inv Hq. inv H1. inv Hi1; cbn in *.
    + (* initial request *)
      inv Hse.
      eapply Genv.find_symbol_match in H5 as FIND'; eauto.
      destruct FIND' as [fb' [FINJ FIND']]. inv H.
      inv H0. inv H7. inv H3.
      rewrite FINJ in H4. inv H4. rename b2 into fb'. rewrite Ptrofs.add_zero.
      exploit find_request. instantiate (3 := injpw f m1 m2 Hm). 2-4:eauto.
      cbn; econstructor;eauto. intro FINDR.
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
      exploit find_encrypt. instantiate (3 := injpw f m1 m2 Hm). 2-4:eauto.
      cbn;econstructor;eauto. intro FINDE.
      exists ((st L false (Call1 v'0 i m2)) :: nil).
      split. split.
      -- simpl. unfold Genv.is_internal.
         setoid_rewrite find_encrypt with (w:= injpw f m1 m2 Hm); eauto.
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
            
      (* stack_acc implies inject_incr *)
      assert (H22: inject_incr f f0).
      eapply stack_acc_inject_incr. eapply KINJP.
      (* introduce the memory produced by target memory *)
      exploit (exec_request_mem1). eapply READIDX. eapply ADDIDX. eapply READINPUT. eapply Hm. eapply H12. eapply H22.
      eauto. instantiate (1:= tinb). auto.
      intros (tm1 & sp & tm2 & tm3 & INJM & INJM' & ALLOCTM & STORETM1 & STORETM2 & LOADTM2 & LOADIDXTM3 & LOADINPUTTM3 & INJPM).
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
      econstructor.
      (* stack acc *)
      instantiate (1:= sp::lsp).
      instantiate (1:= injpw j m tm2 INJM).
      econstructor.
      eapply Hm. instantiate (1:= Hm). eauto.
      eapply stack_acc_compose_injp_acc. 
      eauto. eauto. eauto. eauto.
      reflexivity. eapply INJPM.
      econstructor. eauto. rewrite Ptrofs.add_zero. auto.
      (* match_kframe *)
      inv KFRM. econstructor. econstructor. econstructor.
      econstructor. eauto.
      
    (* request: 0 < index < N *)
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
      exploit (Genv.find_symbol_match H). eapply FINDRES.
      intros (tresb & FINDP7 & FINDRESB).

      assert (IDXNEQRES: idb <> rsb).
      intro. subst.
      exploit Genv.find_symbol_injective.
      eapply FINDIDX. eapply FINDRES.
      unfold index_id. unfold result_id.
      intros. inv H2.

      exploit Mem.load_store_other. eapply STORERES.
      left. eapply IDXNEQRES.
      simpl in READIDX. rewrite READIDX.
      intros LOADRES'.
      
      (* stack_acc implies inject_incr *)
      assert (H22: inject_incr f f0).
      eapply stack_acc_inject_incr. eapply KINJP.
      (* introduce the memory produced by target memory *)
      exploit (exec_request_mem2). eapply READIDX. eapply STORERES.
      eauto. eauto. eauto.       
      eapply Hm. eapply H12. eapply H22.
      eauto. instantiate (1:= tinb). auto. eauto.
      instantiate (1 := r).
      intros (tm1 & sp & tm2 & tm3 & tm4 & INJM & INJM'' & ALLOCTM & STORETM1 & LOADTM2 & LOADSP & STORETM2 & LOADTM3 & STORETM3 & LOADTM4 & INJPM).
      (* simplfy condition *)
      eapply andb_true_iff in COND.
      destruct COND as (COND1 & COND2).
      generalize COND1. intros COND3. rewrite Int.lt_not in COND3.
      eapply andb_true_iff in COND3.
      destruct COND3 as (COND4 & COND5). eapply negb_true_iff in COND5.
      eapply negb_true_iff in COND4.
      
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
      (* step2: if index==0 *)
      econstructor. simpl. 
      econstructor. econstructor.
      econstructor. eapply eval_Evar_global.
      auto. eauto. econstructor. simpl. eauto.
      eauto. econstructor. simpl. rewrite sem_cmp_int_int.
      simpl. unfold Int.zero in COND5. rewrite COND5.
      eauto.
      unfold Cop.bool_val. simpl. rewrite Int.eq_true.
      eauto. simpl.
      (* step3: if (0 < index < N) *)
      eapply star_step;eauto. econstructor.
      simpl. econstructor. econstructor.
      econstructor. econstructor.
      eapply eval_Evar_global.
      auto. eauto. econstructor. simpl. eauto.
      eauto. econstructor. simpl.
      rewrite sem_cmp_int_int. simpl. unfold Int.zero in COND1.
      rewrite COND1. eauto.
      econstructor. econstructor. 
      eapply eval_Evar_global.
      auto. eauto. econstructor. simpl. eauto.
      eauto. econstructor. simpl.
      rewrite sem_cmp_int_int. simpl. unfold Nint in COND2.
      rewrite COND2. eauto.
      simpl.
      unfold Cop.sem_and. unfold Cop.sem_binarith. unfold Cop.sem_cast. simpl.
      destruct Archi.ptr64 eqn:PTR. simpl. eauto.
      destruct Ctypes.intsize_eq;try congruence. simpl. eauto.
      simpl. rewrite Int.and_idem. unfold Cop.bool_val.
      simpl. destruct (Int.eq Int.one Int.zero) eqn: EQ.
      exploit Int.eq_spec. rewrite EQ. intros.
      exploit Int.one_not_zero. eauto. intros. contradiction.
      eauto.
      simpl.
      (* step4: assign result *)
      eapply star_step;eauto. econstructor.
      simpl. econstructor.
      eapply star_step;eauto. econstructor.
      simpl.
      (* evaluate result [index - 1] *)
      econstructor.
      econstructor. econstructor. econstructor.
      eapply eval_Evar_global. auto. eauto.
      eapply deref_loc_reference. eauto.
      econstructor. econstructor. eapply eval_Evar_global.
      auto. eauto. econstructor. simpl. eauto.
      eauto. econstructor. simpl. unfold Cop.sem_sub. simpl.
      unfold Cop.sem_binarith. simpl. rewrite! sem_cast_int_int.
      eauto.
      simpl.
      unfold Cop.sem_add. simpl. rewrite Ptrofs.add_zero_l.
      eauto.
      econstructor. eapply eval_Evar_local. eapply Maps.PTree.gss.
      econstructor. simpl. eauto. eauto.
      simpl. rewrite sem_cast_int_int. eauto.
      econstructor. simpl. eauto.
      eauto.
      (* step5: evaluate index++ (copy from last case) *)
      eapply star_step;eauto. econstructor. simpl.
      econstructor.
      eapply star_step;eauto. econstructor. simpl.
      econstructor.
      eapply star_step;eauto. econstructor.     
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
      (* step6: call encrypt *)
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
      auto. eauto. econstructor. simpl. auto.
      eapply Mem.load_store_same;auto. eauto.
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
      econstructor.
      (* stack acc *)
      instantiate (1:= sp::lsp).
      instantiate (1:= injpw j m tm2 INJM).
      econstructor.
      eapply Hm. instantiate (1:= Hm). eauto.
      eapply stack_acc_compose_injp_acc. 
      eauto. eauto. eauto. eauto.
      reflexivity. eapply INJPM.
      econstructor. eauto. rewrite Ptrofs.add_zero. auto.
      (* match_kframe *)
      inv KFRM. econstructor. econstructor. econstructor.
      econstructor. eauto.              

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
      assert (H22: inject_incr f f0).
      eapply stack_acc_inject_incr. eapply KINJP. 
      (* introduce the memory produced by target memory *)
      exploit exec_request_mem3. eapply READIDX. eapply STORERES.
      eapply H12. eapply H22. eauto.
      eapply H12. eapply H22. eauto.
      instantiate (2:= tm). instantiate (1:= Hm).
      intros (tm1 & tm2 & tm3 & tm4 & sp & INJTM4 & ALLOCTM & STORETM1 & LOADTM2 & LOADSP & STORETM2 & FREETM3 & INJPTM4).
      (* introduce the state after executing the continuation *)
      exploit exec_kframe.
      2: { etransitivity. eapply INJP'. eapply INJPTM4. }
      eauto. eauto. instantiate (1:= se2).
      intros (tm5 & INJTM5 & s & REST).
      
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
      eapply star_step;eauto.
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
      instantiate (1:= s::nil).
      instantiate (1:= E0).
      destruct REST as (INJPTM5 & STAR & TOPS).
      destruct TOPS;subst;auto.
      eauto.
      eapply star_refl. eauto.

      (* match state *)
      destruct REST as (INJPTM5 & STAR & TOPS).
      destruct TOPS;subst.
      econstructor;eauto.
      econstructor;eauto.

    (* callencrypt *)
    + generalize Hse. intros Hse2.
      generalize INJP. intros INJP'.
      inv Hse. inv INJP.
      exploit (Genv.find_symbol_match H). eapply FINDP.
      intros (trb & FINDP3 & FINDSYMB).
      exploit (Genv.find_symbol_match H). eapply FINDK.
      intros (tkb & FINDP4 & FINDTKB).
      assert (INCR: inject_incr f f0).
      eapply stack_acc_inject_incr. eapply KINJP. 
      exploit find_request. eapply Hse2. eauto. eauto. eauto.
      intros FINDFUN.
      
      inv VINJ.
      generalize FINDP3. intros FINDP5.
      eapply INCR in FINDP3. eapply H12 in FINDP3.
      rewrite H4 in FINDP3. inv FINDP3.
      simpl. eexists. split.
      eapply plus_star_trans.
      econstructor. econstructor. simpl.
      econstructor;eauto.
      exploit Mem.loadv_inject;eauto. rewrite Ptrofs.add_zero.
      intros (v2 & LOADTM & VINJ). inv VINJ.
      eauto.
      (* at external *)
      eapply star_step;eauto. eapply step_push.
      econstructor. rewrite Ptrofs.add_zero_l.
      eapply find_request_server. eauto.
      instantiate (1 := true). simpl.
      rewrite Ptrofs.add_zero. unfold Genv.is_internal.      

      simpl in FINDFUN.
      simpl. 
      rewrite FINDFUN. eauto.
      simpl. rewrite Ptrofs.add_zero_l.
      replace (int__void_sg) with (Ctypes.signature_of_type (Ctypes.Tcons
            (Ctypes.Tint Ctypes.I32 Ctypes.Signed
               {| Ctypes.attr_volatile := false; Ctypes.attr_alignas := None |}) Ctypes.Tnil) Ctypes.Tvoid {| cc_vararg := None; cc_unproto := false; cc_structret := false |}) by auto.
      econstructor. eauto.
      unfold func_request. unfold ClientMR.func_request.
      unfold type_of_function. simpl.
      unfold Ctypesdefs.tint. unfold cc_default. auto.
      econstructor. econstructor. econstructor. econstructor.
      simpl. eapply Mem.sup_include_trans. eauto.
      eapply Mem.sup_include_trans. eapply stack_acc_sup_include2;eauto.
      eapply H11.
      eapply star_refl. eauto.
      eapply star_refl. eauto.

      (* match state *)
      econstructor;eauto.
      econstructor;eauto.
      
  - constructor. intros. inv H.

    
Admitted.
                                        
      
End WITH_N.
