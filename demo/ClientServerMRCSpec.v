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
| Callrequest (br: block) (sps : list block) (m:mem)
| Callencrypt (input : int) (sps: list block) (fptr : val) (m:mem)
| Return (m:mem).

Definition genv := Genv.t unit unit.

Section WITH_SE.
Context (se:Genv.symtbl).

Inductive initial_state : query li_c ->  state -> Prop :=
|initial_request br m fb
   (FIND: Genv.find_symbol se request_id = Some fb):
  initial_state (cq (Vptr fb Ptrofs.zero) intptr__void_sg ((Vptr br Ptrofs.zero) :: nil) m)
    (Callrequest br nil m)
|initial_encrypt i fb b ofs m
   (FIND: Genv.find_symbol se encrypt_id = Some fb):
  initial_state (cq (Vptr fb Ptrofs.zero) int_fptr__void_sg ((Vint i) :: (Vptr b ofs) :: nil) m)
    (Callencrypt i nil (Vptr b ofs) m).

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
| step_request1 input rb idb inb eb idx m m' sps b_r
  (FINDIDX: Genv.find_symbol se index_id = Some idb)
  (FINDREQ: Genv.find_symbol se request_id = Some rb)
  (FINDINPUT: Genv.find_symbol se input_id = Some inb)
  (FINDE: Genv.find_symbol se encrypt_id = Some eb)
  (READIDX: Mem.loadv Mint32 m (Vptr idb Ptrofs.zero) = Some (Vint idx))
  (COND: Int.eq idx Int.zero = true)
  (ADDIDX: Mem.storev Mint32 m (Vptr idb Ptrofs.zero) (Vint (Int.add idx Int.one)) = Some m')
  (READINPUT: Mem.loadv Mint32 m' (Vptr inb (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints idx))) = Some (Vint input)):
  step (Callrequest b_r sps m) E0 (Callencrypt input sps (Vptr rb Ptrofs.zero) m')
| step_request2 r input rb idb inb rsb eb idx m m' m'' sp sps
  (FINDIDX: Genv.find_symbol se index_id = Some idb)
  (FINDREQ: Genv.find_symbol se request_id = Some rb)
  (FINDINPUT: Genv.find_symbol se input_id = Some inb)
  (FINDRES: Genv.find_symbol se result_id = Some rsb)
  (FINDE: Genv.find_symbol se encrypt_id = Some eb)
  (READR: Mem.loadv Mint32 m (Vptr sp Ptrofs.zero) = Some (Vint r))
  (READIDX: Mem.loadv Mint32 m (Vptr idb Ptrofs.zero) = Some (Vint idx))
  (COND: Int.lt Int.zero idx && Int.lt idx Nint = true)
  (STORERES: Mem.storev Mint32 m (Vptr rsb (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.sub idx (Int.repr 1))))) (Vint r) = Some m')
  (ADDIDX: Mem.storev Mint32 m' (Vptr idb Ptrofs.zero) (Vint (Int.add idx Int.one)) = Some m'')
  (* 4 * (index - 1) *)
  (READINPUT: Mem.loadv Mint32 m'' (Vptr inb (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints idx))) = Some (Vint input)):
  step (Callrequest sp sps m) E0 (Callencrypt input sps (Vptr rb Ptrofs.zero) m'')
| step_request3 r idb rsb idx m m' m'' sps b_r
  (FINDIDX: Genv.find_symbol se index_id = Some idb)
  (FINDRES: Genv.find_symbol se result_id = Some rsb)
  (READR: Mem.loadv Mint32 m (Vptr b_r Ptrofs.zero) = Some (Vint r))
  (READIDX: Mem.loadv Mint32 m (Vptr idb Ptrofs.zero) = Some (Vint idx))
  (COND: Int.cmp Cge idx Nint = true)
  (STORERES: Mem.storev Mint32 m (Vptr rsb (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.sub idx (Int.repr 1))))) (Vint r) = Some m')
  (FREE: Mem.free_list m' (map (fun b => (b,0,8)) sps) = Some m''):
  step (Callrequest b_r sps m) E0 (Return m'')
| step_encrypt kb rb key input m m' m'' output sp sps
   (FINDK: Genv.find_symbol se key_id = Some kb)
   (FINDRE: Genv.find_symbol se request_id = Some rb)
   (ALLOC: Mem.alloc m 0 8 = (m', sp))
   (READ: Mem.loadv Mint32 m' (Vptr kb Ptrofs.zero) = Some (Vint key))
   (STORE: Mem.storev Many64 m' (Vptr sp Ptrofs.zero) (Vint output) = Some m'')
   (XOR: output = Int.xor input key):
  step (Callencrypt input sps (Vptr rb Ptrofs.zero) m) E0 (Callrequest sp (sp :: sps) m'').

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
(*
Inductive stack_acc_request (w: injp_world) : injp_world -> list block -> Prop :=
| stack_acc_nil w':
  injp_acc w w' ->
  stack_acc_request w w' nil
| stack_acc_cons f1 m1 tm1 w1 (Hm1: Mem.inject f1 m1 tm1) lsp tm1' tm1'' sp Hm1' w2 r
    (Hm1: Mem.inject f1 m1 tm1)
    (WORLD1: w1 = injpw f1 m1 tm1 Hm1)
    (STKB: stack_acc_request w w1 lsp)
    (* (INJP1: injp_acc w w1) *)
    (ALLOC: Mem.alloc tm1 0 4 = (tm1', sp))
    (STORESP: Mem.store Mint32 tm1' sp 0 (Vint r) = Some tm1'')
    (INJP2: injp_acc (injpw f1 m1 tm1'' Hm1') w2):
  stack_acc_request w w2 (sp::lsp).
 *)

Definition initial_tm := match w with injpw _ _ tm _ => tm end.

Inductive match_kframe_request : meminj -> list block -> list block -> list (frame L) -> Prop :=
| match_kframe_request_nil j:
  match_kframe_request j nil nil nil
| match_kframe_request_cons lsp_re lsp_en m fb k sp_en tsp_en j:
  match_kframe_encrypt j lsp_re lsp_en k ->
  j sp_en = Some (tsp_en,0) -> 
  match_kframe_request j lsp_re (sp_en :: lsp_en) ((st L false (Call2 fb tsp_en m)) :: k)
                       
with match_kframe_encrypt : meminj -> list block -> list block -> list (frame L) -> Prop :=
| match_kframe_encrypt_nil j:
  match_kframe_encrypt j nil nil nil
| match_kframe_encrypt_cons m fb vargs k le lsp_re lsp_en sp_re j:
  match_kframe_request j lsp_re lsp_en k ->
  (forall b d, ~ j b = Some (sp_re,d)) -> ~In sp_re lsp_re -> ~Mem.valid_block initial_tm sp_re ->
  match_kframe_encrypt j (sp_re::lsp_re) lsp_en (st L true (Callstate fb vargs (Kcall None func_request (Maps.PTree.set r_id (sp_re, tintp) empty_env) le Kstop) m) :: k).

Inductive frames_request_freeable : mem -> list block -> Prop :=
|frames_request_freeable_nil tm:
  frames_request_freeable tm nil
|frames_request_freeable_cons tm sp lsp_re:
  frames_request_freeable tm lsp_re ->
  Mem.range_perm tm sp 0 8 Cur Freeable ->
  frames_request_freeable tm (sp:: lsp_re).
                          
(*TODO: need to use a invariant link stack_acc to keep the injection relation of stack block of encrypt *)
Inductive match_state: state -> list (frame L) -> Prop :=
| match_request_intro j rb rb' m tm ks b_r tb_r lsp_re lsp_en delta
    (Hm: Mem.inject j m tm)
    (* (KINJP: stack_acc w w1 lsp) *)
    (INJP: injp_acc w (injpw j m tm Hm))
    (FINDP: Genv.find_symbol se request_id = Some rb)
    (RINJ: j b_r = Some (tb_r, delta))
    (FINJ: j rb = Some (rb',0))
    (KFRM: match_kframe_request j lsp_re lsp_en ks)
    (FREEABLE: frames_request_freeable tm lsp_re):
  match_state (Callrequest b_r lsp_en m) ((st L true (Callstate (Vptr rb' Ptrofs.zero) (Vptr tb_r (Ptrofs.repr delta) :: nil) Kstop tm)) :: ks)
| match_encrypt_intro j v tv m tm input ks lsp_re lsp_en
    (Hm: Mem.inject j m tm)
    (* (KINJP: stack_acc w w1 lsp) *)
    (INJP: injp_acc w (injpw j m tm Hm))
    (VINJ: Val.inject j v tv)
    (KFRM: match_kframe_encrypt j lsp_re lsp_en ks)
    (FREEABLE: frames_request_freeable tm lsp_re):
  match_state (Callencrypt input lsp_en v m) ((st L false (Call1 tv input tm)) :: ks)
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
  intros. cbn. rewrite pred_dec_true; eauto.
  unfold global_definitions_client. unfold Genv.find_funct_ptr.
  rewrite Genv.find_def_spec.
  eapply Genv.find_symbol_match in H; eauto.
  destruct H as [tb' [A B]]. rewrite A in H1. inv H1.
  apply Genv.find_invert_symbol in B. cbn.
  rewrite B. rewrite Maps.PTree.gso.
  rewrite Maps.PTree.gso.
  rewrite Maps.PTree.gso.
  rewrite Maps.PTree.gss. reflexivity.
  unfold request_id, input_id. congruence.
  unfold request_id, result_id. congruence.
  unfold request_id, index_id. congruence.
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
  rewrite Maps.PTree.gso.
  rewrite Maps.PTree.gss. reflexivity.
  unfold encrypt_id, request_id. congruence.
  unfold encrypt_id, input_id. congruence.
  unfold encrypt_id, result_id. congruence.
  unfold encrypt_id, index_id. congruence.
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

Lemma find_request_server:
  forall rb',
  Genv.find_symbol tge2 request_id = Some rb' ->
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
  unfold request_id in *. rewrite H.
  unfold NMap.get. rewrite NMap.gss.
  auto.
Qed.

End MS.

Lemma freeable_perm_nodec: forall lsp tm tm',
    frames_request_freeable tm lsp ->
    (forall b ofs k p, Mem.perm tm b ofs k p -> Mem.perm tm' b ofs k p) ->
    frames_request_freeable tm' lsp.
Proof.
  induction 1; intros. constructor.
  constructor. eapply IHframes_request_freeable; eauto.
  red. intros. eauto.
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
Proof.
  unfold Nint.
  intros. simpl in H.
  destruct Int.eq eqn:EQ;try congruence.
  exploit Int.eq_spec. rewrite EQ. intros. subst.
  unfold Int.lt in *. unfold Int.zero in H.
  rewrite! Int.signed_repr in H.
  destruct zlt eqn: LT1 in H;simpl in H;try congruence. lia.
  generalize Int.min_signed_neg. intros. lia.
  generalize Int.min_signed_neg. intros.
  generalize  Int.max_signed_pos. lia.
Qed.  
  
  
(* idx == 0 *)
Lemma exec_request_mem1:
  forall ib tib sm sm1 tm idx idx' j inb ofs input tinb trb delta,
    Mem.loadv Mint32 sm (Vptr ib Ptrofs.zero) = Some (Vint idx) ->
    Mem.storev Mint32 sm (Vptr ib Ptrofs.zero) (Vint idx') = Some sm1 ->
    Mem.loadv Mint32 sm1 (Vptr inb ofs) = Some (Vint input) ->
    Mem.inject j sm tm ->
    j ib = Some (tib,0) ->
    j inb = Some (tinb,0) ->
    exists tm1 sp tm2 tm3 Hm Hm',
      Mem.alloc tm 0 8 = (tm1, sp) /\
        Mem.storev Mptr tm1 (Vptr sp Ptrofs.zero) (Vptr trb (Ptrofs.repr delta)) = Some tm2 /\
        Mem.storev Mint32 tm2 (Vptr tib Ptrofs.zero) (Vint idx') = Some tm3 /\
        Mem.loadv Mint32  tm2 (Vptr tib Ptrofs.zero) = Some (Vint idx) /\
        Mem.loadv Mint32  tm3 (Vptr tib Ptrofs.zero) = Some (Vint idx') /\
        Mem.loadv Mint32 tm3 (Vptr tinb ofs) = Some (Vint input) /\
        (* Mem.unchanged_on (fun b ofs => b = tib -> ~ 0 <= ofs < 4) tm tm3 /\ *)
        injp_acc (injpw j sm tm2 Hm) (injpw j sm1 tm3 Hm').
Proof.
  intros until delta.
  intros LOADSM STORESM LOADSM1 INJ INJIB INJINB.
  destruct (Mem.alloc tm 0 8) as [tm1 sp] eqn:ALLOCTM.
  exploit Mem.alloc_right_inject;eauto.
  intros INJ1.
  exists tm1,sp.
  assert (STORETM1: {tm2:mem| Mem.store Mptr tm1 sp 0 (Vptr trb (Ptrofs.repr delta)) = Some tm2}).
  eapply Mem.valid_access_store. unfold Mem.valid_access.
  split. red. intros.
  eapply Mem.perm_implies.
  eapply Mem.valid_access_alloc_same;eauto.
  lia. unfold Mptr. replace Archi.ptr64 with true by reflexivity. simpl. lia. apply Z.divide_0_r.
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

Lemma load_result_Mptr_eq:
    forall v, v <> Vundef -> Val.has_type v Tptr ->
         Val.load_result Mptr v = v.
Proof.
  intros. unfold Mptr. cbn.
  unfold Tptr in H0. replace Archi.ptr64 with true in * by reflexivity.
  destruct v; cbn in *; eauto; try congruence; eauto.
  inv H0. inv H0. inv H0.
Qed.
    
(* 0 < index < N *)
Lemma exec_request_mem2:
  forall ib tib sm sm1 sm2 tm idx idx' idx'' j r ofs1 ofs2 inb tinb input resb tresb rb trb d,
    Mem.loadv Mint32 sm (Vptr ib Ptrofs.zero) = Some (Vint idx) ->
    Mem.loadv Mint32 sm (Vptr rb Ptrofs.zero) = Some (Vint r) ->
    Mem.storev Mint32 sm (Vptr resb ofs1) (Vint r) = Some sm1 ->
    Mem.loadv Mint32 sm1 (Vptr ib Ptrofs.zero) = Some (Vint idx') ->
    Mem.storev Mint32 sm1 (Vptr ib Ptrofs.zero) (Vint idx'') = Some sm2 ->
    Mem.loadv Mint32 sm2 (Vptr inb ofs2) = Some (Vint input) ->
    Mem.inject j sm tm ->
    j rb = Some (trb,d) ->
    j ib = Some (tib,0) ->
    j inb = Some (tinb,0) ->
    j resb = Some (tresb,0) ->
    exists tm1 sp tm2 tm3 tm4 Hm Hm',
      Mem.alloc tm 0 8 = (tm1, sp) /\
        Mem.storev Mptr tm1 (Vptr sp Ptrofs.zero) (Vptr trb (Ptrofs.repr d)) = Some tm2 /\
        Mem.loadv Mint32 tm2 (Vptr tib Ptrofs.zero) = Some (Vint idx) /\
        Mem.loadv Mptr tm2 (Vptr sp Ptrofs.zero) = Some (Vptr trb (Ptrofs.repr d)) /\
        Mem.loadv Mint32 tm2 (Vptr trb (Ptrofs.repr d)) = Some (Vint r) /\
        Mem.storev Mint32 tm2 (Vptr tresb ofs1) (Vint r) = Some tm3 /\
        Mem.loadv Mint32 tm3 (Vptr tib Ptrofs.zero) = Some (Vint idx') /\
        Mem.storev Mint32 tm3 (Vptr tib Ptrofs.zero) (Vint idx'') = Some tm4 /\
        Mem.loadv Mint32 tm4 (Vptr tinb ofs2) = Some (Vint input) /\
        injp_acc (injpw j sm tm2 Hm) (injpw j sm2 tm4 Hm').
Proof.
  intros until d.
  intros LOADIDX LOADR STORERES LOADIDX1 STOREIDX LOADIN INJ INJRB INJIDX INJIN INJRES.
  destruct (Mem.alloc tm 0 8) as [tm1 sp] eqn:ALLOCTM.
  exists tm1,sp.
  (* inject j sm tm1 *)
  exploit Mem.alloc_right_inject;eauto.
  intros INJ1.
  assert (STOREM: {tm2: mem | Mem.store Mptr tm1 sp 0 (Vptr trb (Ptrofs.repr d)) = Some tm2}).
  eapply Mem.valid_access_store. eapply Mem.valid_access_implies.
  eapply Mem.valid_access_alloc_same;eauto. lia. unfold Mptr.
  replace Archi.ptr64 with true by reflexivity. simpl. lia. simpl.
  eapply Z.divide_0_r. econstructor.
  destruct STOREM as (tm2 & STOREDPTR').
  exists tm2.
  (* inject j sm tm2 *)
  exploit Mem.store_outside_inject;eauto.
  intros. eapply Mem.fresh_block_alloc;eauto.
  eapply Mem.valid_block_inject_2;eauto.
  intros INJ2.
  exploit Mem.loadv_inject. eapply INJ2.
  eapply LOADIDX. eapply Val.inject_ptr. eauto.
  rewrite Ptrofs.add_zero_l. eauto.
  intros (v2 & LOADIDX' & VINJ). inv VINJ.
  exploit Mem.load_store_same. eapply STOREDPTR'.
  intros LOADDPTR'.
  exploit Mem.loadv_inject. eapply INJ2.
  eapply LOADR. eapply Val.inject_ptr. eauto.
  rewrite Ptrofs.add_zero_l. eauto.
  intros (v2 & LOADR' & VINJ). inv VINJ.
  (* store tm2 *)
  exploit Mem.storev_mapped_inject. eapply INJ2.
  eauto. eapply Val.inject_ptr. eauto. eauto.
  eapply Val.inject_int. intros (tm3 & STORERES' & INJ3).
  rewrite Ptrofs.add_zero in STORERES'.
  exists tm3.
  exploit Mem.loadv_inject. eapply INJ3.
  eauto. eapply Val.inject_ptr. eauto.
  rewrite Ptrofs.add_zero_l. eauto.
  intros (v2 & LOADIDX1' & VINJ). inv VINJ.
  (* store tm3 *)
  exploit Mem.storev_mapped_inject. eapply INJ3.
  eauto. eapply Val.inject_ptr. eauto. eauto.
  eapply Val.inject_int. intros (tm4 & STOREIDX' & INJ4).
  rewrite Ptrofs.add_zero_l in STOREIDX'.
  exists tm4,INJ2,INJ4.
  exploit Mem.loadv_inject. eapply INJ4.
  eauto. eapply Val.inject_ptr. eauto.
  rewrite Ptrofs.add_zero. eauto.
  intros (v2 & LOADIN' & VINJ). inv VINJ. 
  do 9 (try split;eauto).
  etransitivity.
  eapply injp_acc_storev;eauto.
  eapply Val.inject_ptr. eauto. rewrite Ptrofs.add_zero. auto.
  instantiate (1:= INJ3).
  eapply injp_acc_storev;eauto.
Qed.
  

(* idnex >= N *)
Lemma exec_request_mem3:
  forall ib tib sm sm1 tm idx r j ofs1 resb tresb rb trb d (Hm:Mem.inject j sm tm),
    Mem.loadv Mint32 sm (Vptr ib Ptrofs.zero) = Some (Vint idx) ->
    Mem.loadv Mint32 sm (Vptr rb Ptrofs.zero) = Some (Vint r) ->
    Mem.storev Mint32 sm (Vptr resb ofs1) (Vint r) = Some sm1 ->
    j ib = Some (tib,0) ->
    j resb = Some (tresb,0) ->
    j rb = Some (trb, d) ->
    exists tm1 tm2 tm3 tm4 sp Hm1,
      Mem.alloc tm 0 8 = (tm1, sp) /\
        Mem.storev Mptr tm1 (Vptr sp Ptrofs.zero) (Vptr trb (Ptrofs.repr d)) = Some tm2 /\
        Mem.loadv Mint32  tm2 (Vptr tib Ptrofs.zero) = Some (Vint idx) /\
        Mem.loadv Mptr tm2 (Vptr sp Ptrofs.zero) = Some (Vptr trb (Ptrofs.repr d)) /\
        Mem.loadv Mint32 tm2 (Vptr trb (Ptrofs.repr d)) = Some (Vint r) /\
        Mem.storev Mint32 tm2 (Vptr tresb ofs1) (Vint r) = Some tm3 /\
        Mem.free tm3 sp 0 8 = Some tm4 /\
        (* Mem.unchanged_on (fun b ofs => b = tresb -> ~ (Ptrofs.signed ofs1) <= ofs < (Ptrofs.signed ofs1 + 4)) tm tm4 /\ *)
        injp_acc (injpw j sm tm Hm) (injpw j sm1 tm4 Hm1).
Proof.
  intros until Hm.
  intros LOADIDX LOADR STORER INJIDX INJRES INJR.
  destruct (Mem.alloc tm 0 8) as [tm1 sp] eqn: ALLOC.
  exists tm1.
  exploit Mem.alloc_right_inject;eauto. intros INJ1.
  assert (STOREM: {m2: mem | Mem.store Mptr tm1 sp 0 (Vptr trb (Ptrofs.repr d)) = Some m2}).
  eapply Mem.valid_access_store. eapply Mem.valid_access_implies.
  eapply Mem.valid_access_alloc_same;eauto. lia. unfold Mptr. simpl.
  replace Archi.ptr64 with true by reflexivity. simpl. lia.
  eapply Z.divide_0_r. econstructor.
  destruct STOREM as (tm2 & STORERPTR').
  exists tm2.
  (* inject sm tm2 *)
  exploit Mem.store_outside_inject;eauto.
  intros. eapply Mem.fresh_block_alloc;eauto.
  eapply Mem.valid_block_inject_2;eauto.
  intros INJ2.
  (* loadv index from tm2 *)
  exploit Mem.loadv_inject. eapply INJ2. eapply LOADIDX.
  eapply Val.inject_ptr;eauto.
  intros (v2 & LOADIDX' & VINJ). inv VINJ.
  (* loadv sp from tm2 *)
  exploit Mem.load_store_same. eapply STORERPTR'.
  intros LOADRPTR. simpl in LOADRPTR.
  rewrite load_result_Mptr_eq in LOADRPTR; eauto. 2: congruence. 2: constructor.
  (* loadv value from *r *)
  exploit Mem.loadv_inject. eapply INJ2. eapply LOADR.
  eapply Val.inject_ptr;eauto.
  intros (v2 & LOADR' & VINJ). inv VINJ. rewrite Ptrofs.add_zero_l in LOADR'.
  (* store result *)
  exploit Mem.store_mapped_inject. eapply INJ2.
  eapply STORER. eauto. eapply Val.inject_int.
  intros (tm3 & STORER' & INJ3).
  exists tm3.
  (* free *)
  assert (FREE: {tm4:mem | Mem.free tm3 sp 0 8 = Some tm4}).
  eapply Mem.range_perm_free.
  unfold Mem.range_perm. intros .
  eapply Mem.perm_store_1;eauto.
  eapply Mem.perm_store_1;eauto.
  eapply Mem.perm_alloc_2;eauto.
  destruct FREE as (tm4 & FREE).
  exists tm4, sp.
  (* inject sm1 tm4 *)
  exploit Mem.free_right_inject. eapply INJ3. eauto.
  intros. eapply Mem.fresh_block_alloc;eauto.
  eapply Mem.valid_block_inject_2;eauto.
  intros INJ4.
  exists INJ4.
  rewrite Z.add_0_r in STORER'.
  repeat apply conj; eauto.
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
  exploit Mem.store_valid_access_3. eapply STORER.
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

Lemma freeframe_other: forall lsp b tm lo hi tm',
    frames_request_freeable tm lsp -> Mem.free tm b lo hi = Some tm' ->
    ~ In b lsp -> frames_request_freeable tm' lsp.
Proof.
  induction lsp; intros. constructor.
  inv H. constructor. eapply IHlsp; eauto.
  intro. apply H1. right. eauto.
  red. intros. eapply Mem.perm_free_1; eauto.
  left. intro. apply H1. left. eauto.
Qed.

Lemma matchframe_outofreach: forall w lsp_re j lsp_en k tb,
    match_kframe_request w j lsp_re lsp_en k ->
    In tb lsp_re ->
    (forall b d, ~j b = Some (tb,d)).
Proof.
  induction lsp_re; intros.
  - inv H. inv H0. inv H1. inv H0.
  - inv H. inv H1.
    destruct H0. subst. eauto.
    eapply IHlsp_re; eauto.
Qed.

Lemma exec_kframe: forall lsp_en lsp_re w m tm j Hm  ks se m',
    injp_acc w (injpw j m tm Hm) ->
    match_kframe_request w j lsp_re lsp_en ks ->
    Mem.free_list m (map (fun b => (b,0,8)) lsp_en) = Some m' ->
    frames_request_freeable tm lsp_re ->
    exists tm' Hm' s,
      injp_acc w (injpw j m' tm' Hm') /\
        star (fun _ : unit => SmallstepLinking.step L se) tt
          (st L true (Returnstate Vundef Kstop tm) :: ks) E0 (s :: nil) /\
        (s = st L true (Returnstate Vundef Kstop tm') \/
           s = st L false (Return2 tm')).
Proof.
  induction lsp_en; intros.
  - (* only returnstate *)
    inv H1. inv H0. inv H2.
    exists tm,Hm. eexists.
    split. eauto. 
    split. eapply star_refl.
    eauto.
  - (* returnstate::call2 *)
    inv H0. simpl in H1. destruct (Mem.free m a 0 8) eqn:FREE_EN; try congruence.
    exploit Mem.free_parallel_inject; eauto. simpl. intros (tm' & FREE_EN' & Hm').
    exploit injp_acc_free. replace 8 with (0 + 8) in FREE_EN by lia. eauto.
    instantiate (2:=0). simpl. eauto. eauto. instantiate (1:= Hm').
    instantiate (1:= Hm). intro ACCF.
    inv H7.
    + (*ks = nil*)
      inv H2. simpl in H1. inv H1.
      exists tm', Hm'. eexists.
      split. etransitivity; eauto.
      split. eapply star_step. eapply step_pop. econstructor.
      econstructor. eapply star_step. simpl. econstructor.
      simpl. econstructor. eauto. eapply star_refl. eauto. eauto.
      right. eauto.
    + (*ks <> nil, IH case *)
      inv H2.
      assert (RNGP: Mem.range_perm tm' sp_re 0 8 Cur Freeable).
      red. intros. eapply Mem.perm_free_1; eauto.
      left. intro. subst. eapply H3; eauto.
      apply Mem.range_perm_free in RNGP as FREE.
      destruct FREE as (tm'' & FREE_RE').
      exploit Mem.free_right_inject; eauto.
      intros. eapply H3; eauto.
      intros Hm''.
      assert (ACCF2: injp_acc w (injpw j m1 tm'' Hm'')).
      {
        inv H. inv ACCF.
        constructor; eauto.
        - eapply Mem.ro_unchanged_trans; eauto.
          inversion H15. eauto.
        - eapply Mem.ro_unchanged_trans; eauto.
          eapply Mem.ro_unchanged_trans; eauto.
          eapply Mem.ro_unchanged_free; eauto.
          inversion H26. eauto. inversion H17. eauto.
        - red. intros. eapply H13; eauto.
          eapply H23; eauto. inversion H15.
          eapply unchanged_on_support; eauto.
        - red. intros. eapply H14; eauto.
          eapply H24; eauto. inversion H17.
          eapply unchanged_on_support; eauto.
          eapply Mem.perm_free_3; eauto.
        - eapply Mem.unchanged_on_implies.
          eapply Mem.unchanged_on_trans. 2: eauto.
          eapply Mem.unchanged_on_implies. eauto.
          intros. red. red in H. destruct (f b) as [[b' d]|] eqn:Hf.
          apply H18 in Hf. congruence. eauto.
          intros. red. red in H.
          destruct (j b) as [[b' d]|] eqn:Hj; eauto.  
          exploit H19; eauto. intros [A B]. congruence.
        - assert (Mem.unchanged_on (loc_out_of_reach f m3) m4 tm').
          { eapply mem_unchanged_on_trans_implies_valid. eauto.
          eauto.
          intros.
          intros. eapply loc_out_of_reach_incr; eauto.
          eapply inject_implies_dom_in; eauto. }
          eapply mem_unchanged_on_trans_implies_valid. eauto.
          instantiate (1:= fun b ofs => b <> sp_re).
          eapply Mem.free_unchanged_on; eauto.
          intros. red. intros. subst.
          simpl in H5. congruence.
      }
      exploit IHlsp_en. apply ACCF2. eauto. eauto.
      eapply freeframe_other. 2: eauto.
      eapply freeframe_other; eauto.
      intro.
      eapply matchframe_outofreach in H0. 2: eauto. apply H0. eauto.
      eauto.
      intros (tm''' & Hm''' & s & A & B & C).
      exists tm''', Hm''', s. split. eauto.

      (*steps *)
      split. 2: eauto.
      eapply star_step. eapply step_pop. econstructor.
      econstructor. eapply star_step. simpl. econstructor.
      econstructor. eauto. eapply star_step. simpl.
      eapply step_pop. econstructor. econstructor.
      eapply star_step. simpl. econstructor. econstructor.
      eapply star_step. econstructor. econstructor.
      reflexivity. simpl. replace Archi.ptr64 with true by reflexivity.
      rewrite FREE_RE'. reflexivity.
      eapply B. all: eauto.
Qed.

Lemma match_frame_incr: forall w lsp_re lsp_en ks j j',
          match_kframe_encrypt w j lsp_re lsp_en ks ->
          inject_incr j j' -> (forall b tb d, In tb lsp_re -> j' b = Some (tb,d) <-> j b = Some (tb,d)) ->
          match_kframe_encrypt w j' lsp_re lsp_en ks.
Proof.
  induction lsp_re; intros. inv H. constructor.
  inv H. constructor. inv H4. constructor.
  constructor. eapply IHlsp_re; eauto.
  intros. eapply H1. right. eauto.
  apply H0. eauto.
  intros. intro.
  assert (In a ((a :: lsp_re))). left. eauto.
  eapply H1 in H2. eapply H2 in H. eapply H5. eauto.
  eauto. eauto.
Qed.

Lemma freeable_valid : forall tm lsp_re b,
    frames_request_freeable tm lsp_re ->
    In b lsp_re ->
    Mem.valid_block tm b.
Proof.
  induction lsp_re; intros. inv H0.
  inv H. destruct H0. subst.
  eapply Mem.perm_valid_block; eauto. eapply H5. instantiate (1:= 0). lia.
  eapply IHlsp_re; eauto.
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
    + subst. setoid_rewrite find_request;eauto.
      (* cbn. econstructor;eauto.      *)
   + destruct (peq i 1).
     ++ subst i.
        exploit find_encrypt. 2: eauto.
        instantiate (1:=se2). instantiate (1 := f0). eauto.
        eauto. intros.
        rewrite H0.
        unfold fundef_is_internal. simpl. eapply orb_true_r.
     ++ unfold Genv.find_funct.
        destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero);try congruence.
        unfold Genv.find_funct_ptr.
        assert (FIND_DEF_CLIENT: forall f, Genv.find_def (Genv.globalenv se2 (Ctypes.program_of_program client)) b2 <> Some (Gfun f)).
         { unfold Genv.globalenv. simpl.
           intros.
           unfold Genv.add_globdef.
           (* destruct all the get *)
           simpl.

           (* se2 b2 = i *)
           assert (A: Maps.PTree.get i (Genv.genv_symb se2) = Some b2).
           erewrite <- Genv.mge_symb. 2: eapply H2.
           eauto. eauto.
           (* restore the naming *)
           destruct Maps.PTree.get as [db1|] eqn:? at 1;unfold Maps.PTree.prev in *; simpl in *;
             destruct Maps.PTree.get as [db2|] eqn:? at 1;unfold Maps.PTree.prev in *; simpl in *;
             destruct Maps.PTree.get as [db3|] eqn:? at 1;unfold Maps.PTree.prev in *; simpl in *;
             destruct Maps.PTree.get as [db4|] eqn:? at 1;unfold Maps.PTree.prev in *; simpl in *;
             destruct Maps.PTree.get as [db5|] eqn:? at 1;unfold Maps.PTree.prev in *; simpl in *.           
           all :try assert (NEQ1: b2 <> db2) by (unfold not; intros; subst; exploit Genv.genv_vars_inj;[eapply A | eauto | eauto]; intros; congruence);
             try assert (NEQ2: b2 <> db3) by (unfold not; intros; subst; exploit Genv.genv_vars_inj;[eapply A | eauto | eauto]; intros; congruence).
           
           1-16: setoid_rewrite NMap.gsspec;destruct NMap.elt_eq;try congruence.
           1-8,17-24: unfold NMap.get;erewrite NMap.gso;eauto.
           1-4,9-12,17-20,25-28: unfold NMap.get;erewrite NMap.gso;eauto.
           1,2,5,6,9,10,13,14,17,18,21,22,25,26,29,30: setoid_rewrite NMap.gsspec;destruct NMap.elt_eq;try congruence.
           1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31: setoid_rewrite NMap.gsspec;destruct NMap.elt_eq;try congruence.
           all: unfold NMap.get;rewrite NMap.gi;congruence. }

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
           | 3%positive | 1%positive => true
           | _ => false
                      end = false).
         { destruct i;try congruence;destruct i;try congruence;auto;destruct i;try congruence;auto. }
         rewrite RHS.

         destruct Genv.find_def eqn:?. destruct g. specialize (FIND_DEF_CLIENT f). contradiction.
         destruct Genv.find_def eqn:? at 1. destruct g. rewrite Heqo0 in FIND_DEF_SERVER. specialize (FIND_DEF_SERVER f). contradiction.
         auto. auto.
         destruct Genv.find_def eqn:? at 1. destruct g. rewrite Heqo0 in FIND_DEF_SERVER. specialize (FIND_DEF_SERVER f). contradiction.
         auto. auto.         
        
  - intros q1 q2 s1 Hq Hi1. inv Hq. inv H1. inv Hi1; cbn in *.
    + (* initial request *)
      inv Hse.
      eapply Genv.find_symbol_match in H5 as FIND'; eauto.
      destruct FIND' as [fb' [FINJ FIND']]. inv H.
      inv H0. inv H7. inv H3.
      rewrite FINJ in H4. inv H4. rename b2 into fb'. rewrite Ptrofs.add_zero.
      exploit find_request;eauto. 
      intro FINDR.
      exists ((st L true (Callstate (Vptr fb' Ptrofs.zero) ((Vptr b0 (Ptrofs.repr delta0)) :: nil) Kstop m2)) :: nil).
      split. split.
      -- simpl. unfold Genv.is_internal. setoid_rewrite FINDR. reflexivity.
      -- simpl.
       set (targs := (Ctypes.Tcons tintp Ctypes.Tnil)).
       assert (Ctypes.signature_of_type targs Ctypes.Tvoid cc_default = intptr__void_sg).
       reflexivity.
       rewrite <- H. rewrite Ptrofs.add_zero_l.
       econstructor; eauto.
       constructor; cbn; eauto. constructor; eauto. constructor.
      -- eapply match_request_intro; eauto.  reflexivity. econstructor; eauto.
         constructor.
    + (* initial encrypt *)
      inv Hse.
      eapply Genv.find_symbol_match in H5 as FIND'; eauto.
      destruct FIND' as [fb' [FINJ FIND']]. inv H.
      inv H0. inv H7. inv H3. inv H10.
      rewrite FINJ in H4. inv H4. rename b2 into fb'. rewrite Ptrofs.add_zero.
      exploit find_encrypt;eauto. intro FINDE.
      exists ((st L false (Call1 v'0 i m2)) :: nil).
      split. split.
      -- simpl. unfold Genv.is_internal.
         setoid_rewrite find_encrypt; eauto.
      -- simpl. inv H1. econstructor; eauto.
      -- inv H1.
         econstructor;eauto. reflexivity.
         constructor. constructor.
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
      eapply Genv.match_stbls_incr in H; eauto.
      2: { intros. exploit H15; eauto. intros [A B].
           split; intro. apply A. apply H0. eauto.
           apply B. apply H1. eauto. }
      exploit (Genv.find_symbol_match H). eapply FINDP.
      intros (trb & FINDP3 & FINDSYMB).
      rewrite FINDREQ in FINDP. inv FINDP.
      exploit (Genv.find_symbol_match H). eapply FINDIDX.
      intros (tidb & FINDP4 & FINDTIDB).
      exploit (Genv.find_symbol_match H). eapply FINDINPUT.
      intros (tinb & FINDP5 & FINDINB).
      exploit find_encrypt';eauto.
      intros (teb & FINDP6 & FINDTEB & FINDENC).
            
(*      (* stack_acc implies inject_incr *)
      assert (H22: inject_incr f f0).
      eapply stack_acc_inject_incr. eapply KINJP. *)
      (* introduce the memory produced by target memory *)
      exploit (exec_request_mem1). eapply READIDX. eapply ADDIDX. eapply READINPUT. eapply Hm.
      eauto. eauto.
      intros (tm1 & sp & tm2 & tm3 & INJM & INJM' & ALLOCTM & STORETM1 & STORETM2 & LOADTM2 & LOADIDXTM3 & LOADINPUTTM3 & INJPM).
      (* step1 : evaluate the function entry *)
      simpl. eexists. split.
      eapply plus_star_trans.
      econstructor. econstructor. simpl.      
      (* step_internal *)
      econstructor. eapply find_request; eauto.
      (* function entry *)    
      econstructor; simpl.
      constructor; eauto. constructor.
      econstructor; eauto. simpl. replace Archi.ptr64 with true by reflexivity.
      eauto.
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
      instantiate (1:= INJM').
      etransitivity. 2: eauto.
      etransitivity. eauto.
      assert (ro_acc tm tm2). eapply ro_acc_trans.
      eapply ro_acc_alloc; eauto. eapply ro_acc_store; eauto.
      inv H2.
      constructor; eauto with mem. red. eauto.
      set (P:= fun b (ofs:Z) => b <> sp).
      eapply Mem.unchanged_on_implies. instantiate (1:= P).
      eapply Mem.unchanged_on_trans.
      eapply Mem.alloc_unchanged_on; eauto.
      eapply Mem.store_unchanged_on; eauto.
      intros. unfold P. intro. subst.
      apply Mem.fresh_block_alloc in ALLOCTM.
      congruence. red. intros. congruence.
      econstructor; eauto.
      (* stack acc *)
      (* instantiate (1:= sp::lsp).
      instantiate (1:= injpw j m tm2 INJM).
      econstructor.
      eapply Hm. instantiate (1:= Hm). eauto.
      eapply stack_acc_compose_injp_acc. 
      eauto. eauto. eauto. eauto.
      reflexivity. eapply INJPM.
      econstructor. eauto. rewrite Ptrofs.add_zero. auto.
       *)
      (* match_kframe *)
      instantiate (1:= sp :: lsp_re).
      econstructor; eauto.
      clear - Hm'0 ALLOCTM. inv Hm'0.
      intros. intro. exploit mi_mappedblocks; eauto.
      intro. eapply Mem.fresh_block_alloc; eauto.
      intro. eapply freeable_valid in FREEABLE; eauto.
      eapply Mem.fresh_block_alloc; eauto.
      simpl. intro. eapply Mem.fresh_block_alloc.
      eauto. inversion H13. apply unchanged_on_support. eauto.
      econstructor.
      clear - FREEABLE KFRM ALLOCTM STORETM1 STORETM2.
      assert (forall b ofs k p, Mem.perm tm b ofs k p -> Mem.perm tm3 b ofs k p).
      intros. eauto with mem.
      eapply freeable_perm_nodec; eauto.
      red. intros. eauto with mem.
      
    (* request: 0 < index < N *)
    + generalize Hse. intros Hse2.
      generalize INJP. intros INJP'.
      inv Hse. inv INJP.
       eapply Genv.match_stbls_incr in H; eauto.
      2: { intros. exploit H15; eauto. intros [A B].
           split; intro. apply A. apply H0. eauto.
           apply B. apply H1. eauto. }
      exploit (Genv.find_symbol_match H). eapply FINDP.
      intros (trb & FINDP3 & FINDSYMB).
      rewrite FINDREQ in FINDP. inv FINDP.
      exploit (Genv.find_symbol_match H). eapply FINDIDX.
      intros (tidb & FINDP4 & FINDTIDB).
      exploit (Genv.find_symbol_match H). eapply FINDINPUT.
      intros (tinb & FINDP5 & FINDINB).
      exploit find_encrypt';eauto.
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
      intros READIDX1.
      
     (* (* stack_acc implies inject_incr *)
      assert (H22: inject_incr f f0).
      eapply stack_acc_inject_incr. eapply KINJP. *)
      (* introduce the memory produced by target memory *)
      exploit (exec_request_mem2). eapply READIDX. eapply READR. eapply STORERES.
      eapply READIDX1.
      eauto. eauto. eauto. eauto. eauto. eauto. eauto.
      intros (tm1 & tsp & tm2 & tm3 & tm4 & INJM & INJM'' & ALLOCTM & STORERPTR' & LOADIDX' & LOADRPTR'
              & LOADR' & STOREIDX' & LOADIDX1' & STOREIDX1' & LOADIN' & INJACC).
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
      econstructor. eapply find_request;eauto.
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
      econstructor.
      (* evaluate result [index - 1] *)
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
      (* evaluate r* *)
      econstructor.
      econstructor. econstructor.
      eapply eval_Evar_local. eapply Maps.PTree.gss.
      econstructor. simpl. eauto. eauto.
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
      etransitivity. eauto.
      etransitivity. 2: eauto.
      assert (ro_acc tm tm2). eapply ro_acc_trans.
      eapply ro_acc_alloc; eauto. eapply ro_acc_store; eauto.
      inv H2.
      constructor; eauto with mem. red. eauto.
      set (P:= fun b (ofs:Z) => b <> tsp).
      eapply Mem.unchanged_on_implies. instantiate (1:= P).
      eapply Mem.unchanged_on_trans.
      eapply Mem.alloc_unchanged_on; eauto.
      eapply Mem.store_unchanged_on; eauto.
      intros. unfold P. intro. subst.
      apply Mem.fresh_block_alloc in ALLOCTM.
      congruence. red. intros. congruence.
      econstructor; eauto.
      (* stack acc *)
      (* instantiate (1:= sp::lsp).
      instantiate (1:= injpw j m tm2 INJM).
      econstructor.
      eapply Hm. instantiate (1:= Hm). eauto.
      eapply stack_acc_compose_injp_acc. 
      eauto. eauto. eauto. eauto.
      reflexivity. eapply INJPM.
      econstructor. eauto. rewrite Ptrofs.add_zero. auto. *)
      (* match_kframe *)
      instantiate (1:= tsp::lsp_re).
      econstructor; eauto.
      inversion Hm'0. intros. intro.
      eapply Mem.fresh_block_alloc; eauto.
      intro. eapply freeable_valid in FREEABLE; eauto.
      eapply Mem.fresh_block_alloc; eauto.
      simpl. intro. eapply Mem.fresh_block_alloc.
      eauto. inversion H13. apply unchanged_on_support. eauto.
      econstructor.
      assert (forall b ofs k p, Mem.perm tm b ofs k p -> Mem.perm tm4 b ofs k p).
      intros. eauto with mem.
      eapply freeable_perm_nodec; eauto.
      red. intros. eauto with mem.
      
    (* request: index >= N, return *)
    + generalize Hse. intros Hse2.
      generalize INJP. intros INJP'.
      inv Hse. inv INJP.
       eapply Genv.match_stbls_incr in H; eauto.
      2: { intros. exploit H15; eauto. intros [A B].
           split; intro. apply A. apply H0. eauto.
           apply B. apply H1. eauto. }
      exploit (Genv.find_symbol_match H). eapply FINDP.
      intros (trb & FINDP3 & FINDSYMB).
      exploit (Genv.find_symbol_match H). eapply FINDIDX.
      intros (tidb & FINDP4 & FINDTIDB).
      exploit (Genv.find_symbol_match H). eapply FINDRES.
      intros (tresb & FINDP5 & FINDRESB).
            
      (* (* stack_acc implies injp_acc *)
      assert (H22: inject_incr f f0).
      eapply stack_acc_inject_incr. eapply KINJP.
       *)
      (* introduce the memory produced by target memory *)
      exploit exec_request_mem3. eapply READIDX. eapply READR. eapply STORERES.
      eauto. eauto. eauto.
      intros (tm1 & tm2 & tm3 & tm4 & sp & INJTM4 & ALLOCTM & STORETM1 & LOADTM2  & LOADSP
              & LOADTM3 & STORETM2 & FREETM3 & INJPTM4).
      (* introduce the state after executing the continuation *)
      exploit exec_kframe.
      etransitivity. eapply INJP'.
      eapply INJPTM4. eauto. eauto.
      eapply freeable_perm_nodec; eauto. intros.
      apply Mem.fresh_block_alloc in ALLOCTM as FRESH.
      assert (b <> sp). apply Mem.perm_valid_block in H2.
      intro. congruence.
      eapply Mem.perm_free_1. eauto. left. auto.
      eauto with mem.
      intros (tm5 & INJTM5 & s & REST).
      
      (* step1: function entry *)
      simpl. eexists. split.
      eapply plus_star_trans.
      econstructor. econstructor. simpl.      
      (* step_internal *)
      econstructor. eapply find_request;eauto.
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
      econstructor. econstructor. econstructor.
      eapply eval_Evar_local. eapply Maps.PTree.gss.
      econstructor. simpl. eauto. eauto.
      econstructor. simpl. eauto. eauto.
      simpl. erewrite sem_cast_int_int. eauto.
      econstructor. simpl. eauto.
      rewrite Ptrofs.add_zero_l. eauto.
      (* step5: return state *)
      eapply star_step;eauto. econstructor. simpl.
      econstructor. unfold is_call_cont. auto.
      (* free list *)
      simpl. replace Archi.ptr64 with true by reflexivity. rewrite FREETM3. eauto.
      instantiate (1:= s::nil).
      instantiate (1:= E0).
      destruct REST as (INJPTM5 & STAR & TOPS).
      eapply STAR. eauto.
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
       eapply Genv.match_stbls_incr in H; eauto.
      2: { intros. exploit H15; eauto. intros [A B].
           split; intro. apply A. apply H0. eauto.
           apply B. apply H1. eauto. }
      exploit (Genv.find_symbol_match H). eapply FINDRE.
      intros (trb & FINDP3 & FINDSYMB).
      exploit (Genv.find_symbol_match H). eapply FINDK.
      intros (tkb & FINDP4 & FINDTKB).
      (*assert (INCR: inject_incr f f0).
      eapply stack_acc_inject_incr. eapply KINJP.  *)
      exploit find_request;eauto.
      intros FINDFUN.
      
      inv VINJ. rewrite FINDP3 in H4. inv H4. rename b2 into trb.
      exploit Mem.alloc_parallel_inject; eauto. instantiate (1:= 0).
      lia. instantiate (1:= 8). lia.
      intros (j' & tm' & tsp & ALLOC' & INJ' & INJINCR & INJSP & INJDIFF).
      exploit Mem.store_mapped_inject; eauto.
      intros (tm'' & STORE' & INJ'').
      exploit injp_acc_alloc. apply ALLOC. apply ALLOC'. all: eauto.
      instantiate (1:= INJ'). instantiate (1:= Hm).
      intro INJPACC1.
      exploit Mem.loadv_inject. apply INJ'. eauto. eauto.
      intros (v2 & LOADTM & VINJ). inv VINJ.
      exploit injp_acc_store. apply STORE. apply STORE'. all: eauto.
      instantiate (1:= INJ''). instantiate (1:= INJ').
      intro INJPACC2. 
      
      simpl. eexists. split.
      eapply plus_star_trans.
      econstructor. econstructor. simpl.
      econstructor; eauto.
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
      replace (intptr__void_sg) with (Ctypes.signature_of_type (Ctypes.Tcons
            tintp Ctypes.Tnil) Ctypes.Tvoid {| cc_vararg := None; cc_unproto := false; cc_structret := false |}) by auto.
      econstructor. eauto.
      unfold func_request. unfold ClientMR.func_request.
      unfold type_of_function. simpl.
      unfold Ctypesdefs.tint. unfold cc_default. auto.
      econstructor. econstructor. econstructor. 
      simpl. eapply Mem.sup_include_trans. eauto.
      eapply Mem.sup_include_trans. inversion H13. eauto.
      eapply Mem.sup_include_trans. inv INJPACC1. inversion H21. eauto.
      inv INJPACC2. inversion H21. eauto.
      eapply star_refl. eauto.
      eapply star_refl. eauto.

      (* match state *)
      econstructor;eauto.
      instantiate (1:= INJ'').
      etransitivity. eauto. etransitivity; eauto.
      instantiate (1:= lsp_re). rewrite Ptrofs.add_zero_l.
      econstructor; eauto.
      eapply match_frame_incr; eauto.
      intros. split; intro.
      rewrite <- INJDIFF. eauto. intro. subst.
      eapply freeable_valid in H2; eauto.
      apply Mem.fresh_block_alloc in ALLOC'.
      congruence. apply INJINCR. eauto.
      assert (forall b ofs k p, Mem.perm tm b ofs k p -> Mem.perm tm'' b ofs k p).
      intros. eauto with mem.
      eapply freeable_perm_nodec; eauto. 
  - constructor. intros. inv H.
Qed.

Section RO.

Variable se : Genv.symtbl.
Variable m0 : mem.

Inductive sound_state : state -> Prop :=
| sound_Callrequest : forall i m l,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Callrequest i l m)
| sound_Callencrypt : forall vf i m l,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Callencrypt i l vf m)
| sound_Return : forall m,
    ro_acc m0 m -> sound_memory_ro se m ->
    sound_state (Return m).
End RO.

Definition ro_inv '(row se0 m0) := sound_state se0 m0.

Lemma spec1_ro : preserves top_spec1 ro ro ro_inv.
Proof.
  intros [se0 m0] se1 Hse Hw. cbn in Hw. subst.
  split; cbn in *.
  - intros. inv H0; inv H.
    + constructor; eauto.
      eapply ro_acc_trans; eauto.
      eapply ro_acc_store;eauto.
      eapply ro_acc_sound; eauto.
      eapply ro_acc_store;eauto.
    + constructor; eauto.
      eapply ro_acc_trans;eauto.
      eapply ro_acc_trans;eauto.
      eapply ro_acc_store;eauto.
      eapply ro_acc_store;eauto.
      eapply ro_acc_sound; eauto.
      eapply ro_acc_trans;eauto.
      eapply ro_acc_store;eauto.
      eapply ro_acc_store;eauto.      
    + assert (ro_acc m m'').
      eapply ro_acc_trans.
      eapply ro_acc_store; eauto.
      eapply ro_acc_free_list; eauto.
      constructor; eauto.
      eapply ro_acc_trans;eauto.     
      eapply ro_acc_sound; eauto.
    + assert (ro_acc m m'').
      eapply ro_acc_trans; eauto.
      eapply ro_acc_alloc; eauto.
      eapply ro_acc_store; eauto.
      constructor; eauto.
      eapply ro_acc_trans; eauto.
      eapply ro_acc_sound; eauto.
  - intros. inv H. inv H0. constructor; eauto.
    eapply ro_acc_refl.
    constructor; eauto. eapply ro_acc_refl.
  - intros. inv H0.
  - intros. inv H0. inv H. constructor; eauto.
Qed.

Theorem top1_ro :
  forward_simulation ro ro top_spec1 top_spec1.
Proof.
  eapply preserves_fsim. eapply spec1_ro; eauto.
Qed.


Definition wt_inv :  (Genv.symtbl * signature) -> state -> Prop := fun _ _ => True.

Lemma spec1_wt : preserves top_spec1 wt_c wt_c wt_inv.
Proof.
  intros [se0 sg] se1 Hse Hw. cbn in Hw. subst.
  split; cbn in *.
  - intros. inv H0; inv H.
    + constructor;eauto.
    + constructor; eauto.
    + constructor; eauto.
    + constructor; eauto.
  - intros. inv H. inv H0. constructor; eauto.
    constructor.
  - intros. inv H0.
  - intros. inv H0. inv H. constructor; eauto.
Qed.

Theorem top1_wt : forward_simulation wt_c wt_c top_spec1 top_spec1.
Proof.
  eapply preserves_fsim. eapply spec1_wt; eauto.
Qed.

End WITH_N.
