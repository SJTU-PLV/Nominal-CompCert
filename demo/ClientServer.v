Require Import Coqlib Errors.

Require Import AST Linking Smallstep.
Require Import Compiler.

Require Import CallconvAlgebra.

Require Import Client.
Require Import Server Serverspec Serverproof.

Require Import Linking SmallstepLinking.

(** part1 *)

(*
client ⊕ L1 ≤ client_asm ⊕ b1
client ⊕ L2 ≤ client_asm ⊕ b2
 *)

(* Compute compose (Clight.semantics1 client) L1. 
Can terminate ~10min in at laptop
*)

(* Compute transf_clight_program client. 
Coq process killed
*)
Lemma compose_Client_Server_correct1:
  forall client_asm tp spec,
  compose (Clight.semantics1 client) L1 = Some spec ->
  transf_clight_program client = OK client_asm ->
  link client_asm b1 = Some tp ->
  forward_simulation cc_compcert cc_compcert spec (Asm.semantics tp).
Proof.
  intros.
  rewrite <- (cc_compose_id_right cc_compcert) at 1.
  rewrite <- (cc_compose_id_right cc_compcert) at 2.
  eapply compose_forward_simulations.
  2: { unfold compose in H.
       destruct (@link (AST.program unit unit)) as [skel|] eqn:Hskel. 2: discriminate.
       cbn in *. inv H.
       eapply AsmLinking.asm_linking; eauto. }
  eapply compose_simulation.
  eapply clight_semantic_preservation; eauto using transf_clight_program_match.
  eapply semantics_preservation_L1.
  eauto.
  unfold compose. cbn.
  apply link_erase_program in H1. rewrite H1. cbn. f_equal. f_equal.
  apply Axioms.functional_extensionality. intros [|]; auto.
Qed.

Lemma compose_Client_Server_correct2:
  forall client_asm tp spec,
  compose (Clight.semantics1 client) L2 = Some spec ->
  transf_clight_program client = OK client_asm ->
  link client_asm b2 = Some tp ->
  forward_simulation cc_compcert cc_compcert spec (Asm.semantics tp).
Proof.
  intros.
  rewrite <- (cc_compose_id_right cc_compcert) at 1.
  rewrite <- (cc_compose_id_right cc_compcert) at 2.
  eapply compose_forward_simulations.
  2: { unfold compose in H.
       destruct (@link (AST.program unit unit)) as [skel|] eqn:Hskel. 2: discriminate.
       cbn in *. inv H.
       eapply AsmLinking.asm_linking; eauto. }
  eapply compose_simulation.
  eapply clight_semantic_preservation; eauto using transf_clight_program_match.
  eapply semantics_preservation_L2.
  eauto.
  unfold compose. cbn.
  apply link_erase_program in H1. rewrite H1. cbn. f_equal. f_equal.
  apply Axioms.functional_extensionality. intros [|]; auto.
Qed.

(** * C-level composed specification *)

Require Import Integers Values Memory.

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

Compute link (skel (Clight.semantics1 client)) (skel L1).

Definition linked_skel1 : program unit unit:=
  {|
    prog_defs := (result_id, result_def) :: (key_id, key_def) ::
                   (request_id, Gfun tt) :: (encrypt_id, Gfun tt) ::
                   (process_id, )(complete_id, Gfun tt) :: nil;
    prog_public := encrypt_id :: 
  |}
Program Definition top_spec : Smallstep.semantics li_c li_c :=
    {|
      Smallstep.skel := link (skel (Clight.semantics1 client)) (skel L1);
      Smallstep.state := state;
      Smallstep.activate se :=
        {|
          Smallstep.step _ := step se;
          Smallstep.valid_query q := valid_query se;
          Smallstep.initial_state := initial_state ge;
          Smallstep.at_external := at_external ge;
          Smallstep.after_external := after_external;
          Smallstep.final_state := final_state;
          globalenv := tt;
        |}
    |}.


(* Top level theorem *)
Require Import InjectFootprint Invariant ValueAnalysis.
Require Import CA Asm CallConv CKLRAlgebra.
Section SPEC.

(*items need to define and prove *)
Variable spec1 : Smallstep.semantics li_c li_c.
Variable compose_spec1 : Smallstep.semantics li_c li_c.

Axiom compose : compose (Clight.semantics1 client) L1 = Some compose_spec1.
Axiom top_sim: forward_simulation (cc_c injp) (cc_c injp) spec1 compose_spec1.
Axiom top_ro : forward_simulation ro ro spec1 spec1.
Axiom top_wt : forward_simulation wt_c wt_c spec1 spec1.

Variable client_asm tp : Asm.program.
Axiom compile: transf_clight_program client = OK client_asm.
Axiom link : link client_asm b1 = Some tp.

Lemma ro_injp_cc_compcert:
  cceqv cc_compcert (wt_c @ ro @ cc_c injp @ cc_compcert).
Proof.
  split; unfold cc_compcert.
  - (*incoming side*)
  etransitivity.
  rewrite (inv_dup wt_c), cc_compose_assoc.
  rewrite cc_cainjp__injp_ca, cc_compose_assoc.
  rewrite <- lessdef_c_cklr,cc_compose_assoc.
  (* rewrite injp_injp at 1. rewrite cc_c_compose, cc_compose_assoc. *)
  rewrite <- (cc_compose_assoc ro).
  rewrite <- (cc_compose_assoc wt_c).
  rewrite (commute_around (_@_) (R2 := injp)).
  rewrite inv_commute_ref.
  rewrite !cc_compose_assoc.
  rewrite <- (cc_compose_assoc ro).
  rewrite trans_injp_inv_incoming, ! cc_compose_assoc.
  reflexivity.
  repeat (rstep; [rauto | ]).  
  rewrite <- (cc_compose_assoc wt_c).
  rewrite <- (cc_compose_assoc injp).
  rewrite wt_c_R_refinement, !cc_compose_assoc.
  rewrite <- (cc_compose_assoc lessdef_c), lessdef_c_cklr.
  repeat (rstep; [rauto|]).
  rewrite <- (cc_compose_assoc injp).
  rewrite cc_injpca_cainjp. reflexivity.
  - (*outgoing side*)
    etransitivity.
    rewrite cc_cainjp__injp_ca, cc_compose_assoc.
    rewrite injp_injp at 2. rewrite cc_c_compose, cc_compose_assoc.
    rewrite <- lessdef_c_cklr at 2. rewrite cc_compose_assoc.
    rewrite <- ! (cc_compose_assoc wt_c).
    rewrite (commute_around (wt_c@ lessdef_c) (R2:=injp)), !cc_compose_assoc.
    rewrite <- !(cc_compose_assoc ro).
    rewrite <- (cc_compose_assoc (ro @ injp)).
    rewrite trans_injp_ro_outgoing, cc_compose_assoc.
    rewrite <- (cc_compose_assoc wt_c), inv_commute_ref, cc_compose_assoc.
    rewrite <- (cc_compose_assoc injp).
    rewrite <- (cc_compose_assoc wt_c).
    rewrite (inv_drop _ wt_c), cc_compose_assoc.
    rewrite <- (cc_compose_assoc wt_c).
    reflexivity.
    rstep; [rauto |].
    rewrite <- (cc_compose_assoc injp).
    rewrite wt_c_R_refinement, !cc_compose_assoc.
    rstep; [rauto|].
    rewrite <- (cc_compose_assoc). rewrite lessdef_c_cklr.
    rewrite <- cc_compose_assoc. rewrite <- cc_c_compose.
    rewrite injp_injp2.
    rewrite <- (cc_compose_assoc injp).
  rewrite cc_injpca_cainjp. reflexivity.
Qed.
  
Theorem spec_sim_1 : forward_simulation cc_compcert cc_compcert spec1 (Asm.semantics tp).
Proof.
  rewrite ro_injp_cc_compcert at 1.
  rewrite ro_injp_cc_compcert at 2.
  eapply compose_forward_simulations.
  eapply top_wt.
  eapply compose_forward_simulations.
  eapply top_ro.
  eapply compose_forward_simulations.
  eapply top_sim.
  eapply compose_Client_Server_correct1; eauto.
  eapply compose.
  eapply compile.
  eapply link.
Qed.  

End SPEC.
