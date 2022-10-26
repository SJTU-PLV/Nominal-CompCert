Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.
Require Import Values Memory.
Require Import Conventions Mach Asm.
Require Import CKLR.
Require Import Locations CallConv Compiler.


(*
Given b.asm


 sth

 CA -->> CA

 {| b.asm |}

CCO:
m             A                    m

m_            cc_stacking injp   inj

args_remove
tm           B                   tm

 C  -> []

     injp

 C  -> [sp bx ra] li_c -> li_c   (cq : args m)

     CA

 Asm -> [sp bx ra]



   cc_c_asm_injp   ==    injp      === injp
                          CA           CL
                                       LM
                                       MA

*)

Record cc_ca_world :=
  caw{
      caw_sg : signature;
      caw_rs : regset;
      caw_m : mem
    }.

Definition make_locset_rs (rs: regset) (m:mem) (sp: val) (l:loc):=
  match l with
    |R r => rs (preg_of r)
    |S Outgoing ofs ty =>
      let v := load_stack m sp ty (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs)) in Val.maketotal v
    |_ => Vundef
  end.

Inductive cc_c_asm_mq : cc_ca_world -> c_query -> query li_asm -> Prop:=
  cc_c_asm_mq_intro sg args m (rs: regset) tm (ls : Locmap.t):
    let sp := rs#SP in let ra := rs#RA in let vf := rs#PC in
    args = (map (fun p => Locmap.getpair p ls) (loc_arguments sg)) ->
    ls = make_locset_rs rs tm sp ->
(*    ls = make_locset mrs tm sp ->
    (forall r: mreg, mrs r = rs (preg_of r)) -> *)
    args_removed sg sp tm m ->
    Val.has_type sp Tptr ->
    Val.has_type ra Tptr ->
    valid_blockv (Mem.support tm) sp ->
    vf <> Vundef -> ra <> Vundef ->
    cc_c_asm_mq
      (caw sg rs tm)
      (cq vf sg args m)
      (rs,tm).

Definition rs_getpair (p: rpair preg) (rs : regset) :=
  match p with
    |One r => rs r
    |Twolong r1 r2 => Val.longofwords (rs r1) (rs r2)
  end.

Inductive cc_c_asm_mr : cc_ca_world -> c_reply -> reply li_asm -> Prop :=
  cc_c_asm_mr_intro sg res tm m' tm' (rs rs' :regset) :
     let sp := rs#SP in
     res = rs_getpair (map_rpair preg_of (loc_result sg)) rs' ->
(*     res = Locmap.getpair (map_rpair R (loc_result sg)) ls' ->
     (forall r, In r (regs_of_rpair (loc_result sg)) -> rs' (preg_of r) = ls' (R r)) ->
*)
     (forall r, is_callee_save r = true -> rs' (preg_of r) = rs (preg_of r)) ->
     Mem.unchanged_on (not_init_args (size_arguments sg) sp) m' tm' ->
     Mem.unchanged_on (loc_init_args (size_arguments sg) sp) tm tm' ->
     Mem.support m' = Mem.support tm' ->
     (forall b ofs k p, loc_init_args (size_arguments sg) sp b ofs ->
                       ~ Mem.perm m' b ofs k p) ->
     rs'#SP = rs#SP -> rs'#PC = rs#RA ->
     cc_c_asm_mr
       (caw sg rs tm)
       (cr res m')
       (rs', tm').

Program Definition cc_c_asm : callconv li_c li_asm :=
  {|
    match_senv _ := eq;
    match_query := cc_c_asm_mq;
    match_reply := cc_c_asm_mr
  |}.

Definition rs_to_mrs (rs : regset) :=
  fun r: mreg => rs (preg_of r).

Lemma cc_ca_cllmma :
  ccref (cc_c_asm) (cc_c_locset @ cc_locset_mach @ cc_mach_asm).
Proof.
  intros [sg rs tm] se1 se2 q1 q2 Hse. destruct Hse.
  intros Hq. inversion Hq. subst sg0 rs0 tm0 q1 q2.
  exists (se1,sg,(se1,(lmw sg (rs_to_mrs rs) tm sp),
      (rs,Mem.support tm))).
  repeat apply conj; cbn in *; eauto.
  - exists (lq vf sg ls m). split.
    econstructor; eauto.
    exists (mq vf sp ra (rs_to_mrs rs) tm). split. rewrite H3.
    econstructor; eauto.
    econstructor; eauto.
  - intros cr ar [lr [Hr1 [mr [Hr2 Hr3]]]].
    inv Hr1. inv Hr2. inv Hr3.
    econstructor; eauto.
    + destruct (loc_result sg).
      -- simpl. rewrite <- H13. rewrite H9. reflexivity. simpl. auto.
      -- simpl. f_equal.
         rewrite <- H13. rewrite H9. reflexivity. simpl. eauto.
         rewrite <- H13. rewrite H9. reflexivity. simpl. eauto.
    + intros. rewrite <- H13. rewrite H12. reflexivity. eauto.
Qed.

Lemma cc_cllmma_ca :
  ccref (cc_c_locset @ cc_locset_mach @ cc_mach_asm) (cc_c_asm).
Proof.
  intros [[se' sg] [[se'' w2] [rs tm]]] se''' se q1 q2 Hse Hq.
  destruct Hse. inv H. destruct H0. inv H. inv H0.
  destruct Hq as [lq [Hq1 [mq [Hq2 Hq3]]]]. cbn in *.
  inv Hq1. inv Hq2. inv Hq3.
  rename rs1 into mrs. rename m0 into tm.
  exists (caw sg rs tm).
  repeat apply conj; eauto.
  - econstructor; eauto.
    apply Axioms.extensionality.
    intro r. destruct r; simpl; eauto.
  - intros r1 r2 Hr. inv Hr.
    set (ls' loc := 
           match loc with
             |R r => rs' (preg_of r)
             |_ => Vundef
           end
        ).
    exists (lr ls'  m'). split.
    constructor; eauto.
    destruct (loc_result); simpl; eauto.
    exists (mr (rs_to_mrs rs') tm'). split.
    constructor; eauto.
    intros. unfold rs_to_mrs. rewrite H3. eauto. eauto.
    constructor; eauto.
    inversion H8. eauto.
Qed.
