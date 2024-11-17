Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.
Require Import Values Memory.
Require Import Conventions Mach Asm.
Require Import CKLR.
Require Import Locations CallConv.
Require Import Inject InjectFootprint.
Require Import CA CallConvRust Rusttypes.

(** Structual convention between Rust and assembly (RA) *)

Record cc_ra_world :=
  raw{
      raw_sg : rust_signature;
      raw_rs : regset;
      raw_m : mem
    }.

Inductive cc_rust_asm_mq : cc_ra_world -> rust_query -> query li_asm -> Prop:=
  cc_rust_asm_mq_intro rsg args m (rs: regset) tm (ls : Locmap.t):
    let sp := rs#SP in let ra := rs#RA in let vf := rs#PC in
    let sg := signature_of_rust_signature rsg in
    args = (map (fun p => Locmap.getpair p ls) (loc_arguments sg)) ->
    ls = make_locset_rs rs tm sp ->
    args_removed sg sp tm m ->
    Val.has_type sp Tptr ->
    Val.has_type ra Tptr ->
    valid_blockv (Mem.support tm) sp ->
    vf <> Vundef -> ra <> Vundef ->
    cc_rust_asm_mq
      (raw rsg rs tm)
      (rsq vf rsg args m)
      (rs,tm).

Inductive cc_rust_asm_mr : cc_ra_world -> rust_reply -> reply li_asm -> Prop :=
  cc_rust_asm_mr_intro rsg res tm m' tm' (rs rs' :regset) :
    let sp := rs#SP in
    let sg := signature_of_rust_signature rsg in
     res = rs_getpair (map_rpair preg_of (loc_result sg)) rs' ->
     (forall r, is_callee_save r = true -> rs' (preg_of r) = rs (preg_of r)) ->
     Mem.unchanged_on (not_init_args (size_arguments sg) sp) m' tm' ->
     Mem.unchanged_on (loc_init_args (size_arguments sg) sp) tm tm' ->
     Mem.support m' = Mem.support tm' ->
     (forall b ofs k p, loc_init_args (size_arguments sg) sp b ofs ->
                       ~ Mem.perm m' b ofs k p) ->
     rs'#SP = rs#SP -> rs'#PC = rs#RA ->
     cc_rust_asm_mr
       (raw rsg rs tm)
       (rsr res m')
       (rs', tm').

Program Definition cc_rust_asm : callconv li_rs li_asm :=
  {|
    match_senv _ := eq;
    match_query := cc_rust_asm_mq;
    match_reply := cc_rust_asm_mr
  |}.
Next Obligation.
  split; auto.
Defined.

Lemma cc_ra_rcca:
  ccref cc_rust_asm (cc_rust_c @ cc_c_asm).
Proof.
  red. intros [sg rs m] se1 se2 q1 q2 Hse. destruct Hse.
  intros Hq. inv Hq.
  exists (se1, tt, caw sg0 rs m). repeat apply conj.
  - econstructor. constructor.
    econstructor.
  - econstructor. split.
    econstructor.
    econstructor; eauto.
  - intros r1 r2 Hr. inv Hr. destruct H.
    inv H. inv H0.
    econstructor; eauto.
Qed.


Lemma cc_rcca_ra:
  ccref (cc_rust_c @ cc_c_asm) cc_rust_asm.
Proof.
  red. intros ((se1' & ?)& [sg rs m]) se1 se2 q1 q2 Hse. destruct Hse. 
  inv H. inv H0. intros Hq. inv Hq.
  destruct H. inv H. inv H0.
  exists (raw sg0 rs m). repeat apply conj.
  - econstructor.
  - econstructor; eauto.
  - intros r1 r2 Hr. inv Hr.
    econstructor. split.
    econstructor. econstructor; eauto.
Qed.

Lemma cc_ra_rcca_equiv:
  cceqv cc_rust_asm (cc_rust_c @ cc_c_asm).
Proof. split. apply cc_ra_rcca. apply cc_rcca_ra. Qed.
    

(** Definition of cc_rust_asm_injp (RAinjp) as the general calling
convention between Rust and assembly.  The memory and arguments are
related by some injection function. *)

Record cc_rainjp_world :=
  rajw {
      rajw_injp: world injp;
      rajw_sg : rust_signature;
      rajw_rs : regset;
    }.

Inductive cc_rust_asm_injp_mq : cc_rainjp_world -> rust_query -> query li_asm -> Prop:=
  cc_rust_asm_injp_mq_intro rsg args m j (rs: regset) tm tm0 vf
    (Hm: Mem.inject j m tm):
    let sg := signature_of_rust_signature rsg in
    let tsp := rs#SP in let tra := rs#RA in let tvf := rs#PC in
    let targs := (map (fun p => Locmap.getpair p (make_locset_rs rs tm tsp))
                      (loc_arguments sg)) in
    Val.inject_list j args targs ->
    Val.inject j vf tvf ->
    (forall b ofs, loc_init_args (size_arguments sg) tsp b ofs ->
              loc_out_of_reach j m b ofs) ->
    Val.has_type tsp Tptr ->
    Val.has_type tra Tptr ->
    valid_blockv (Mem.support tm) tsp ->
    args_removed sg tsp tm tm0 -> (* The Outgoing arguments are readable and freeable in tm *)
    vf <> Vundef -> tra <> Vundef ->
    cc_rust_asm_injp_mq
      (rajw (injpw j m tm Hm) rsg rs)
      (rsq vf rsg args m)
      (rs,tm).

Inductive cc_rust_asm_injp_mr : cc_rainjp_world -> rust_reply -> reply li_asm -> Prop :=
  cc_rust_asm_injp_mr_intro rsg res j m tm Hm j' m' tm' Hm' (rs rs' :regset) :
    let tsp := rs#SP in
    let sg := signature_of_rust_signature rsg in
    let tres := rs_getpair (map_rpair preg_of (loc_result sg)) rs' in     
     Val.inject j' res tres ->
     injp_acc (injpw j m tm Hm) (injpw j' m' tm' Hm') ->
     (forall r, is_callee_save r = true -> rs' (preg_of r) = rs (preg_of r)) ->
     (forall b ofs, loc_init_args (size_arguments sg) tsp b ofs ->
              loc_out_of_reach j m b ofs) ->
     rs'#SP = rs#SP -> rs'#PC = rs#RA ->
     cc_rust_asm_injp_mr
       (rajw (injpw j m tm Hm) rsg rs)
       (rsr res m')
       (rs', tm').

Program Definition cc_rust_asm_injp : callconv li_rs li_asm :=
  {|
    match_senv w := match_stbls injp (rajw_injp w);
    match_query := cc_rust_asm_injp_mq;
    match_reply := cc_rust_asm_injp_mr
  |}.
Next Obligation.
  inv H. inv H1. eauto.
Qed.
Next Obligation.
  inv H.
  eapply Genv.valid_for_match in H1.
  split; intros.
  apply H1. auto.
  apply H1. auto.
Qed.

(** The following two lemmas help us resue the proof of
cc_injpca_cainjp and cc_cainjp__injp_ca in CA instead of writing them
again *)

Lemma cainjp__rc_cainjp:
  ccref cc_rust_asm_injp (cc_rust_c @ cc_c_asm_injp).
Proof.
  red. intros [w sg rs] se1 se2 q1 q2 Hse Hq.
  destruct w as [j m tm1 Hm]. inv Hse. inv Hq. 
  exists (se1, tt, cajw (injpw j m tm1 Hm) sg0 rs).
  repeat apply conj.
  - econstructor. econstructor.
    econstructor; eauto.
  - econstructor. split.
    econstructor.
    econstructor; eauto.
  - intros r1 r2 Hr. inv Hr. destruct H.
    inv H. inv H0. inv H21.
    econstructor; eauto.
    instantiate (1 := Hm'2).
    econstructor; eauto.
Qed.    
  
Lemma rc_cainjp__ca_injp:
  ccref (cc_rust_c @ cc_c_asm_injp) cc_rust_asm_injp.
Proof.
  red. intros ((se1' & ?) & [w sg rs]) se1 se2 q1 q2 Hse Hq.
  destruct w as [j m tm1 Hm]. inv Hse. inv H. inv Hq. 
  destruct H. inv H. inv H1. inv H0.
  exists (rajw (injpw j m0 tm1 Hm) sg0 rs).
  repeat apply conj.
  - econstructor; eauto.
  - econstructor; eauto.
  - intros r1 r2 Hr. inv Hr.
    econstructor. split.
    econstructor.
    econstructor; eauto.
    inv H8.
    instantiate (1 := Hm').
    econstructor; eauto.
Qed.

    
(** cc_rust_asm_injp ≡ cc_rs injp @ cc_rust_asm *)

Lemma cc_rainjp_injpra :
  ccref (cc_rust_asm_injp) (cc_rs injp @ cc_rust_asm).
Proof.
  rewrite cainjp__rc_cainjp.
  rewrite cc_cainjp__injp_ca.
  rewrite (commute_around cc_rust_c).
  eapply cc_compose_ref. reflexivity.
  eapply cc_rcca_ra.
Qed.

Lemma cc_injpra_rainjp :
  ccref (cc_rs injp @ cc_rust_asm) (cc_rust_asm_injp).
Proof.
  rewrite cc_ra_rcca.
  rewrite <- cc_compose_assoc.
  rewrite injp_rs__rc_injp. rewrite cc_compose_assoc.
  rewrite cc_injpca_cainjp.
  eapply rc_cainjp__ca_injp.
Qed.  

Theorem rainjp_injpra_equiv :
  cceqv (cc_rust_asm_injp) (cc_rs injp @ cc_rust_asm).
Proof. split. apply cc_rainjp_injpra. apply cc_injpra_rainjp. Qed.  

