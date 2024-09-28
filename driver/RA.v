Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.
Require Import Values Memory.
Require Import Conventions Mach Asm.
Require Import CKLR.
Require Import Locations CallConv.
Require Import Inject InjectFootprint.
Require Import CA Rusttypes.

(** Structual convention between Rust and assembly (RA) *)

Record cc_ra_world :=
  raw{
      raw_sg : signature;
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
      (raw sg rs tm)
      (rsq vf rsg args m)
      (rs,tm).

Inductive cc_rust_asm_mr : cc_ra_world -> rust_reply -> reply li_asm -> Prop :=
  cc_rust_asm_mr_intro sg res tm m' tm' (rs rs' :regset) :
     let sp := rs#SP in
     res = rs_getpair (map_rpair preg_of (loc_result sg)) rs' ->
     (forall r, is_callee_save r = true -> rs' (preg_of r) = rs (preg_of r)) ->
     Mem.unchanged_on (not_init_args (size_arguments sg) sp) m' tm' ->
     Mem.unchanged_on (loc_init_args (size_arguments sg) sp) tm tm' ->
     Mem.support m' = Mem.support tm' ->
     (forall b ofs k p, loc_init_args (size_arguments sg) sp b ofs ->
                       ~ Mem.perm m' b ofs k p) ->
     rs'#SP = rs#SP -> rs'#PC = rs#RA ->
     cc_rust_asm_mr
       (raw sg rs tm)
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
Admitted.


Lemma cc_rcca_ra:
  ccref (cc_rust_c @ cc_c_asm) cc_rust_asm.
Admitted.

Lemma cc_ra_rcca_equiv:
  cceqv cc_rust_asm (cc_rust_c @ cc_c_asm).
Proof. split. apply cc_ra_rcca. apply cc_rcca_ra. Qed.
    

(** Definition of cc_rust_asm_injp (RAinjp) as the general calling
convention between Rust and assembly.  The memory and arguments are
related by some injection function. *)

Record cc_rainjp_world :=
  rajw {
      rajw_injp: world injp;
      rajw_sg : signature;
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
      (rajw (injpw j m tm Hm) sg rs)
      (rsq vf rsg args m)
      (rs,tm).

Inductive cc_rust_asm_injp_mr : cc_rainjp_world -> rust_reply -> reply li_asm -> Prop :=
  cc_rust_asm_injp_mr_intro sg res j m tm Hm j' m' tm' Hm' (rs rs' :regset) :
     let tsp := rs#SP in
     let tres := rs_getpair (map_rpair preg_of (loc_result sg)) rs' in
     Val.inject j' res tres ->
     injp_acc (injpw j m tm Hm) (injpw j' m' tm' Hm') ->
     (forall r, is_callee_save r = true -> rs' (preg_of r) = rs (preg_of r)) ->
     (forall b ofs, loc_init_args (size_arguments sg) tsp b ofs ->
              loc_out_of_reach j m b ofs) ->
     rs'#SP = rs#SP -> rs'#PC = rs#RA ->
     cc_rust_asm_injp_mr
       (rajw (injpw j m tm Hm) sg rs)
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


(** cc_rust_asm_injp ≡ cc_rs injp @ cc_rust_asm *)

Lemma cc_rainjp_injpra :
  ccref (cc_rust_asm_injp) (cc_rs injp @ cc_rust_asm).
Proof.
Admitted.

Lemma cc_injpra_rainjp :
  ccref (cc_rs injp @ cc_rust_asm) (cc_rust_asm_injp).
Proof.
Admitted.

Theorem rainjp_injpra_equiv :
  cceqv (cc_rust_asm_injp) (cc_rs injp @ cc_rust_asm).
Proof. split. apply cc_rainjp_injpra. apply cc_injpra_rainjp. Qed.  

