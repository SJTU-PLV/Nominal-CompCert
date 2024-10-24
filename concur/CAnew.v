Require Import LanguageInterface CallconvAlgebra Invariant.
Require Import CKLR Inject InjectFootprint Extends.
Require Import Linear Mach Locations Conventions.
Require Import ValueAnalysis.
Require Import Allocproof Lineartyping Asm Asmgenproof0.
Require Import Maps Stacklayout.

Require Import CallconvBig CallConvAlgebra InjpAccoComp InjpExtAccoComp VCompBig Injp CA.
Require Import Separation StackingproofC CallConv CallConvLibs.
Import GS.



Record cc_cainjp_world :=
  cajw {
      cajw_injp: world injp;
      cajw_sg : signature;
      cajw_rs : regset;
    }.


Inductive cc_c_asm_injp_mq : cc_cainjp_world -> c_query -> query li_asm -> Prop:=
  cc_c_asm_injp_mq_intro sg args m j (rs: regset) tm tm0 vf
    (Hm: Mem.inject j m tm):
    let tsp := rs SP in let tra := rs RA in let tvf := rs PC in
    let targs := (map (fun p => Locmap.getpair p (make_locset_rs rs tm tsp))
                      (loc_arguments sg)) in
    Val.inject_list j args targs ->
    Val.inject j vf tvf ->
    (forall b ofs, loc_init_args (size_arguments sg) tsp b ofs ->
              loc_out_of_reach j m b ofs) ->
    Val.has_type tsp Tptr ->
    Val.has_type tra Tptr ->
    valid_blockv (Mem.support tm) tsp ->
    pointer_tid (Mem.tid (Mem.support tm)) tsp ->
    args_removed sg tsp tm tm0 -> (* The Outgoing arguments are readable and freeable in tm *)
    vf <> Vundef -> tra <> Vundef ->
    cc_c_asm_injp_mq
      (cajw (injpw j m tm Hm) sg rs)
      (cq vf sg args m)
      (rs,tm).

Inductive cc_c_asm_injp_mr : cc_cainjp_world -> c_reply -> reply li_asm -> Prop :=
  cc_c_asm_injp_mr_intro sg res  j' m' tm' Hm' (rs rs' :regset) :
     let tres := rs_getpair (map_rpair preg_of (loc_result sg)) rs' in
     Val.inject j' res tres ->
     (forall r, is_callee_save r = true -> rs' (preg_of r) = rs (preg_of r)) ->
     (*(forall b ofs, loc_init_args (size_arguments sg) tsp b ofs ->
              loc_out_of_reach j m b ofs) -> *)
     rs'#SP = rs#SP -> rs'#PC = rs#RA ->
     cc_c_asm_injp_mr
       (cajw (injpw j' m' tm' Hm') sg rs)
       (cr res m')
       (rs', tm').

Definition get_injp := cajw_injp.

Definition set_injp (wa: cc_cainjp_world) (w : injp_world) :=
  match wa with cajw w' sig rs => cajw w sig rs end.

Program Instance lens_injp : Lens (cc_cainjp_world) injp_world :=
  {
    get := get_injp;
    set := set_injp;
  }.
Next Obligation. destruct t. reflexivity. Qed.
Next Obligation. destruct t. reflexivity. Qed.
Next Obligation. destruct t. reflexivity. Qed.


Program Instance CAworld : World cc_cainjp_world :=
    {
      w_state := injp_world;
      w_lens := lens_injp;
      w_acci := injp_acci;
      w_acce := injp_acce;
      w_acci_trans := injp_acci_preo;
    }.
     

Program Definition cc_c_asm_injp_new : GS.callconv li_c li_asm :=
  {|
    GS.ccworld := cc_cainjp_world;
    GS.ccworld_world := CAworld;
    GS.match_senv w := match_stbls injp (cajw_injp w);
    GS.match_query := cc_c_asm_injp_mq;
    GS.match_reply := cc_c_asm_injp_mr
  |}.
Next Obligation.
  inv H. inv H1. eauto.
Qed.
Next Obligation.
  inv H.
  eapply Genv.valid_for_match in H2.
  apply H2. eauto.
Qed.
