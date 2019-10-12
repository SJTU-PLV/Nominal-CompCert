Require Import Coqlib.
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.

(** * Semantic interface of languages *)

Structure language_interface :=
  mk_language_interface {
    query: Type;
    reply: Type;
    entry: query -> val;
  }.

Arguments entry {_}.

(** ** Null interface *)

(** The null language interface defined below is used as the outgoing
  interface for closed semantics. *)

Definition li_null :=
  {|
    query := Empty_set;
    reply := Empty_set;
    entry q := match q with end;
  |}.

(** * Calling conventions *)

(** ** Definition *)

Record callconv {li1 li2} :=
  mk_callconv {
    ccworld : Type;
    match_senv: ccworld -> Genv.symtbl -> Genv.symtbl -> Prop;
    match_query: ccworld -> query li1 -> query li2 -> Prop;
    match_reply: ccworld -> reply li1 -> reply li2 -> Prop;

    match_senv_public_preserved:
      forall w se1 se2,
        match_senv w se1 se2 ->
        forall id, Genv.public_symbol se2 id = Genv.public_symbol se1 id;
  }.

Arguments callconv: clear implicits.
Delimit Scope cc_scope with cc.
Bind Scope cc_scope with callconv.
Local Obligation Tactic := cbn; eauto.

(** ** Identity *)

Program Definition cc_id {li}: callconv li li :=
  {|
    ccworld := unit;
    match_senv w := eq;
    match_query w := eq;
    match_reply w := eq;
  |}.
Solve All Obligations with
  congruence.

Notation "1" := cc_id : cc_scope.

(** ** Composition *)

Program Definition cc_compose {li1 li2 li3} (cc12: callconv li1 li2) (cc23: callconv li2 li3) :=
  {|
    ccworld := ccworld cc12 * ccworld cc23;
    match_senv w se1 se3 :=
      exists se2,
        match_senv cc12 (fst w) se1 se2 /\
        match_senv cc23 (snd w) se2 se3;
    match_query w q1 q3 :=
      exists q2,
        match_query cc12 (fst w) q1 q2 /\
        match_query cc23 (snd w) q2 q3;
    match_reply w r1 r3 :=
      exists r2,
        match_reply cc12 (fst w) r1 r2 /\
        match_reply cc23 (snd w) r2 r3;
  |}.
Next Obligation.
  intros li1 li2 li3 cc12 cc23 w se1 se3 (se2 & H12 & H23) id.
  etransitivity; eauto using match_senv_public_preserved.
Qed.

Infix "@" := cc_compose (at level 30, right associativity) : cc_scope.

(** * C-like languages *)

(** ** Interface *)

Record c_query :=
  cq {
    cq_vf: val;
    cq_sg: signature;
    cq_args: list val;
    cq_mem: mem;
  }.

Record c_reply :=
  cr {
    cr_retval: val;
    cr_mem: mem;
  }.

Canonical Structure li_c :=
  {|
    query := c_query;
    reply := c_reply;
    entry := cq_vf;
  |}.

(** ** Simulation conventions *)

(** *** Memory extensions *)

Inductive cc_ext_query: c_query -> c_query -> Prop :=
  cc_ext_query_intro vf sg vargs1 vargs2 m1 m2:
    Val.lessdef_list vargs1 vargs2 ->
    Mem.extends m1 m2 ->
    cc_ext_query (cq vf sg vargs1 m1) (cq vf sg vargs2 m2).

Inductive cc_ext_reply: c_reply -> c_reply -> Prop :=
  cc_ext_reply_intro vres1 vres2 m1 m2:
    Val.lessdef vres1 vres2 ->
    Mem.extends m1 m2 ->
    cc_ext_reply (cr vres1 m1) (cr vres2 m2).

Program Definition cc_ext :=
  {|
    ccworld := unit;
    match_senv w := eq;
    match_query w := cc_ext_query;
    match_reply w := cc_ext_reply;
  |}.
Solve All Obligations with
  congruence.

(** *** Memory injections *)

(** Memory injections with thresholds *)

Record meminj_thr :=
  mit {
    mit_meminj :> block -> option (block * Z);
    mit_l: block;
    mit_r: block;
  }.

Definition mit_incr (w: meminj_thr) (f: meminj): Prop :=
  inject_incr w f /\
  forall b1 b2 delta,
    w b1 = None ->
    f b1 = Some (b2, delta) ->
    Pos.le (mit_l w) b1 /\
    Pos.le (mit_r w) b2.

Inductive cc_inj_senv: meminj_thr -> Genv.symtbl -> Genv.symtbl -> Prop :=
  cc_inj_senv_intro f se1 se2:
    Genv.match_stbls f se1 se2 ->
    cc_inj_senv (mit f (Genv.genv_next se1) (Genv.genv_next se2)) se1 se2.

Inductive cc_inj_query (f: meminj_thr): c_query -> c_query -> Prop :=
  cc_inj_query_intro vf1 vf2 sg vargs1 vargs2 m1 m2:
    Val.inject f vf1 vf2 ->
    Val.inject_list f vargs1 vargs2 ->
    Mem.inject f m1 m2 ->
    Pos.le (mit_l f) (Mem.nextblock m1) ->
    Pos.le (mit_r f) (Mem.nextblock m2) ->
    vf1 <> Vundef ->
    cc_inj_query f (cq vf1 sg vargs1 m1) (cq vf2 sg vargs2 m2).

Inductive cc_inj_reply (f: meminj_thr): c_reply -> c_reply -> Prop :=
  cc_inj_reply_intro f' vres1 vres2 m1 m2:
    mit_incr f f' ->
    Val.inject f' vres1 vres2 ->
    Mem.inject f' m1 m2 ->
    Pos.le (mit_l f) (Mem.nextblock m1) ->
    Pos.le (mit_r f) (Mem.nextblock m2) ->
    cc_inj_reply f (cr vres1 m1) (cr vres2 m2).

Program Definition cc_inj :=
  {|
    match_senv := cc_inj_senv;
    match_query := cc_inj_query;
    match_reply := cc_inj_reply;
  |}.
Next Obligation.
  intros. destruct H. rewrite (Genv.mge_public H); auto.
Qed.

Lemma mit_incr_refl w:
  mit_incr w w.
Proof.
  split.
  - apply inject_incr_refl.
  - congruence.
Qed.

Lemma cc_inj_match_stbls w j se1 se2:
  cc_inj_senv w se1 se2 ->
  mit_incr w j ->
  Genv.match_stbls j se1 se2.
Proof.
  intros Hse [Hj SEP]. destruct Hse. cbn in *.
  eapply Genv.match_stbls_incr; eauto.
Qed.

(** *** Injections with footprint enforcement *)

Record cc_injp_world :=
  injpw { injp_inj :> meminj; injp_m1: mem; injp_m2: mem }.

Inductive cc_injp_stbls: cc_injp_world -> Genv.symtbl -> Genv.symtbl -> Prop :=
  cc_injp_stbls_intro f m1 m2 se1 se2:
    Genv.match_stbls f se1 se2 ->
    Pos.le (Genv.genv_next se1) (Mem.nextblock m1) ->
    Pos.le (Genv.genv_next se2) (Mem.nextblock m2) ->
    cc_injp_stbls (injpw f m1 m2) se1 se2.

Inductive cc_injp_query: cc_injp_world -> c_query -> c_query -> Prop :=
  cc_injp_query_intro f vf1 vf2 sg vargs1 vargs2 m1 m2:
    Val.inject f vf1 vf2 ->
    Val.inject_list f vargs1 vargs2 ->
    Mem.inject f m1 m2 ->
    vf1 <> Vundef ->
    cc_injp_query (injpw f m1 m2) (cq vf1 sg vargs1 m1) (cq vf2 sg vargs2 m2).

Inductive cc_injp_reply: cc_injp_world -> c_reply -> c_reply -> Prop :=
  cc_injp_reply_intro f m1 m2 f' vres1 vres2 m1' m2':
    Val.inject f' vres1 vres2 ->
    Mem.inject f' m1' m2' ->
    Mem.unchanged_on (loc_unmapped f) m1 m1' ->
    Mem.unchanged_on (loc_out_of_reach f m1) m2 m2' ->
    inject_incr f f' ->
    inject_separated f f' m1 m2 ->
    (forall b ofs p, Mem.valid_block m1 b -> Mem.perm m1' b ofs Max p -> Mem.perm m1 b ofs Max p) ->
    (forall b ofs p, Mem.valid_block m2 b -> Mem.perm m2' b ofs Max p -> Mem.perm m2 b ofs Max p) ->
    cc_injp_reply (injpw f m1 m2) (cr vres1 m1') (cr vres2 m2').

Program Definition cc_injp :=
  {|
    match_senv := cc_injp_stbls;
    match_query := cc_injp_query;
    match_reply := cc_injp_reply;
  |}.
Next Obligation.
  intros. inv H. erewrite Genv.mge_public; eauto.
Qed.
