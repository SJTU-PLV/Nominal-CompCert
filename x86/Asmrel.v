Require Import Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.
Require Import Mach LanguageInterface CKLR.
Require Import Asm.

Definition genv_match p R w: relation genv :=
  (match_stbls R w) !! (fun se => Genv.globalenv se p).

Inductive state_match R w: rel (block * Asm.state) (block * Asm.state) :=
| state_rel: forall (rs1 rs2: regset) m1 m2 b1 b2 nb1 nb2,
    (forall r: preg, Val.inject (mi R w) (rs1 r) (rs2 r)) ->
    match_mem R w m1 m2 ->
    b1 = b2 ->
    nb1 = Mem.nextblock m1 ->
    nb2 = Mem.nextblock m2 ->
    state_match R w (nb1, Asm.State rs1 m1 b1) (nb2, Asm.State rs2 m2 b2).

Lemma semantics_asm_rel p R:
  forward_simulation (cc_asm R) (cc_asm R) (Asm.semantics p) (Asm.semantics p).
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn -[semantics] in *.
  pose (ms := fun s1 s2 =>
                klr_diam tt (genv_match p R * state_match R)
                         w
                         (Genv.globalenv se1 p, s1)
                         (Genv.globalenv se2 p, s2)).
  apply forward_simulation_step with (match_states := ms); cbn.
  - intros [rs1 m1] [rs2 m2] [vm mm].
    cbn. eapply Genv.is_internal_match; eauto.
    + repeat apply conj; auto.
      induction (prog_defs p) as [ | [id [f|v]] defs IHdefs]; repeat (econstructor; eauto).
      * admit.                  (* match_fundef *)
      * admit.                  (* match_varinfo *)
    + eapply match_stbls_proj; auto.
    + admit.                    (* match_fundef *)
    + admit.                    (* PC <> Vundef *)
  - intros [rs1 m1] [rs2 m2] [nb1 s1] Hs [Hq Hnb].
    assert (Hge: genv_match p R w (Genv.globalenv se1 p) (Genv.globalenv se2 p)).
    {
      cut (match_stbls R w (Genv.globalenv se1 p) (Genv.globalenv se2 p)); eauto.
      eapply (rel_push_rintro (fun se => Genv.globalenv se p) (fun se => Genv.globalenv se p)).
    }
    destruct s1.
    exists (Mem.nextblock m2, State rs2 m2 b).
    repeat apply conj; auto.
    + admit.                    (* initial state *)
    + admit.                    (* match *)
  - intros [nb1 s1] [nb2 s2] [rs1 m1] Hm H.
    admit.                      (* final state *)
  - admit.                      (* external call *)
  - admit.                      (* step *)
  - apply well_founded_ltof.
    
