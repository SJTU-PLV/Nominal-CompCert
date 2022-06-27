(** Preliminary experiments about incorporating state encapsulation into
  CompCert languages *)

From compcert Require Import
     AST Coqlib Maps Values Integers Cop Ctypes Errors Events
     LanguageInterface Smallstep Globalenvs Clight Memory.
From compcert.compcertox Require Import Lifting.

Record esemantics liA liB := {
    pstate : Type;
    init_pstate : pstate;
    esem : semantics (liA @ pstate) (liB @ pstate)
  }.

Definition encap_lift {liA liB} (L: semantics liA liB) :=
  {|
    init_pstate := tt;
    esem := L @ unit;
  |}.

Section Clight.

  Variable ge: genv.

  Section EXPR.

    Variable e: env.
    Variable le: temp_env.
    Variable m: mem.
    (* For now, we assume that the persistent memory does not contain pointers *)
    Variable pm: mem.

    Inductive eval_expr: expr -> val -> Prop :=
    | eval_Econst_int:   forall i ty,
        eval_expr (Econst_int i ty) (Vint i)
    | eval_Econst_float:   forall f ty,
        eval_expr (Econst_float f ty) (Vfloat f)
    | eval_Econst_single:   forall f ty,
        eval_expr (Econst_single f ty) (Vsingle f)
    | eval_Econst_long:   forall i ty,
        eval_expr (Econst_long i ty) (Vlong i)
    | eval_Etempvar:  forall id ty v,
        le!id = Some v ->
        eval_expr (Etempvar id ty) v
    | eval_Eaddrof: forall a ty loc ofs,
        eval_lvalue a loc ofs Full ->
        eval_expr (Eaddrof a ty) (Vptr loc ofs)
    | eval_Eunop:  forall op a ty v1 v,
        eval_expr a v1 ->
        sem_unary_operation op v1 (typeof a) m = Some v \/
        sem_unary_operation op v1 (typeof a) pm = Some v ->
        eval_expr (Eunop op a ty) v
    | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
        eval_expr a1 v1 ->
        eval_expr a2 v2 ->
        sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m = Some v \/
        sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) pm = Some v ->
        eval_expr (Ebinop op a1 a2 ty) v
    | eval_Ecast:   forall a ty v1 v,
        eval_expr a v1 ->
        sem_cast v1 (typeof a) ty m = Some v \/
        sem_cast v1 (typeof a) ty pm = Some v ->
        eval_expr (Ecast a ty) v
    | eval_Esizeof: forall ty1 ty,
        eval_expr (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
    | eval_Ealignof: forall ty1 ty,
        eval_expr (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof ge ty1)))
    | eval_Elvalue: forall a loc bf ofs v,
        eval_lvalue a loc ofs bf ->
        deref_loc (typeof a) m loc ofs bf v ->
        eval_expr a v
    | eval_Elvalue_pm: forall a loc bf ofs v,
        eval_lvalue a loc ofs bf ->
        deref_loc (typeof a) pm loc ofs bf v ->
        eval_expr a v
    with eval_lvalue: expr -> block -> ptrofs -> bitfield -> Prop :=
    | eval_Evar_local:   forall id l ty,
        e!id = Some(l, ty) ->
        eval_lvalue (Evar id ty) l Ptrofs.zero Full
    | eval_Evar_global: forall id l ty,
        e!id = None ->
        Genv.find_symbol ge id = Some l ->
        eval_lvalue (Evar id ty) l Ptrofs.zero Full
    | eval_Ederef: forall a ty l ofs,
        eval_expr a (Vptr l ofs) ->
        eval_lvalue (Ederef a ty) l ofs Full
    | eval_Efield_struct:   forall a i ty l ofs id co att delta bf,
        eval_expr a (Vptr l ofs) ->
        typeof a = Tstruct id att ->
        ge.(genv_cenv)!id = Some co ->
        field_offset ge i (co_members co) = OK (delta, bf) ->
        eval_lvalue (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf
    | eval_Efield_union:   forall a i ty l ofs id co att delta bf,
        eval_expr a (Vptr l ofs) ->
        typeof a = Tunion id att ->
        ge.(genv_cenv)!id = Some co ->
        union_field_offset ge i (co_members co) = OK (delta, bf) ->
        eval_lvalue (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf.

    Scheme eval_expr_ind2 := Minimality for eval_expr Sort Prop
        with eval_lvalue_ind2 := Minimality for eval_lvalue Sort Prop.
    Combined Scheme eval_expr_lvalue_ind from eval_expr_ind2, eval_lvalue_ind2.

    Inductive eval_exprlist: list expr -> typelist -> list val -> Prop :=
    | eval_Enil:
      eval_exprlist nil Tnil nil
    | eval_Econs:   forall a bl ty tyl v1 v2 vl,
        eval_expr a v1 ->
        sem_cast v1 (typeof a) ty m = Some v2 \/
        sem_cast v1 (typeof a) ty pm = Some v2 ->
        eval_exprlist bl tyl vl ->
        eval_exprlist (a :: bl) (Tcons ty tyl) (v2 :: vl).

  End EXPR.

  Variable function_entry: function -> list val -> mem -> env -> temp_env -> mem -> Prop.

  Inductive step: Clight.state * mem -> trace -> Clight.state * mem -> Prop :=

  | step_assign:   forall f a1 a2 k e le m pm loc ofs bf v2 v m',
      eval_lvalue e le m pm a1 loc ofs bf ->
      eval_expr e le m pm a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v \/
      sem_cast v2 (typeof a2) (typeof a1) pm = Some v ->
      assign_loc ge (typeof a1) m loc ofs bf v m' ->
      step (State f (Sassign a1 a2) k e le m, pm)
           E0 (State f Sskip k e le m', pm)

  | step_assign_pm:   forall f a1 a2 k e le m pm loc ofs bf v2 v pm',
      eval_lvalue e le m pm a1 loc ofs bf ->
      eval_expr e le m pm a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v \/
      sem_cast v2 (typeof a2) (typeof a1) pm = Some v ->
      assign_loc ge (typeof a1) pm loc ofs bf v pm' ->
      step (State f (Sassign a1 a2) k e le m, pm)
           E0 (State f Sskip k e le m, pm')

  | step_set:   forall f id a k e le m pm v,
      eval_expr e le m pm a v ->
      step (State f (Sset id a) k e le m, pm)
           E0 (State f Sskip k e (PTree.set id v le) m, pm)

  | step_call:   forall f optid a al k e le m pm tyargs tyres cconv vf vargs fd,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr e le m pm a vf ->
      eval_exprlist e le m pm al tyargs vargs ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction tyargs tyres cconv ->
      step (State f (Scall optid a al) k e le m, pm)
           E0 (Callstate vf vargs (Kcall optid f e le k) m, pm)

  | step_builtin:   forall f optid ef tyargs al k e le m pm vargs t vres m',
      eval_exprlist e le m pm al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      step (State f (Sbuiltin optid ef tyargs al) k e le m, pm)
           t (State f Sskip k e (set_opttemp optid vres le) m', pm)

  | step_seq:  forall f s1 s2 k e le m pm,
      step (State f (Ssequence s1 s2) k e le m, pm)
           E0 (State f s1 (Kseq s2 k) e le m, pm)
  | step_skip_seq: forall f s k e le m pm,
      step (State f Sskip (Kseq s k) e le m, pm)
           E0 (State f s k e le m, pm)
  | step_continue_seq: forall f s k e le m pm,
      step (State f Scontinue (Kseq s k) e le m, pm)
           E0 (State f Scontinue k e le m, pm)
  | step_break_seq: forall f s k e le m pm,
      step (State f Sbreak (Kseq s k) e le m, pm)
           E0 (State f Sbreak k e le m, pm)

  | step_ifthenelse:  forall f a s1 s2 k e le m pm v1 b,
      eval_expr e le m pm a v1 ->
      bool_val v1 (typeof a) m = Some b \/
      bool_val v1 (typeof a) pm = Some b ->
      step (State f (Sifthenelse a s1 s2) k e le m, pm)
           E0 (State f (if b then s1 else s2) k e le m, pm)

  | step_loop: forall f s1 s2 k e le m pm,
      step (State f (Sloop s1 s2) k e le m, pm)
           E0 (State f s1 (Kloop1 s1 s2 k) e le m, pm)
  | step_skip_or_continue_loop1:  forall f s1 s2 k e le m pm x,
      x = Sskip \/ x = Scontinue ->
      step (State f x (Kloop1 s1 s2 k) e le m, pm)
           E0 (State f s2 (Kloop2 s1 s2 k) e le m, pm)
  | step_break_loop1:  forall f s1 s2 k e le m pm,
      step (State f Sbreak (Kloop1 s1 s2 k) e le m, pm)
           E0 (State f Sskip k e le m, pm)
  | step_skip_loop2: forall f s1 s2 k e le m pm,
      step (State f Sskip (Kloop2 s1 s2 k) e le m, pm)
           E0 (State f (Sloop s1 s2) k e le m, pm)
  | step_break_loop2: forall f s1 s2 k e le m pm,
      step (State f Sbreak (Kloop2 s1 s2 k) e le m, pm)
           E0 (State f Sskip k e le m, pm)

  | step_return_0: forall f k e le m m' pm,
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      step (State f (Sreturn None) k e le m, pm)
           E0 (Returnstate Vundef (call_cont k) m', pm)
  | step_return_1: forall f a k e le m v v' m' pm,
      eval_expr e le m pm a v ->
      sem_cast v (typeof a) f.(fn_return) m = Some v' \/
      sem_cast v (typeof a) f.(fn_return) pm = Some v' ->
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      step (State f (Sreturn (Some a)) k e le m, pm)
           E0 (Returnstate v' (call_cont k) m', pm)
  | step_skip_call: forall f k e le m m' pm,
      is_call_cont k ->
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      step (State f Sskip k e le m, pm)
           E0 (Returnstate Vundef k m', pm)

  | step_switch: forall f a sl k e le m pm v n,
      eval_expr e le m pm a v ->
      sem_switch_arg v (typeof a) = Some n ->
      step (State f (Sswitch a sl) k e le m, pm)
           E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m, pm)
  | step_skip_break_switch: forall f x k e le m pm,
      x = Sskip \/ x = Sbreak ->
      step (State f x (Kswitch k) e le m, pm)
           E0 (State f Sskip k e le m, pm)
  | step_continue_switch: forall f k e le m pm,
      step (State f Scontinue (Kswitch k) e le m, pm)
           E0 (State f Scontinue k e le m, pm)

  | step_label: forall f lbl s k e le m pm,
      step (State f (Slabel lbl s) k e le m, pm)
           E0 (State f s k e le m, pm)

  | step_goto: forall f lbl k e le m pm s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
      step (State f (Sgoto lbl) k e le m, pm)
           E0 (State f s' k' e le m, pm)

  | step_internal_function: forall vf f vargs k m pm e le m1,
    forall FIND: Genv.find_funct ge vf = Some (Internal f),
      function_entry f vargs m e le m1 ->
      step (Callstate vf vargs k m, pm)
           E0 (State f f.(fn_body) k e le m1, pm)

  | step_external_function: forall vf ef targs tres cconv vargs k m pm vres t m',
    forall FIND: Genv.find_funct ge vf = Some (External ef targs tres cconv),
      external_call ef ge vargs m t vres m' ->
      step (Callstate vf vargs k m, pm)
           t (Returnstate vres k m', pm)

  | step_returnstate: forall v optid f e le k pm m,
      step (Returnstate v (Kcall optid f e le k) m, pm)
           E0 (State f Sskip k e (set_opttemp optid v le) m, pm).

  Inductive initial_state: c_query * mem -> Clight.state * mem -> Prop :=
  | initial_state_intro: forall vf f targs tres tcc vargs m pm,
      Genv.find_funct ge vf = Some (Internal f) ->
      type_of_function f = Tfunction targs tres tcc ->
      val_casted_list vargs targs ->
      Sup.sup_include (Genv.genv_sup ge) (Mem.support m) ->
      initial_state
        (cq vf (signature_of_type targs tres tcc) vargs m, pm)
        (Callstate vf vargs Kstop m, pm).

  Inductive at_external: Clight.state * mem -> c_query * mem -> Prop :=
  | at_external_intro name sg targs tres cconv vf vargs k m pm:
      let f := External (EF_external name sg) targs tres cconv in
      Genv.find_funct ge vf = Some f ->
      at_external
        (Callstate vf vargs k m, pm)
        (cq vf sg vargs m, pm).

  (** Re-entrant calls are possible *)
  Inductive after_external: Clight.state * mem -> c_reply * mem -> Clight.state * mem -> Prop :=
  | after_external_intro vf vargs k m pm vres m' pm':
      after_external
        (Callstate vf vargs k m, pm)
        (cr vres m', pm')
        (Returnstate vres k m', pm').

  Inductive final_state: Clight.state * mem -> c_reply * mem -> Prop :=
  | final_state_intro: forall r m pm,
      final_state
        (Returnstate r Kstop m, pm)
        (cr r m, pm).

End Clight.

Definition estep1 (ge: genv) := step ge (function_entry1 ge).
Definition estep2 (ge: genv) := step ge (function_entry2 ge).

Program Definition eclight1 (p: program) :=
  {|
    init_pstate := Mem.empty;
    esem := Semantics_gen estep1
                         initial_state
                         at_external
                         (fun _ => after_external)
                         (fun _ => final_state)
                         globalenv p
  |}.

Program Definition eclight2 (p: program) :=
  {|
    init_pstate := Mem.empty;
    esem := Semantics_gen estep2
                         initial_state
                         at_external
                         (fun _ => after_external)
                         (fun _ => final_state)
                         globalenv p
  |}.
