(** Preliminary experiments about incorporating state encapsulation into
  CompCert languages *)

From compcert Require Import
     AST Coqlib Maps Values Integers Cop Ctypes Errors Events
     LanguageInterface Smallstep Globalenvs Clight Memory Floats.
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

Module ClightP.

  Inductive val : Type :=
  | Val : Values.val -> val
  | Array : nat -> ZMap.t val -> val
  | Struct : list ident -> PMap.t val -> val.

  Record privvar (V: Type) : Type :=
    mkprivvar {
        pvar_info: V;         (**r language-dependent info, e.g. a type *)
        pvar_init: val;       (**r initialization data *)
      }.

  Inductive expr : Type :=
  | Econst_int: int -> type -> expr       (**r integer literal *)
  | Econst_float: float -> type -> expr   (**r double float literal *)
  | Econst_single: float32 -> type -> expr (**r single float literal *)
  | Econst_long: int64 -> type -> expr    (**r long integer literal *)
  | Evar: ident -> type -> expr           (**r variable *)
  | Etempvar: ident -> type -> expr       (**r temporary variable *)
  | Ederef: expr -> type -> expr          (**r pointer dereference (unary [*]) *)
  | Eaddrof: expr -> type -> expr         (**r address-of operator ([&]) *)
  | Eunop: unary_operation -> expr -> type -> expr  (**r unary operation *)
  | Ebinop: binary_operation -> expr -> expr -> type -> expr (**r binary operation *)
  | Ecast: expr -> type -> expr   (**r type cast ([(ty) e]) *)
  | Efield: expr -> ident -> type -> expr (**r access to a member of a struct or union *)
  | Esizeof: type -> type -> expr         (**r size of a type *)
  | Ealignof: type -> type -> expr        (**r alignment of a type *)
  (* two new cases for persistent data and struct and array *)
  | Epvar : ident -> type -> expr
  | Eaccess : expr -> Z + ident -> type -> expr.

  Definition typeof (e: expr) : type :=
    match e with
    | Econst_int _ ty => ty
    | Econst_float _ ty => ty
    | Econst_single _ ty => ty
    | Econst_long _ ty => ty
    | Evar _ ty => ty
    | Etempvar _ ty => ty
    | Ederef _ ty => ty
    | Eaddrof _ ty => ty
    | Eunop _ _ ty => ty
    | Ebinop _ _ _ ty => ty
    | Ecast _ ty => ty
    | Efield _ _ ty => ty
    | Esizeof _ ty => ty
    | Ealignof _ ty => ty
    | Epvar _ ty => ty
    | Eaccess _ _ ty => ty
    end.

  Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Sassign : expr -> expr -> statement (**r assignment [lvalue = rvalue] *)
  | Sset : ident -> expr -> statement   (**r assignment [tempvar = rvalue] *)
  | Scall: option ident -> expr -> list expr -> statement (**r function call *)
  | Sbuiltin: option ident -> external_function -> typelist -> list expr -> statement (**r builtin invocation *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
  | Sloop: statement -> statement -> statement (**r infinite loop *)
  | Sbreak : statement                      (**r [break] statement *)
  | Scontinue : statement                   (**r [continue] statement *)
  | Sreturn : option expr -> statement      (**r [return] statement *)
  | Sswitch : expr -> labeled_statements -> statement  (**r [switch] statement *)
  | Slabel : label -> statement -> statement
  | Sgoto : label -> statement

  | Supdate : expr -> expr -> statement

  with labeled_statements : Type :=            (**r cases of a [switch] *)
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements.
  (**r [None] is [default], [Some x] is [case x] *)

  Fixpoint select_switch_default (sl: labeled_statements): labeled_statements :=
    match sl with
    | LSnil => sl
    | LScons None s sl' => sl
    | LScons (Some i) s sl' => select_switch_default sl'
    end.

  Fixpoint select_switch_case (n: Z) (sl: labeled_statements): option labeled_statements :=
    match sl with
    | LSnil => None
    | LScons None s sl' => select_switch_case n sl'
    | LScons (Some c) s sl' => if zeq c n then Some sl else select_switch_case n sl'
    end.

  Definition select_switch (n: Z) (sl: labeled_statements): labeled_statements :=
    match select_switch_case n sl with
    | Some sl' => sl'
    | None => select_switch_default sl
    end.

  (** Turn a labeled statement into a sequence *)

  Fixpoint seq_of_labeled_statement (sl: labeled_statements) : statement :=
    match sl with
    | LSnil => Sskip
    | LScons _ s sl' => Ssequence s (seq_of_labeled_statement sl')
    end.

  Record function : Type :=
    mkfunction {
        fn_return: type;
        fn_callconv: calling_convention;
        fn_params: list (ident * type);
        fn_vars: list (ident * type);
        fn_temps: list (ident * type);
        fn_body: statement
      }.
  Definition fundef := Ctypes.fundef function.
  Definition type_of_function (f: function) : type :=
    Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

  Definition type_of_fundef (f: fundef) : type :=
    match f with
    | Internal fd => type_of_function fd
    | External id args res cc => Tfunction args res cc
    end.


  Record program : Type := {
      prog_defs: list (ident * globdef fundef type);
      prog_private: list (ident * privvar type);
      prog_public: list ident;
      prog_main: ident;
      prog_types: list composite_definition;
      prog_comp_env: composite_env;
      prog_comp_env_eq: build_composite_env prog_types = OK prog_comp_env
    }.

  Definition program_of_program (p: program) : AST.program fundef type :=
    {|
      AST.prog_defs := p.(prog_defs);
      AST.prog_public := p.(prog_public);
      AST.prog_main := p.(prog_main); |}.
  Coercion program_of_program: program >-> AST.program.

  Record genv := { genv_genv :> Genv.t fundef type;
                   genv_cenv :> composite_env }.

  Definition globalenv (se: Genv.symtbl) (p: program) :=
    {| genv_genv := Genv.globalenv se p; genv_cenv := p.(prog_comp_env) |}.

  Section SEM.
    Definition penv : Type := PTree.t val.
    Variable ge: genv.

    Inductive alloc_variables: env -> mem ->
                               list (ident * type) ->
                               env -> mem -> Prop :=
    | alloc_variables_nil:
      forall e m,
        alloc_variables e m nil e m
    | alloc_variables_cons:
      forall e m id ty vars m1 b1 m2 e2,
        Mem.alloc m 0 (sizeof ge ty) = (m1, b1) ->
        alloc_variables (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
        alloc_variables e m ((id, ty) :: vars) e2 m2.

    Inductive bind_parameters (e: env):
                               mem ->
                               list (ident * type) -> list Values.val ->
                               mem -> Prop :=
    | bind_parameters_nil:
      forall m,
        bind_parameters e m nil nil m
    | bind_parameters_cons:
      forall m id ty params v1 vl b m1 m2,
        PTree.get id e = Some(b, ty) ->
        assign_loc ge ty m b Ptrofs.zero Full v1 m1 ->
        bind_parameters e m1 params vl m2 ->
        bind_parameters e m ((id, ty) :: params) (v1 :: vl) m2.

    Section EXPR.

      Variable e: env.
      Variable le: temp_env.
      Variable pe: penv.
      Variable m: mem.

      Coercion Val : Values.val >-> val.

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
          eval_expr a (Val v1) ->
          sem_unary_operation op v1 (typeof a) m = Some v ->
          eval_expr (Eunop op a ty) v
      | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
          eval_expr a1 (Val v1) ->
          eval_expr a2 (Val v2) ->
          sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m = Some v ->
          eval_expr (Ebinop op a1 a2 ty) v
      | eval_Ecast:   forall a ty v1 v,
          eval_expr a (Val v1) ->
          sem_cast v1 (typeof a) ty m = Some v ->
          eval_expr (Ecast a ty) v
      | eval_Esizeof: forall ty1 ty,
          eval_expr (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
      | eval_Ealignof: forall ty1 ty,
          eval_expr (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof ge ty1)))
      | eval_Elvalue: forall a loc ofs bf v,
          eval_lvalue a loc ofs bf ->
          deref_loc (typeof a) m loc ofs bf v ->
          eval_expr a v
      (* the new case *)
      | eval_Epvar: forall id ty v,
          pe!id = Some v ->
          eval_expr (Epvar id ty) v
      | eval_Earray: forall a i ty v sz vs,
          eval_expr a (Array sz vs) ->
          i < Z.of_nat sz ->
          ZMap.get i vs = v ->
          eval_expr (Eaccess a (inl i) ty) v
      | eval_Estruct: forall a f ty v fs vs,
          eval_expr a (Struct fs vs) ->
          In f fs ->
          PMap.get f vs = v ->
          eval_expr (Eaccess a (inr f) ty) v

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

      Inductive eval_exprlist: list expr -> typelist -> list Values.val -> Prop :=
      | eval_Enil:
        eval_exprlist nil Tnil nil
      | eval_Econs:   forall a bl ty tyl v1 v2 vl,
          eval_expr a (Val v1) ->
          sem_cast v1 (typeof a) ty m = Some v2 ->
          eval_exprlist bl tyl vl ->
          eval_exprlist (a :: bl) (Tcons ty tyl) (v2 :: vl).

    End EXPR.

    Definition block_of_binding (id_b_ty: ident * (block * type)) :=
      match id_b_ty with (id, (b, ty)) => (b, 0, sizeof ge ty) end.

    Definition blocks_of_env (e: env) : list (block * Z * Z) :=
      List.map block_of_binding (PTree.elements e).

    (** Transition relation *)

    Inductive cont: Type :=
    | Kstop: cont
    | Kseq: statement -> cont -> cont
    | Kloop1: statement -> statement -> cont -> cont
    | Kloop2: statement -> statement -> cont -> cont
    | Kswitch: cont -> cont
    | Kcall: option ident -> function -> env -> temp_env -> cont -> cont.

    Fixpoint call_cont (k: cont) : cont :=
      match k with
      | Kseq s k => call_cont k
      | Kloop1 s1 s2 k => call_cont k
      | Kloop2 s1 s2 k => call_cont k
      | Kswitch k => call_cont k
      | _ => k
      end.

    Definition is_call_cont (k: cont) : Prop :=
      match k with
      | Kstop => True
      | Kcall _ _ _ _ _ => True
      | _ => False
      end.

    Inductive state: Type :=
    | State (f: function) (s: statement) (k: cont)
            (e: env) (le: temp_env) (m: mem) : state
    | Callstate (vf: Values.val) (args: list Values.val)
                (k: cont) (m: mem) : state
    | Returnstate (res: Values.val) (k: cont) (m: mem) : state.

    Fixpoint find_label (lbl: label) (s: statement) (k: cont)
             {struct s}: option (statement * cont) :=
      match s with
      | Ssequence s1 s2 =>
          match find_label lbl s1 (Kseq s2 k) with
          | Some sk => Some sk
          | None => find_label lbl s2 k
          end
      | Sifthenelse a s1 s2 =>
          match find_label lbl s1 k with
          | Some sk => Some sk
          | None => find_label lbl s2 k
          end
      | Sloop s1 s2 =>
          match find_label lbl s1 (Kloop1 s1 s2 k) with
          | Some sk => Some sk
          | None => find_label lbl s2 (Kloop2 s1 s2 k)
          end
      | Sswitch e sl =>
          find_label_ls lbl sl (Kswitch k)
      | Slabel lbl' s' =>
          if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
      | _ => None
      end

    with find_label_ls (lbl: label) (sl: labeled_statements) (k: cont)
                       {struct sl}: option (statement * cont) :=
           match sl with
           | LSnil => None
           | LScons _ s sl' =>
               match find_label lbl s (Kseq (seq_of_labeled_statement sl') k) with
               | Some sk => Some sk
               | None => find_label_ls lbl sl' k
               end
           end.

    Fixpoint update_penv_helper (a: expr) (v: val) (w: Values.val) : option (ident * val) :=
      match a, v with
      | Epvar i _, Val _ => Some (i, Val w)
      | Eaccess e (inl x) _, Array sz vs =>
          match update_penv_helper e (ZMap.get x vs) w with
          | Some (i, v') => Some (i, Array sz (ZMap.set x v' vs))
          | None => None
          end
      | Eaccess e (inr f) _, Struct fs vs =>
          match update_penv_helper e (PMap.get f vs) w with
          | Some (i, v') => Some (i, Struct fs (PMap.set f v' vs))
          | None => None
          end
      | _, _ => None
      end.

    Variable function_entry:
      function -> list Values.val -> mem -> env -> temp_env -> mem -> Prop.

    Inductive step: state * penv -> trace -> state * penv -> Prop :=

    | step_assign:   forall f a1 a2 k e le pe m loc ofs bf v2 v m',
        eval_lvalue e le pe m a1 loc ofs bf ->
        eval_expr e le pe m a2 (Val v2) ->
        sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
        assign_loc ge (typeof a1) m loc ofs bf v m' ->
        step (State f (Sassign a1 a2) k e le m, pe)
             E0 (State f Sskip k e le m', pe)

    | step_set:   forall f id a k e le pe m v,
        eval_expr e le pe m a (Val v) ->
        step (State f (Sset id a) k e le m, pe)
             E0 (State f Sskip k e (PTree.set id v le) m, pe)

    | step_update: forall f a1 a2 k e le pe m id v w v' w',
        eval_expr e le pe m a1 v ->
        eval_expr e le pe m a2 (Val w) ->
        sem_cast w (typeof a2) (typeof a1) m = Some w' ->
        update_penv_helper a1 v w = Some (id, v') ->
        step (State f (Supdate a1 a2) k e le m, pe)
             E0 (State f Sskip k e le m, PTree.set id v pe)

    | step_call:   forall f optid a al k e le pe m tyargs tyres cconv vf vargs fd,
        classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
        eval_expr e le pe m a (Val vf) ->
        eval_exprlist e le pe m al tyargs vargs ->
        Genv.find_funct ge vf = Some fd ->
        type_of_fundef fd = Tfunction tyargs tyres cconv ->
        step (State f (Scall optid a al) k e le m, pe)
             E0 (Callstate vf vargs (Kcall optid f e le k) m, pe)

    | step_builtin:   forall f optid ef tyargs al k e le pe m vargs t vres m',
        eval_exprlist e le pe m al tyargs vargs ->
        external_call ef ge vargs m t vres m' ->
        step (State f (Sbuiltin optid ef tyargs al) k e le m, pe)
             t (State f Sskip k e (set_opttemp optid vres le) m', pe)

    | step_seq:  forall f s1 s2 k e le pe m,
        step (State f (Ssequence s1 s2) k e le m, pe)
             E0 (State f s1 (Kseq s2 k) e le m, pe)
    | step_skip_seq: forall f s k e le pe m,
        step (State f Sskip (Kseq s k) e le m, pe)
             E0 (State f s k e le m, pe)
    | step_continue_seq: forall f s k e le pe m,
        step (State f Scontinue (Kseq s k) e le m, pe)
             E0 (State f Scontinue k e le m, pe)
    | step_break_seq: forall f s k e le pe m,
        step (State f Sbreak (Kseq s k) e le m, pe)
             E0 (State f Sbreak k e le m, pe)

    | step_ifthenelse:  forall f a s1 s2 k e le pe m v1 b,
        eval_expr e le pe m a (Val v1) ->
        bool_val v1 (typeof a) m = Some b ->
        step (State f (Sifthenelse a s1 s2) k e le m, pe)
             E0 (State f (if b then s1 else s2) k e le m, pe)

    | step_loop: forall f s1 s2 k e le pe m,
        step (State f (Sloop s1 s2) k e le m, pe)
             E0 (State f s1 (Kloop1 s1 s2 k) e le m, pe)
    | step_skip_or_continue_loop1:  forall f s1 s2 k e le pe m x,
        x = Sskip \/ x = Scontinue ->
        step (State f x (Kloop1 s1 s2 k) e le m, pe)
             E0 (State f s2 (Kloop2 s1 s2 k) e le m, pe)
    | step_break_loop1:  forall f s1 s2 k e le pe m,
        step (State f Sbreak (Kloop1 s1 s2 k) e le m, pe)
             E0 (State f Sskip k e le m, pe)
    | step_skip_loop2: forall f s1 s2 k e le pe m,
        step (State f Sskip (Kloop2 s1 s2 k) e le m, pe)
             E0 (State f (Sloop s1 s2) k e le m, pe)
    | step_break_loop2: forall f s1 s2 k e le pe m,
        step (State f Sbreak (Kloop2 s1 s2 k) e le m, pe)
             E0 (State f Sskip k e le m, pe)

    | step_return_0: forall f k e le pe m m',
        Mem.free_list m (blocks_of_env e) = Some m' ->
        step (State f (Sreturn None) k e le m, pe)
             E0 (Returnstate Vundef (call_cont k) m', pe)
    | step_return_1: forall f a k e le pe m v v' m',
        eval_expr e le pe m a (Val v) ->
        sem_cast v (typeof a) f.(fn_return) m = Some v' ->
        Mem.free_list m (blocks_of_env e) = Some m' ->
        step (State f (Sreturn (Some a)) k e le m, pe)
             E0 (Returnstate v' (call_cont k) m', pe)
    | step_skip_call: forall f k e le pe m m',
        is_call_cont k ->
        Mem.free_list m (blocks_of_env e) = Some m' ->
        step (State f Sskip k e le m, pe)
             E0 (Returnstate Vundef k m', pe)

    | step_switch: forall f a sl k e le pe m v n,
        eval_expr e le pe m a (Val v) ->
        sem_switch_arg v (typeof a) = Some n ->
        step (State f (Sswitch a sl) k e le m, pe)
             E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le m, pe)
    | step_skip_break_switch: forall f x k e le pe m,
        x = Sskip \/ x = Sbreak ->
        step (State f x (Kswitch k) e le m, pe)
             E0 (State f Sskip k e le m, pe)
    | step_continue_switch: forall f k e le pe m,
        step (State f Scontinue (Kswitch k) e le m, pe)
             E0 (State f Scontinue k e le m, pe)

    | step_label: forall f lbl s k e le pe m,
        step (State f (Slabel lbl s) k e le m, pe)
             E0 (State f s k e le m, pe)

    | step_goto: forall f lbl k e le pe m s' k',
        find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
        step (State f (Sgoto lbl) k e le m, pe)
             E0 (State f s' k' e le m, pe)

    | step_internal_function: forall vf f vargs k m e le pe m1,
      forall FIND: Genv.find_funct ge vf = Some (Internal f),
        function_entry f vargs m e le m1 ->
        step (Callstate vf vargs k m, pe)
             E0 (State f f.(fn_body) k e le m1, pe)

    | step_external_function: forall vf ef targs tres cconv vargs k m vres t m' pe,
      forall FIND: Genv.find_funct ge vf = Some (External ef targs tres cconv),
        external_call ef ge vargs m t vres m' ->
        step (Callstate vf vargs k m, pe)
             t (Returnstate vres k m', pe)

    | step_returnstate: forall v optid f e le pe k m,
        step (Returnstate v (Kcall optid f e le k) m, pe)
             E0 (State f Sskip k e (set_opttemp optid v le) m, pe).

    Inductive initial_state: c_query * penv -> state * penv -> Prop :=
    | initial_state_intro: forall vf f targs tres tcc vargs m pe,
        Genv.find_funct ge vf = Some (Internal f) ->
        type_of_function f = Tfunction targs tres tcc ->
        val_casted_list vargs targs ->
        Mem.sup_include (Genv.genv_sup ge) (Mem.support m) ->
        initial_state
          (cq vf (signature_of_type targs tres tcc) vargs m, pe)
          (Callstate vf vargs Kstop m, pe).

    Inductive at_external: state * penv -> c_query * penv -> Prop :=
    | at_external_intro name sg targs tres cconv vf vargs k m pe:
      let f := External (EF_external name sg) targs tres cconv in
      Genv.find_funct ge vf = Some f ->
      at_external
        (Callstate vf vargs k m, pe)
        (cq vf sg vargs m, pe).

    Inductive after_external: state * penv -> c_reply * penv -> state * penv -> Prop :=
    | after_external_intro vf vargs k m pe vres m' pe':
      after_external
        (Callstate vf vargs k m, pe)
        (cr vres m', pe')
        (Returnstate vres k m', pe').

    Inductive final_state: state * penv -> c_reply * penv -> Prop :=
    | final_state_intro: forall r m pe,
        final_state
          (Returnstate r Kstop m, pe)
          (cr r m, pe).

  End SEM.

  Inductive function_entry1 (ge: genv) (f: function) (vargs: list Values.val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
  | function_entry1_intro: forall m1,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters ge e m1 f.(fn_params) vargs m' ->
      le = create_undef_temps f.(fn_temps) ->
      function_entry1 ge f vargs m e le m'.

  Definition step1 (ge: genv) := step ge (function_entry1 ge).

  (** Second, parameters as temporaries. *)

  Inductive function_entry2 (ge: genv)  (f: function) (vargs: list Values.val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
  | function_entry2_intro:
    list_norepet (var_names f.(fn_vars)) ->
    list_norepet (var_names f.(fn_params)) ->
    list_disjoint (var_names f.(fn_params)) (var_names f.(fn_temps)) ->
    alloc_variables ge empty_env m f.(fn_vars) e m' ->
    bind_parameter_temps f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
    function_entry2 ge f vargs m e le m'.

  Definition step2 (ge: genv) := step ge (function_entry2 ge).

  Definition add_private (pe: penv) (x: ident * privvar type) : penv :=
    match x with
      (i, v) => PTree.set i (pvar_init _ v) pe
    end.

  Definition empty_penv : penv := PTree.empty val.

  Definition add_privates (pe: penv) (x: list (ident * privvar type)) : penv :=
    List.fold_left add_private x pe.

  Program Definition clightp1 (p : program) : esemantics li_c li_c :=
    {|
      pstate := penv;
      init_pstate := add_privates empty_penv (prog_private p);
      esem := Semantics_gen step1
                            initial_state
                            at_external
                            (fun _ => after_external)
                            (fun _ => final_state)
                            globalenv p;
    |}.

End ClightP.

Section ClightM.

  Variable ge: Clight.genv.

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

End ClightM.

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
