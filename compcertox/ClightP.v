From compcert Require Import
     AST Coqlib Maps Values Integers Errors Events
     LanguageInterface Smallstep Globalenvs Memory Floats.
From compcert Require Import
     CategoricalComp.
From compcert.compcertox Require Import
     TensorComp Lifting Encapsulation.
Require Import Ctypes Cop Clight.

(** ** ClightP semantics *)
Module ClightP.

  Inductive val : Type :=
  | Val : Values.val -> type -> val.
  (* | Array : nat -> ZMap.t val -> val *)
  (* | Struct : list ident -> PMap.t val -> val. *)

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
  | Epvar : ident -> type -> expr.
  (* | Eaccess : expr -> Z + ident -> type -> expr. *)

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
    (* | Eaccess _ _ ty => ty *)
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
    Open Scope Z_scope.

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

      (* Coercion Val : Values.val >-> val. *)

      Inductive eval_expr: expr -> val -> Prop :=
      | eval_Econst_int:   forall i ty,
          eval_expr (Econst_int i ty) (Val (Vint i) ty)
      | eval_Econst_float:   forall f ty,
          eval_expr (Econst_float f ty) (Val (Vfloat f) ty)
      | eval_Econst_single:   forall f ty,
          eval_expr (Econst_single f ty) (Val (Vsingle f) ty)
      | eval_Econst_long:   forall i ty,
          eval_expr (Econst_long i ty) (Val (Vlong i) ty)
      | eval_Etempvar:  forall id ty v,
          le!id = Some v ->
          eval_expr (Etempvar id ty) (Val v ty)
      | eval_Eaddrof: forall a ty loc ofs,
          eval_lvalue a loc ofs Full ->
          eval_expr (Eaddrof a ty) (Val (Vptr loc ofs) ty)
      | eval_Eunop:  forall op a ty v1 v tyv,
          eval_expr a (Val v1 tyv) ->
          sem_unary_operation op v1 (typeof a) m = Some v ->
          eval_expr (Eunop op a ty) (Val v ty)
      | eval_Ebinop: forall op a1 a2 ty v1 v2 v tyv1 tyv2,
          eval_expr a1 (Val v1 tyv1) ->
          eval_expr a2 (Val v2 tyv2) ->
          sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m = Some v ->
          eval_expr (Ebinop op a1 a2 ty) (Val v ty)
      | eval_Ecast:   forall a ty v1 v tyv,
          eval_expr a (Val v1 tyv) ->
          sem_cast v1 (typeof a) ty m = Some v ->
          eval_expr (Ecast a ty) (Val v ty)
      | eval_Esizeof: forall ty1 ty,
          eval_expr (Esizeof ty1 ty) (Val (Vptrofs (Ptrofs.repr (sizeof ge ty1))) ty)
      | eval_Ealignof: forall ty1 ty,
          eval_expr (Ealignof ty1 ty) (Val (Vptrofs (Ptrofs.repr (alignof ge ty1))) ty)
      | eval_Elvalue: forall a loc ofs bf v,
          eval_lvalue a loc ofs bf ->
          deref_loc (typeof a) m loc ofs bf v ->
          eval_expr a (Val v (typeof a))
      (* the new case *)
      | eval_Epvar: forall id ty v,
          (* note that we require the types of the value and the expression to
             be the same *)
          pe!id = Some (Val v ty) ->
          eval_expr (Epvar id ty) (Val v ty)
      (* | eval_Earray: forall a i ty v sz vs, *)
      (*     eval_expr a (Array sz vs) -> *)
      (*     i < Z.of_nat sz -> *)
      (*     ZMap.get i vs = v -> *)
      (*     eval_expr (Eaccess a (inl i) ty) v *)
      (* | eval_Estruct: forall a f ty v fs vs, *)
      (*     eval_expr a (Struct fs vs) -> *)
      (*     In f fs -> *)
      (*     PMap.get f vs = v -> *)
      (*     eval_expr (Eaccess a (inr f) ty) v *)

      with eval_lvalue: expr -> block -> ptrofs -> bitfield -> Prop :=
      | eval_Evar_local:   forall id l ty,
          e!id = Some(l, ty) ->
          eval_lvalue (Evar id ty) l Ptrofs.zero Full
      | eval_Evar_global: forall id l ty,
          e!id = None ->
          Genv.find_symbol ge id = Some l ->
          eval_lvalue (Evar id ty) l Ptrofs.zero Full
      | eval_Ederef: forall a ty l ofs tya,
          eval_expr a (Val (Vptr l ofs) tya) ->
          eval_lvalue (Ederef a ty) l ofs Full
      | eval_Efield_struct:   forall a i ty l ofs id co att delta bf tya,
          eval_expr a (Val (Vptr l ofs) tya) ->
          typeof a = Tstruct id att ->
          ge.(genv_cenv)!id = Some co ->
          field_offset ge i (co_members co) = OK (delta, bf) ->
          eval_lvalue (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf
      | eval_Efield_union:   forall a i ty l ofs id co att delta bf tya,
          eval_expr a (Val (Vptr l ofs) tya) ->
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
      | eval_Econs:   forall a bl ty tyl v1 v2 vl tya,
          eval_expr a (Val v1 tya) ->
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

    (* Fixpoint update_penv_helper (a: expr) (v: val) (w: Values.val) tyw : option (ident * val) := *)
    (*   match a, v with *)
    (*   | Epvar i _, Val _ _ => Some (i, Val w tyw) *)
    (*   | Eaccess e (inl x) _, Array sz vs => *)
    (*       match update_penv_helper e (ZMap.get x vs) w tyw with *)
    (*       | Some (i, v') => Some (i, Array sz (ZMap.set x v' vs)) *)
    (*       | None => None *)
    (*       end *)
    (*   | Eaccess e (inr f) _, Struct fs vs => *)
    (*       match update_penv_helper e (PMap.get f vs) w tyw with *)
    (*       | Some (i, v') => Some (i, Struct fs (PMap.set f v' vs)) *)
    (*       | None => None *)
    (*       end *)
    (*   | _, _ => None *)
    (*   end. *)

    Variable function_entry:
      function -> list Values.val -> mem -> env -> temp_env -> mem -> Prop.

    Inductive step: state * penv -> trace -> state * penv -> Prop :=

    | step_assign:   forall f a1 a2 k e le pe m loc ofs bf v2 v m' tyv,
        eval_lvalue e le pe m a1 loc ofs bf ->
        eval_expr e le pe m a2 (Val v2 tyv) ->
        sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
        assign_loc ge (typeof a1) m loc ofs bf v m' ->
        step (State f (Sassign a1 a2) k e le m, pe)
             E0 (State f Sskip k e le m', pe)

    | step_set:   forall f id a k e le pe m v tyv,
        eval_expr e le pe m a (Val v tyv) ->
        step (State f (Sset id a) k e le m, pe)
             E0 (State f Sskip k e (PTree.set id v le) m, pe)
    (* we need a penv_loc and define something like assign_loc *)
    (* By_value update *)
    | step_update: forall f a2 k e le pe m id ty new_v old_v ch,
        pe ! id = Some (Val old_v ty) ->
        access_mode ty = By_value ch ->
        eval_expr e le pe m a2 (Val new_v ty) ->
        val_casted new_v ty ->
        step (State f (Supdate (Epvar id ty) a2) k e le m, pe)
             E0 (State f Sskip k e le m, PTree.set id (Val new_v ty) pe)

    | step_call:   forall f optid a al k e le pe m tyargs tyres cconv vf vargs fd tyvf,
        classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
        eval_expr e le pe m a (Val vf tyvf) ->
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

    | step_ifthenelse:  forall f a s1 s2 k e le pe m v1 b tyv,
        eval_expr e le pe m a (Val v1 tyv) ->
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
    | step_return_1: forall f a k e le pe m v v' m' tyv,
        eval_expr e le pe m a (Val v tyv) ->
        sem_cast v (typeof a) f.(fn_return) m = Some v' ->
        Mem.free_list m (blocks_of_env e) = Some m' ->
        step (State f (Sreturn (Some a)) k e le m, pe)
             E0 (Returnstate v' (call_cont k) m', pe)
    | step_skip_call: forall f k e le pe m m',
        is_call_cont k ->
        Mem.free_list m (blocks_of_env e) = Some m' ->
        step (State f Sskip k e le m, pe)
             E0 (Returnstate Vundef k m', pe)

    | step_switch: forall f a sl k e le pe m v n tyv,
        eval_expr e le pe m a (Val v tyv) ->
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

    Inductive at_external: state * penv -> c_query -> Prop :=
    | at_external_intro name sg targs tres cconv vf vargs k m pe:
      let f := External (EF_external name sg) targs tres cconv in
      Genv.find_funct ge vf = Some f ->
      at_external
        (Callstate vf vargs k m, pe)
        (cq vf sg vargs m).

    Inductive after_external: state * penv -> c_reply -> state * penv -> Prop :=
    | after_external_intro vf vargs k m pe vres m':
      after_external
        (Callstate vf vargs k m, pe)
        (cr vres m')
        (Returnstate vres k m', pe).

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

  Program Definition clightp1 (p : program) : semantics _ (li_c@penv) :=
      Semantics_gen step1
        initial_state
        at_external
        (fun _ => after_external)
        (fun _ => final_state)
        globalenv p.

  Program Definition clightp2 (p : program) : semantics _ (li_c@penv) :=
      Semantics_gen step2
        initial_state
        at_external
        (fun _ => after_external)
        (fun _ => final_state)
        globalenv p.

End ClightP.

(** ** Compile ClightP to Clight *)

Section TRANSF.
  Open Scope Z_scope.
  Open Scope error_monad_scope.
  Import ClightP.

  Fixpoint transl_lvalue (a: expr) : res Clight.expr :=
    match a with
    | Epvar i ty => OK (Clight.Evar i ty)
    (* | Eaccess e (inr f) ty => *)
    (*     do te <- transl_lvalue e; *)
    (*     OK (Clight.Efield te f ty) *)
    (* | Eaccess e (inl i) ty => *)
    (*     do te <- transl_lvalue e; *)
    (*     OK (Clight.Ebinop Oadd te *)
    (*                          (Clight.Econst_int (Int.repr i) (Tint I32 Unsigned noattr)) *)
    (*                          (Tpointer ty noattr)) *)
    | _ => Error (msg "transl_lvalue")
    end.

  Fixpoint transl_expr (a: expr) : res Clight.expr :=
    match a with
    | Econst_int i ty => OK (Clight.Econst_int i ty)
    | Econst_float f ty => OK (Clight.Econst_float f ty)
    | Econst_single s ty => OK (Clight.Econst_single s ty)
    | Econst_long l ty => OK (Clight.Econst_long l ty)
    | Evar i ty => OK (Clight.Evar i ty)
    | Etempvar i ty => OK (Clight.Etempvar i ty)
    | Ederef e ty =>
        do te <- transl_expr e;
        OK (Clight.Ederef te ty)
    | Eaddrof e ty =>
        do te <- transl_expr e;
        OK (Clight.Eaddrof te ty)
    | Eunop op e ty =>
        do te <- transl_expr e;
        OK (Clight.Eunop op te ty)
    | Ebinop op e1 e2 ty =>
        do te1 <- transl_expr e1;
        do te2 <- transl_expr e2;
        OK (Clight.Ebinop op te1 te2 ty)
    | Ecast e ty =>
        do te <- transl_expr e;
        OK (Clight.Ecast te ty)
    | Efield e f ty =>
        do te <- transl_expr e;
        OK (Clight.Efield te f ty)
    | Esizeof t ty => OK (Clight.Esizeof t ty)
    | Ealignof t ty => OK (Clight.Ealignof t ty)
    | Epvar i ty =>
        OK (Clight.Evar i ty)
    (* | Eaccess e (inr f) ty => *)
    (*     do te <- transl_lvalue e; *)
    (*     OK (Clight.Ederef (Clight.Efield te f ty) ty) *)
    (* | Eaccess e (inl i) ty => *)
    (*     do te <- transl_lvalue e; *)
    (*     OK (Clight.Ederef *)
    (*           (Clight.Ebinop Oadd te *)
    (*                          (Clight.Econst_int (Int.repr i) (Tint I32 Unsigned noattr)) *)
    (*                          (Tpointer ty noattr)) ty) *)
    end.

  Fixpoint transl_exprlist (xs: list expr): res (list Clight.expr) :=
    match xs with
    | nil => OK nil
    | e :: es =>
        do te <- transl_expr e;
        do tes <- transl_exprlist es;
        OK (te :: tes)
    end.

  Definition transl_arglist := transl_exprlist.

  Fixpoint transl_statement (s: statement) : res Clight.statement :=
    match s with
    | Sskip => OK Clight.Sskip
    | Sassign b c =>
        do tb <- transl_expr b;
        do tc <- transl_expr c;
        OK (Clight.Sassign tb tc)
    | Sset x b =>
        do tb <- transl_expr b;
        OK (Clight.Sset x tb)
    | Scall x b cl =>
        do tb <- transl_expr b;
        do tcl <- transl_arglist cl;
        OK (Clight.Scall x tb tcl)
    | Sbuiltin x ef tyargs bl =>
        do tbl <- transl_arglist bl;
        OK (Clight.Sbuiltin x ef tyargs tbl)
    | Ssequence s1 s2 =>
        do ts1 <- transl_statement s1;
        do ts2 <- transl_statement s2;
        OK (Clight.Ssequence ts1 ts2)
    | Sifthenelse e s1 s2 =>
        do te <- transl_expr e;
        do ts1 <- transl_statement s1;
        do ts2 <- transl_statement s2;
        OK (Clight.Sifthenelse te ts1 ts2)
    | Sloop s1 s2 =>
        do ts1 <- transl_statement s1;
        do ts2 <- transl_statement s2;
        OK (Clight.Sloop ts1 ts2)
    | Sbreak => OK (Clight.Sbreak)
    | Scontinue => OK (Clight.Scontinue)
    | Sreturn (Some e) =>
        do te <- transl_expr e;
        OK (Clight.Sreturn (Some te))
    | Sreturn None => OK (Clight.Sreturn None)
    | Sswitch a sl =>
        do ta <- transl_expr a;
        do tsl <- transl_lbl_stmt sl;
        OK (Clight.Sswitch ta tsl)
    | Slabel lbl s =>
        do ts <- transl_statement s;
        OK (Clight.Slabel lbl ts)
    | Sgoto lbl => OK (Clight.Sgoto lbl)
    | Supdate b c =>
        do tb <- transl_lvalue b;
        do tc <- transl_expr c;
        OK (Clight.Sassign tb tc)
    end
  with transl_lbl_stmt (sl: labeled_statements) :=
         match sl with
         | LSnil => OK Clight.LSnil
         | LScons n s sl' =>
             do ts <- transl_statement s;
             do tsl' <- transl_lbl_stmt sl';
             OK (Clight.LScons n ts tsl')
         end.

  Definition transl_function (f: function) : res Clight.function :=
    do tbody <- transl_statement (fn_body f);
    OK ({|
           Clight.fn_return := fn_return f;
           Clight.fn_callconv := fn_callconv f;
           Clight.fn_params := fn_params f;
           Clight.fn_vars := fn_vars f;
           Clight.fn_temps := fn_temps f;
           Clight.fn_body := tbody
        |}).

  Definition transl_fundef (id: ident) (f: fundef) : res Clight.fundef :=
    match f with
    | Internal g =>
        do tg <- transl_function g;
        OK (Internal tg)
    | External ef args res cconv => OK (External ef args res cconv)
    end.

  Definition transl_globvar (id: ident) (ty: type) := OK ty.

  Definition val_init_data (v: val) : res (list init_data). Admitted.

  Definition transl_privvar {V} (v: privvar V) :=
    do x <- val_init_data (pvar_init _ v);
    OK {|
        gvar_info := pvar_info _ v;
        gvar_init := x;
        gvar_volatile := false;
        gvar_readonly := false;
      |}.

  Fixpoint transl_privvars {F V} (l: list (ident * privvar V)) :=
    match l with
    | nil => OK nil
    | (id, pv) :: l' =>
        do gv <- transl_privvar pv;
        do gv' <- transl_privvars l';
        OK ((id, Gvar (F:=F) gv) :: gv')
    end.

  Definition transl_program (p: program) : res Clight.program :=
    do tgl <- transf_globdefs transl_fundef transl_globvar p.(prog_defs);
    do tgv <- transl_privvars (prog_private p);
    OK ({|
           Ctypes.prog_defs := tgl ++ tgv;
           Ctypes.prog_public := prog_public p;
           Ctypes.prog_main := prog_main p;
           Ctypes.prog_types := prog_types p;
           Ctypes.prog_comp_env := prog_comp_env p;
           Ctypes.prog_comp_env_eq := prog_comp_env_eq p |}).

End TRANSF.

Require Import LogicalRelations.
Require Import OptionRel.
Require Import Lia.

Open Scope Z_scope.

Section MEM_SAME_EXCEPT.

  Variable (P: block -> Z -> Prop).
  Hypothesis P_dec: forall b ofs, {P b ofs} + {~ P b ofs}.

  Record mem_same_except  (m1: Mem.mem) (m2: Mem.mem) :=
    {
      same_support: Mem.support m1 = Mem.support m2;
      same_perm: forall b ofs k p, ~ P b ofs -> Mem.perm m1 b ofs k p <-> Mem.perm m2 b ofs k p;
      same_content: forall b ofs, ~ P b ofs -> ZMap.get ofs (NMap.get _ b (Mem.mem_contents m1))
                                         = ZMap.get ofs (NMap.get _ b (Mem.mem_contents m2));
      diff_perm: forall b ofs, P b ofs -> loc_out_of_bounds m1 b ofs;
    }.

  Instance valid_pointer_mse:
    Monotonic
      (@Mem.valid_pointer)
      (mem_same_except ++> - ==> - ==> leb).
  Proof.
    do 4 rstep. destruct Mem.valid_pointer eqn: X; try easy.
    cbn. rewrite !Mem.valid_pointer_nonempty_perm in *.
    edestruct P_dec.
    - eapply diff_perm in p; eauto. exfalso. apply p.
      eapply Mem.perm_max; eauto.
    - rewrite <- same_perm; eauto.
  Qed.

  Instance weak_valid_pointer_mse:
    Monotonic
      (@Mem.weak_valid_pointer)
      (mem_same_except ++> - ==> - ==> leb).
  Proof.
    unfold Mem.weak_valid_pointer. do 4 rstep.
    destruct orb eqn: X.
    - simpl. rewrite orb_true_iff in *.
      destruct X; [ left | right ]; apply valid_pointer_mse in H.
      specialize (H x0 x1). rewrite H0 in H. eauto.
      specialize (H x0 (x1 - 1)%Z). rewrite H0 in H. eauto.
    - easy.
  Qed.

  Instance bool_val_mse:
    Monotonic
      (@bool_val)
      (- ==> - ==> mem_same_except ++> option_le eq).
  Proof. unfold bool_val. rauto. Qed.

  Instance sem_unary_operation_mse:
    Monotonic
      (@sem_unary_operation)
      (- ==> - ==> - ==> mem_same_except ++> option_le eq).
  Proof.
    unfold sem_unary_operation.
    unfold sem_notbool, sem_notint, sem_neg, sem_absfloat.
    repeat rstep. f_equal. congruence.
  Qed.

  Instance sem_cast_mse:
    Monotonic
      (@Cop.sem_cast)
      (- ==> - ==> - ==> mem_same_except ++> option_le eq).
  Proof. unfold Cop.sem_cast. repeat rstep. Qed.

  Instance sem_binarith_mse:
    Monotonic
      (@Cop.sem_binarith)
      (- ==> - ==> - ==> - ==> - ==> - ==> - ==> - ==> mem_same_except ++> option_le eq).
  Proof. unfold Cop.sem_binarith. repeat rstep. Qed.

  Instance cmp_ptr_mse:
    Related
      (@Cop.cmp_ptr)
      (@Cop.cmp_ptr)
      (mem_same_except ++> - ==> - ==> - ==> option_le eq).
  Proof.
    rstep. rstep. rstep. rstep. rstep.
    unfold Cop.cmp_ptr. rstep. rstep. rewrite H0. reflexivity. rstep.
    - rstep. unfold Val.cmplu_bool. repeat rstep.
    - rstep. unfold Val.cmpu_bool. repeat rstep.
      Unshelve. all: eauto.
  Qed.

  Instance sem_cmp_mse:
    Monotonic
      (@Cop.sem_cmp)
      (- ==> - ==> - ==> - ==> - ==> mem_same_except ++> option_le eq).
  Proof. unfold Cop.sem_cmp. repeat rstep. Qed.

  Instance sem_binary_operation_mse:
    Monotonic
      (@sem_binary_operation)
      (- ==> - ==> - ==> - ==> - ==> - ==> mem_same_except ++> option_le eq).
  Proof.
    unfold sem_binary_operation.
    unfold
      Cop.sem_add,
      Cop.sem_add_ptr_int,
      Cop.sem_add_ptr_long,
      Cop.sem_sub,
      Cop.sem_mul,
      Cop.sem_div,
      Cop.sem_mod,
      Cop.sem_and,
      Cop.sem_or,
      Cop.sem_xor,
      Cop.sem_shl,
      Cop.sem_shr.
    repeat rstep.
  Qed.

(*     Lemma bool_val_inject: *)
(*   forall f m m' v ty b tv, *)
(*   bool_val v ty m = Some b -> *)
(*   Val.inject f v tv -> *)
(*   Mem.inject f m m' -> *)
(*   bool_val tv ty m' = Some b. *)
(* Proof. *)
(*   intros. eapply bool_val_inj; eauto. *)
(*   intros; eapply Mem.weak_valid_pointer_inject_val; eauto. *)
(* Qed. *)

  (* Lemma P_range_dec : forall (b : block) (lo hi : Z), *)
  (*     {forall ofs, (lo <= ofs < hi)%Z -> P b ofs} + {~ (forall ofs, (lo <= ofs < hi)%Z -> P b ofs)}. *)
  (* Admitted. *)

  Lemma perm_mse m1 m2 b ofs k p:
    mem_same_except m1 m2 ->
    Mem.perm m1 b ofs k p ->
    Mem.perm m2 b ofs k p.
  Proof.
    intros HM H.
    destruct (P_dec b ofs) as [X|X].
    - eapply diff_perm in X; eauto.
      exfalso. eauto with mem.
    - rewrite <- same_perm; eauto.
  Qed.

  Lemma range_perm_mse m1 m2 b lo hi k p:
    mem_same_except m1 m2 ->
    Mem.range_perm m1 b lo hi k p ->
    Mem.range_perm m2 b lo hi k p.
  Proof.
    intros HM H ofs X. specialize (H _ X).
    eauto using perm_mse.
  Qed.

  Instance load_mse:
    Monotonic
      (@Mem.load)
      (- ==> mem_same_except ++> - ==> - ==> option_le eq).
  Proof.
    repeat rstep. destruct Mem.load eqn: X; try constructor.
    rename x1 into b. rename x2 into ofs. rename x into ch.
    rename x0 into m1. rename y into m2.
    exploit Mem.load_valid_access. eauto. intros [A B].
    exploit Mem.valid_access_load. split. eapply range_perm_mse; eauto. apply B.
    intros [w Y]. rewrite Y. constructor.
    exploit Mem.load_result. apply X.
    exploit Mem.load_result. apply Y. intros -> ->.
    f_equal. apply Mem.getN_exten.
    intros i Hi. apply same_content; eauto.
    intros contra. eapply diff_perm in contra; eauto.
    apply contra. rewrite <- size_chunk_conv in Hi.
    specialize (A _ Hi). eauto with mem.
  Qed.

  Instance loadv_mse:
    Monotonic
      (@Mem.loadv)
      (- ==> mem_same_except ++> - ==> option_le eq).
  Proof. unfold Mem.loadv. repeat rstep. Qed.

  Instance load_bitfield_mse:
    Monotonic
      (@load_bitfield)
      (- ==> - ==> - ==> - ==> - ==> mem_same_except ++> - ==> - ==> impl).
  Proof.
    repeat rstep. intros Hv.
    destruct Hv as [sz sg1 attr sg pos width m v' ? Hpos Hwidth Hpw Hsg1 Hload].
    transport Hload. subst.
    constructor; eauto.
  Qed.

  Instance deref_loc_mse a:
    Monotonic
      (@deref_loc a)
      (mem_same_except ++> - ==> - ==> - ==> - ==> impl).
  Proof.
    repeat rstep. intros A. inv A; eauto using @deref_loc_reference, @deref_loc_copy.
    - transport H1. subst. eapply deref_loc_value; eauto.
    - eapply deref_loc_bitfield. eapply load_bitfield_mse; eauto.
  Qed.

  Lemma get_setN_inside:
    forall vl p q c,
      p <= q < p + Z.of_nat (length vl) ->
      (ZMap.get q (Mem.setN vl p c)) = nth (Z.to_nat (q - p)) vl Undef.
  Proof.
    induction vl; intros.
    simpl in H. extlia.
    simpl length in H. rewrite Nat2Z.inj_succ in H. simpl.
    destruct (zeq p q).
    - subst q. rewrite Mem.setN_outside by lia. rewrite ZMap.gss.
      replace (p - p) with 0 by lia. reflexivity.
    - rewrite IHvl by lia. destruct H as [A B].
      replace (q - p) with (Z.succ (q - p - 1)) by lia.
      rewrite Z2Nat.inj_succ. 2: lia.
      f_equal. f_equal. lia.
  Qed.

  Instance store_mse:
    Monotonic
      (@Mem.store)
      (- ==> mem_same_except ++> - ==> - ==> - ==> option_le mem_same_except).
  Proof.
    repeat rstep. destruct Mem.store eqn: X; try constructor.
    rename x into ch. rename x1 into b. rename x2 into ofs. rename x3 into v.
    rename x0 into m1. rename y into m2.
    exploit Mem.store_valid_access_3; eauto. intros [A B].
    edestruct Mem.valid_access_store as [n Y]. split. 2: eauto.
    eapply range_perm_mse; eauto.
    rewrite Y. constructor.
    constructor.
    - exploit Mem.support_store. apply X. intros ->.
      exploit Mem.support_store. apply Y. intros ->.
      apply H.
    - intros bx ofsx k p HP. split; intros.
      + eapply Mem.perm_store_1; eauto.
        rewrite <- same_perm. 2-3: eauto.
        eapply Mem.perm_store_2; eauto.
      + eapply Mem.perm_store_1; eauto.
        rewrite same_perm. 2-3: eauto.
        eapply Mem.perm_store_2; eauto.
    - intros bx ofsx HP.
      exploit Mem.store_mem_contents. apply X. intros ->.
      exploit Mem.store_mem_contents. apply Y. intros ->.
      exploit same_content; eauto. intros C.
      rewrite !NMap.gsspec.
      destruct (NMap.elt_eq bx b).
      + subst. destruct (zlt ofsx ofs).
        * now rewrite !Mem.setN_outside by lia.
        * destruct (zle (ofs + Z.of_nat (length (encode_val ch v))) ofsx).
          now rewrite !Mem.setN_outside by lia.
          now rewrite !get_setN_inside by lia.
      + apply C.
    - intros bx ofsx HP C.
      eapply diff_perm; eauto. eauto with mem.
  Qed.

  Transparent Mem.loadbytes Mem.storebytes.
  Instance storev_mse:
    Monotonic
      (@Mem.storev)
      (- ==> mem_same_except ++> - ==> - ==> option_le mem_same_except).
  Proof. unfold Mem.storev. repeat rstep. Qed.

  Instance loadbytes_mse:
    Monotonic
      (@Mem.loadbytes)
      (mem_same_except ++> - ==> - ==> - ==> option_le eq).
  Proof.
    repeat rstep. destruct Mem.loadbytes eqn: X; try constructor.
    unfold Mem.loadbytes in *.
    rename x0 into b. rename x1 into ofs. rename x2 into sz.
    rename x into m1. rename y into m2.
    destruct (Mem.range_perm_dec m1 b ofs (ofs + sz) Cur Readable); inv X.
    destruct Mem.range_perm_dec.
    - constructor. apply Mem.getN_exten. intros i Hi.
      apply same_content; eauto. intros HP.
      eapply diff_perm; eauto.
      destruct (zle 0 sz); eauto.
      + rewrite Z2Nat.id in Hi by lia. eauto with mem.
      + rewrite Z_to_nat_neg in Hi by lia. lia.
    - exfalso. apply n.
      eapply range_perm_mse; eauto.
  Qed.

  Instance storebytes_mse:
    Monotonic
      (@Mem.storebytes)
      (mem_same_except ++> - ==> - ==> - ==> option_le mem_same_except).
  Proof.
    repeat rstep. destruct Mem.storebytes eqn: X; try constructor.
    unfold Mem.storebytes in *.
    rename x0 into b. rename x1 into ofs. rename x2 into vl.
    rename x into m1. rename y into m2.
    destruct (Mem.range_perm_dec m1 b ofs (ofs + Z.of_nat (Datatypes.length vl)) Cur Writable); inv X.
    destruct Mem.range_perm_dec.
    - constructor. constructor; cbn -[NMap.get].
      + apply same_support; eauto.
      + intros bx ofsx k p HP.
        unfold Mem.perm. cbn.
        apply same_perm; eauto.
      + intros bx ofsx HP.
        exploit same_content; eauto. intros A.
        rewrite !NMap.gsspec.
        destruct (NMap.elt_eq bx b).
        * subst. destruct (zlt ofsx ofs).
          -- now rewrite !Mem.setN_outside by lia.
          -- destruct (zle (ofs + Z.of_nat (length vl)) ofsx).
             now rewrite !Mem.setN_outside by lia.
             now rewrite !get_setN_inside by lia.
        * apply A.
      + intros bx ofsx HP C.
        eapply diff_perm; eauto.
    - exfalso. apply n.
      eauto using range_perm_mse.
  Qed.
  Opaque Mem.loadbytes Mem.storebytes.

  Instance store_bitfield_mse:
    Monotonic
      (@store_bitfield)
      (- ==> - ==> - ==> - ==> - ==> mem_same_except ++> - ==> - ==> % set_le (mem_same_except * eq)).
  Proof.
    repeat rstep.
    intros [v m] Hv.
    destruct Hv as [sz sg1 attr sg pos width m addr v n m' Hpos Hw Hpw Hsg1 Hload Hstore].
    transport Hload. subst.
    transport Hstore.
    eexists (_, _). cbn. split; [ | rauto].
    econstructor; eauto.
  Qed.

  Instance assign_loc_mse:
    Monotonic
      (@assign_loc)
      (- ==> - ==> mem_same_except ++> - ==> - ==> - ==> - ==> set_le mem_same_except).
  Proof.
    repeat rstep. intros m A. inv A.
    - transport H1. eexists; split; eauto.
      eapply assign_loc_value; eauto.
    - transport H4. subst.
      transport H5.
      eexists; split; eauto.
      eapply assign_loc_copy; eauto.
    - exploit store_bitfield_mse; eauto.
      unfold uncurry. instantiate (8 := (_, _)). cbn. apply H0.
      intros ([a b] & A & B). cbn in *. split_hyps. subst.
      eexists. split; eauto.
      eapply assign_loc_bitfield; eauto.
  Qed.

  Lemma mse_preserve mx m m' ch b ofs v:
    mem_same_except mx m ->
    Mem.store ch m b ofs v = Some m' ->
    (forall i, ofs <= i < ofs + size_chunk ch -> P b i) ->
    mem_same_except mx m'.
  Proof.
    intros H HST HX.
    constructor.
    - eapply Mem.support_store in HST.
      rewrite HST. apply H.
    - intros bx ofsx k p HP. split; intros.
      + eapply Mem.perm_store_1; eauto.
        rewrite <- same_perm; eauto.
      + rewrite same_perm. 2-3: eauto.
        eapply Mem.perm_store_2; eauto.
    - intros bx ofsx HP.
      erewrite same_content. 2-3: eauto.
      exploit Mem.store_mem_contents; eauto. intros ->.
      rewrite NMap.gsspec.
      destruct (NMap.elt_eq bx b).
      + subst. destruct (zlt ofsx ofs).
        * now rewrite !Mem.setN_outside by lia.
        * destruct (zle (ofs + Z.of_nat (length (encode_val ch v))) ofsx).
          -- now rewrite !Mem.setN_outside by lia.
          -- exfalso.
             apply HP. apply HX.
             rewrite encode_val_length in *.
             unfold size_chunk_nat in *.
             rewrite Z2Nat.id in *. lia.
             destruct ch; cbn; lia.
      + reflexivity.
    - intros bx ofsx HP C.
      eapply diff_perm; eauto.
  Qed.

End MEM_SAME_EXCEPT.

(* Lemma transport_in_goal_manual `{Transport}: *)
(*   forall (Q: Prop), (R a b) -> (PB -> Q) -> (PA -> Q). *)
(* Proof. firstorder. Qed. *)

(* Ltac transp H := *)
(*   revert H; *)
(*   lazymatch goal with *)
(*   | |- ?PA -> ?Q => *)
(*       eapply (transport_in_goal_manual (PA:=PA) Q) *)
(*   end; *)
(*   try solve [ rauto | rstep; eauto ]; intro H. *)

Require Import AbRel.

Fixpoint psizeof_ty (t: type) : Z :=
  match t with
  | Tvoid => 1
  | Tint I8 _ _ => 1
  | Tint I16 _ _ => 2
  | Tint I32 _ _ => 4
  | Tint IBool _ _ => 1
  | Tlong _ _ => 8
  | Tfloat F32 _ => 4
  | Tfloat F64 _ => 8
  | Tpointer _ _ => if Archi.ptr64 then 8 else 4
  | _ => 0
  end.

Fixpoint psizeof (x: ClightP.val) : Z :=
  match x with
  | ClightP.Val _ ty => psizeof_ty ty
  end.

Definition penv_footprint (pe: ClightP.penv): list (ident * Z) :=
  map (fun '(id, v) => (id, psizeof v)) (PTree.elements pe).

(* Fixpoint pfield_offset_rec (s: PMap.t ClightP.val) (id: ident) (ms: list ident) (pos: Z) *)
(*   {struct ms} : option Z := *)
(*   match ms with *)
(*   | nil => None *)
(*   | m :: ms => *)
(*       if ident_eq id m then Some pos *)
(*       else *)
(*         let x := PMap.get id s in *)
(*         pfield_offset_rec s id ms (pos + psizeof x) *)
(*   end. *)

(* Definition pfield_offset (s: PMap.t ClightP.val) (id: ident) (ms: list ident) := *)
(*   pfield_offset_rec s id ms 0. *)

Inductive pvalue_match: block -> Z -> ClightP.val -> Mem.mem -> Prop :=
| pval_match b ofs ty chunk v m:
  access_mode ty = By_value chunk ->
  Mem.load chunk m  b ofs = Some v ->
  Mem.valid_access m chunk b ofs Writable ->
  pvalue_match b ofs (ClightP.Val v ty) m.
(* | parr_match b ofs n a m: *)
(*   (forall i, i < n -> *)
(*         let z := Z.of_nat i in *)
(*         pvalue_match b (Ptrofs.add ofs (Ptrofs.repr z)) (ZMap.get z a) m) -> *)
(*   pvalue_match b ofs (ClightP.Array n a) m *)
(* | pstr_match b ofs l s m: *)
(*   (forall p x, In p l -> pfield_offset s p l = Some x -> *)
(*           pvalue_match b (Ptrofs.add ofs (Ptrofs.repr x)) (PMap.get p s) m) -> *)
(*   pvalue_match b ofs (ClightP.Struct l s) m. *)

Inductive penv_match: Genv.symtbl -> (ClightP.penv * Mem.mem) -> Mem.mem -> Prop :=
| penv_match_intro se pe m tm
    (MSAME: mem_same_except (locsp se (penv_footprint pe)) m tm)
    (MDIFF: forall id v, PTree.get id pe = Some v ->
                    exists b, Genv.find_symbol se id = Some b /\
                           pvalue_match b 0 v tm)
  : penv_match se (pe, m) tm.

Inductive pmatch_query: Genv.symtbl -> query (li_c @ ClightP.penv) -> query li_c -> Prop :=
| pmatch_query_intro se vf sg vargs m tm pe
    (PM: penv_match se (pe, m) tm):
  pmatch_query se (cq vf sg vargs m, pe) (cq vf sg vargs tm).

Inductive pmatch_reply: Genv.symtbl -> reply (li_c @ ClightP.penv) -> reply li_c -> Prop :=
| pmatch_reply_intro se rv m tm pe
    (PM: penv_match se (pe, m) tm):
  pmatch_reply se (cr rv m, pe) (cr rv tm).

Program Definition cc_penv: callconv (li_c @ ClightP.penv) li_c :=
  {|
    (* the world is defined as the target program symbol table, which is
       supposed to contain the variables in penv *)
    ccworld := Genv.symtbl;
    match_senv se se1 se2 := se = se1 /\ se = se2;
    match_query := pmatch_query;
    match_reply := pmatch_reply;
  |}.
Next Obligation. reflexivity. Qed.
Next Obligation. inv H0. reflexivity. Qed.
Next Obligation. inv H. reflexivity. Qed.

Definition value_of (pv: ClightP.val) :=
  match pv with
  | ClightP.Val v _ => v
  end.
Definition type_of (pv: ClightP.val) :=
  match pv with
  | ClightP.Val _ ty => ty
  end.

Lemma size_type_chunk ty ch:
  access_mode ty = By_value ch ->
  size_chunk ch = psizeof_ty ty.
Proof.
  intros. destruct ty; inv H; cbn in *; try easy.
  - destruct i; destruct s; inv H1; easy.
  - destruct f; inv H1; easy.
Qed.

Lemma unchanged_on_pvalue_match P b ofs v m m':
  pvalue_match b ofs v m -> Mem.unchanged_on P m m' ->
  (forall i, ofs <= i < ofs + psizeof_ty (type_of v) -> P b i) ->
  pvalue_match b ofs v m'.
Proof.
  intros A B C. inv A. econstructor; eauto.
  unfold Mem.loadv in *.
  eapply Mem.load_unchanged_on; eauto.
  intros i Hi.
  apply C. cbn. erewrite <- size_type_chunk; eauto.
  destruct H1 as [D E]. split; eauto.
  intros x Hx. specialize (D _ Hx).
  eapply Mem.perm_unchanged_on; eauto.
  apply C. cbn. erewrite <- size_type_chunk; eauto.
Qed.

Lemma eval_expr_type_same ge e le pe t x v:
  ClightP.eval_expr ge e le pe t x v ->
  type_of v = ClightP.typeof x.
Admitted.

Section PRESERVATION.

  Definition ptree_disjoint {A B} (m: PTree.t A) (n: PTree.t B) :=
    forall i v w, m ! i = Some v -> n ! i = Some w -> False.

  Variable prog: ClightP.program.
  Variable tprog: Clight.program.
  Hypothesis TRANSL: transl_program prog = OK tprog.
  (* match_senv is defined as equal. For now, we require the source and target
     symbol tables to be the same and both carry the module static variables *)
  Variable se: Genv.symtbl.
  Let ge : ClightP.genv := ClightP.globalenv se prog.
  Let tge : Clight.genv := Clight.globalenv se tprog.

  Inductive pmatch_cont: (ClightP.cont * ClightP.penv) -> Clight.cont -> Prop :=
  | pmatch_Kstop: forall pe, pmatch_cont (ClightP.Kstop, pe) Clight.Kstop
  | pmatch_Kseq: forall s t k tk pe,
      transl_statement s = OK t ->
      pmatch_cont (k, pe) tk ->
      pmatch_cont (ClightP.Kseq s k, pe) (Clight.Kseq t tk)
  | pmatch_Kloop1: forall s1 s2 ts1 ts2 k tk pe,
      transl_statement s1 = OK ts1 ->
      transl_statement s2 = OK ts2 ->
      pmatch_cont (k, pe) tk ->
      pmatch_cont (ClightP.Kloop1 s1 s2 k, pe) (Clight.Kloop1 ts1 ts2 tk)
  | pmatch_Kloop2: forall s1 s2 ts1 ts2 k tk pe,
      transl_statement s1 = OK ts1 ->
      transl_statement s2 = OK ts2 ->
      pmatch_cont (k, pe) tk ->
      pmatch_cont (ClightP.Kloop2 s1 s2 k, pe) (Clight.Kloop2 ts1 ts2 tk)
  | pmatch_Kswitch: forall k tk pe,
      pmatch_cont (k, pe) tk -> pmatch_cont (ClightP.Kswitch k, pe) (Clight.Kswitch tk)
  | pmatch_Kcall: forall fid f tf e le k tk pe,
      transl_function f = OK tf ->
      pmatch_cont (k, pe) tk ->
      ptree_disjoint e pe ->
      pmatch_cont (ClightP.Kcall fid f e le k, pe) (Clight.Kcall fid tf e le tk).

  Inductive pmatch_state: Genv.symtbl -> ClightP.state * ClightP.penv -> Clight.state -> Prop :=
  | pmatch_State: forall se fs ss ks e le ms pe ft st kt mt
      (TRF: transl_function fs = OK ft)
      (TRS: transl_statement ss = OK st)
      (MK: pmatch_cont (ks, pe) kt)
      (MP: penv_match se (pe, ms) mt)
      (DISJ: ptree_disjoint e pe),
      pmatch_state se (ClightP.State fs ss ks e le ms, pe) (Clight.State ft st kt e le mt)
  | pmatch_Callstate: forall se vf args ks kt ms mt pe
      (MK: pmatch_cont (ks, pe) kt)
      (MP: penv_match se (pe, ms) mt),
      pmatch_state se (ClightP.Callstate vf args ks ms, pe) (Clight.Callstate vf args kt mt)
  | pmatch_Returnstate: forall se rv ks kt ms mt pe
      (MK: pmatch_cont (ks, pe) kt)
      (MP: penv_match se (pe, ms) mt),
      pmatch_state se (ClightP.Returnstate rv ks ms, pe) (Clight.Returnstate rv kt mt).

  Definition transl_expr_typeof e te:
    transl_expr e = OK te -> ClightP.typeof e = typeof te.
  Proof.
    intros TE; destruct e; monadInv TE; cbn in *; eauto.
  Qed.

  Lemma penv_footprint_dec:
    forall pe b ofs, {locsp se (penv_footprint pe) b ofs} + {~ locsp se (penv_footprint pe) b ofs}.
  Proof.
    intros.
  Admitted.

  Lemma eval_expr_lvalue_correct :
    forall e le m tm pe,
      ptree_disjoint e pe ->
      penv_match se (pe, m) tm ->
      (forall expr v,
          ClightP.eval_expr ge e le pe m expr v ->
          forall texpr (TR: transl_expr expr = OK texpr),
            Clight.eval_expr tge e le tm texpr (value_of v))
      /\
      (forall expr b ofs bf,
         ClightP.eval_lvalue ge e le pe m expr b ofs bf ->
         forall texpr (TR: transl_expr expr = OK texpr),
           Clight.eval_lvalue tge e le tm texpr b ofs bf).
  Proof.
    intros e le t tm pe HE HP.
    apply ClightP.eval_expr_lvalue_ind.
    - intros. monadInv TR. constructor.
    - intros. monadInv TR. constructor.
    - intros. monadInv TR. constructor.
    - intros. monadInv TR. constructor.
    - intros. monadInv TR. constructor. eauto.
    - intros. monadInv TR.
      constructor. apply H0. apply EQ.
    - intros. monadInv TR. econstructor; eauto.
      erewrite <- transl_expr_typeof; eauto. inv HP.
      pose proof (sem_unary_operation_mse _ (penv_footprint_dec pe)).
      transport H1. subst. eauto.
    - intros. monadInv TR. econstructor; eauto.
      erewrite <- !transl_expr_typeof; eauto. inv HP.
      pose proof (sem_binary_operation_mse _ (penv_footprint_dec pe)).
      transport H3. subst.
      monadInv TRANSL. eauto.
    - intros. monadInv TR. econstructor; eauto.
      erewrite <- transl_expr_typeof; eauto. inv HP.
      pose proof (sem_cast_mse _ (penv_footprint_dec pe)).
      transport H1. subst. eauto.
    - intros. monadInv TR.
      replace (ClightP.genv_cenv ge) with (genv_cenv tge).
      constructor. cbn. monadInv TRANSL. reflexivity.
    - intros. monadInv TR.
      replace (ClightP.genv_cenv ge) with (genv_cenv tge).
      constructor. cbn. monadInv TRANSL. reflexivity.
    - intros. specialize (H0 _ TR).
      econstructor; eauto. cbn.
      erewrite <- transl_expr_typeof; eauto.
      inv HP. eapply deref_loc_mse; eauto. apply penv_footprint_dec.
    - intros. monadInv TR. inv HP.
      specialize (MDIFF _ _ H) as (b & A & B).
      econstructor. eapply eval_Evar_global.
      + edestruct (e ! id) eqn: X; eauto.
        exfalso. eapply HE; eauto.
      + eauto.
      + inv B. eapply deref_loc_value; eauto.
    - intros. monadInv TR. now constructor.
    - intros. monadInv TR. apply eval_Evar_global; eauto.
    - intros. monadInv TR. constructor. eauto.
    - intros. monadInv TR. monadInv TRANSL. econstructor; eauto.
      erewrite <- transl_expr_typeof; eauto.
    - intros. monadInv TR. monadInv TRANSL.
      eapply eval_Efield_union; eauto.
      erewrite <- transl_expr_typeof; eauto.
  Qed.

  Lemma eval_expr_correct:
    forall e le m tm pe,
      ptree_disjoint e pe ->
      penv_match se (pe, m) tm ->
      forall expr v,
          ClightP.eval_expr ge e le pe m expr v ->
          forall texpr (TR: transl_expr expr = OK texpr),
            Clight.eval_expr tge e le tm texpr (value_of v).
  Proof. apply eval_expr_lvalue_correct. Qed.

  Lemma eval_lvalue_correct:
    forall e le m tm pe,
      ptree_disjoint e pe ->
      penv_match se (pe, m) tm ->
      forall expr b ofs bf,
        ClightP.eval_lvalue ge e le pe m expr b ofs bf ->
        forall texpr (TR: transl_expr expr = OK texpr),
          Clight.eval_lvalue tge e le tm texpr b ofs bf.
  Proof. apply eval_expr_lvalue_correct. Qed.

  Lemma eval_exprlist_correct:
    forall e le m tm pe,
      ptree_disjoint e pe ->
      penv_match se (pe, m) tm ->
      forall es tys vs,
          ClightP.eval_exprlist ge e le pe m es tys vs ->
          forall tes (TR: transl_exprlist es = OK tes),
            Clight.eval_exprlist tge e le tm tes tys vs.
  Proof.
    intros until es. induction es.
    - intros. monadInv TR. inv H1. constructor.
    - intros * HEV * HTR.
      monadInv HTR. inv HEV.
      eapply eval_expr_correct in H3; eauto.
      pose proof (sem_cast_mse _ (penv_footprint_dec pe)).
      inv H0. transport H4. subst.
      econstructor; eauto.
      cbn. erewrite <- transl_expr_typeof; eauto.
  Qed.

  Hint Extern 1 (Transport _ _ _ _ _) =>
         set_le_transport @assign_loc : typeclass_instances.

  Lemma penv_footprint_in pe id pv b i:
    pe ! id = Some pv ->
    Genv.find_symbol se id = Some b ->
    0 <= i < psizeof_ty (type_of pv) ->
    locsp se (penv_footprint pe) b i.
  Proof.
    intros A B C. unfold locsp, penv_footprint.
    apply Exists_exists. exists (id, psizeof pv). split.
    - apply PTree.elements_correct in A.
      apply in_map_iff. exists (id, pv). split; eauto.
    - unfold locp. split; eauto.
      destruct pv. unfold psizeof. apply C.
  Qed.

  (* Lemma pmatch_valid_access m b ofs v ch ty: *)
  (*   pvalue_match b ofs v m -> *)
  (*   Mem.valid_access ?m1 ?chunk ?b ?ofs Writable *)

  Lemma footprint_same pe id ty old_v new_v:
    pe ! id = Some (ClightP.Val old_v ty) ->
    locsp se (penv_footprint (PTree.set id (ClightP.Val new_v ty) pe)) =
      locsp se (penv_footprint pe).
  Proof.
    intros A.
    apply Axioms.functional_extensionality. intros b.
    apply Axioms.functional_extensionality. intros ofs.
    apply PropExtensionality.propositional_extensionality; split; intros B.
    - unfold locsp in *.
      rewrite Exists_exists in *. destruct B as ([x y] & X & Y).
      exists (x, y). split; eauto.
      unfold penv_footprint in *.
      rewrite in_map_iff in *.
      destruct X as ([u v] & U & V). inv U.
      eexists (x, (if peq x id then ClightP.Val old_v ty else v)).
      apply PTree.elements_complete in V.
      rewrite PTree.gsspec in V.
      destruct peq; subst; split; inv V; eauto using PTree.elements_correct.
    - unfold locsp in *.
      rewrite Exists_exists in *. destruct B as ([x y] & X & Y).
      exists (x, y). split; eauto.
      unfold penv_footprint in *.
      rewrite in_map_iff in *.
      destruct X as ([u v] & U & V). inv U.
      eexists (x, (if peq x id then ClightP.Val new_v ty else v)).
      split.
      + destruct peq. subst. apply PTree.elements_complete in V.
        rewrite A in V. inv V. reflexivity. reflexivity.
      + apply PTree.elements_correct.
        rewrite PTree.gsspec.
        destruct peq. subst. reflexivity.
        apply PTree.elements_complete in V. assumption.
  Qed.

  Lemma functions_translated v fd:
    Genv.find_funct (ClightP.genv_genv ge) v = Some fd ->
    exists i tfd, Genv.find_funct tge v = Some tfd /\ transl_fundef i fd = OK tfd.
  Admitted.

  Lemma type_of_fundef_preserved id fd tfd:
    transl_fundef id fd = OK tfd -> ClightP.type_of_fundef fd = type_of_fundef tfd.
  Proof.
    intros H. destruct fd.
    - monadInv H. cbn. destruct f. monadInv EQ. cbn. reflexivity.
    - monadInv H. reflexivity.
  Qed.

  Lemma external_call_match ef vargs pe m tm t vres m':
    penv_match se (pe, m) tm ->
    external_call ef (ClightP.genv_genv ge) vargs m t vres m' ->
    exists tm', external_call ef tge vargs tm t vres tm' /\ penv_match se (pe, m') tm'.
  Proof.
  Admitted.

  Lemma free_list_match pe m bs m' tm:
    penv_match se (pe, m) tm -> Mem.free_list m bs = Some m' ->
    exists tm', Mem.free_list tm bs = Some tm' /\ penv_match se (pe, m') tm'.
  Proof.
  Admitted.

  Lemma pmatch_call_cont pe k kt:
    pmatch_cont (k, pe) kt ->
    pmatch_cont (ClightP.call_cont k, pe) (call_cont kt).
  Proof.
    intros H.
    set (P := fun '(k, pe) kt => pmatch_cont (ClightP.call_cont k, pe) (call_cont kt)).
    eapply pmatch_cont_ind with (P := P) in H; subst P; cbn; eauto.
    constructor.
    intros. constructor; eauto.
  Qed.

  Lemma pmatch_is_call_cont pe k kt:
    pmatch_cont (k, pe) kt ->
    ClightP.is_call_cont k ->
    Clight.is_call_cont kt.
  Proof. intros. inv H; auto. Qed.

  Lemma blocks_of_env_same e:
    ClightP.blocks_of_env ge e = blocks_of_env tge e.
  Proof.
    unfold ClightP.blocks_of_env, blocks_of_env.
    f_equal.
    unfold ClightP.block_of_binding, block_of_binding.
    subst ge tge. monadInv TRANSL. cbn. reflexivity.
  Qed.

  Lemma transl_select_switch n sl tsl:
    transl_lbl_stmt sl = OK tsl ->
    transl_lbl_stmt (ClightP.select_switch n sl) = OK (select_switch n tsl).
  Proof.
  Admitted.

  Lemma transl_seq_of_labeled_statement sl tsl:
    transl_lbl_stmt sl = OK tsl ->
    transl_statement (ClightP.seq_of_labeled_statement sl) = OK (seq_of_labeled_statement tsl).
  Proof.
  Admitted.

  Lemma pmatch_function_entry1 pe m tm f tf vargs m' e le:
    penv_match se (pe, m) tm ->
    transl_function f = OK tf ->
    ClightP.function_entry1 ge f vargs m e le m' ->
    exists tm', function_entry1 tge tf vargs tm e le tm' /\
             penv_match se (pe, m') tm' /\
             ptree_disjoint e pe.
  Proof.
  Admitted.

  Lemma pmatch_find_label pe s ts k tk s' k' lbl:
    transl_statement s = OK ts ->
    pmatch_cont (k, pe) tk ->
    ClightP.find_label lbl s (ClightP.call_cont k) = Some (s', k') ->
    exists ts' tk',
      find_label lbl ts (call_cont tk) = Some (ts', tk') /\
        transl_statement s' = OK ts' /\
        pmatch_cont (k', pe) tk'.
  Proof.
  Admitted.

  Lemma load_result_same ty ch v:
    access_mode ty = By_value ch ->
    Val.load_result (chunk_of_type (typ_of_type ty)) v =
      Val.load_result ch v.
  Admitted.

  Lemma pmatch_cont_set_pe k tk pe id v v':
    pe ! id = Some v ->
    pmatch_cont (k, pe) tk ->
    pmatch_cont (k, (PTree.set id v' pe)) tk.
  Admitted.

  Lemma step_correct:
    forall s1 pe t s1' pe',
      ClightP.step1 ge (s1, pe) t (s1', pe') ->
      forall s2 : state,
        pmatch_state se (s1, pe) s2 ->
        exists s2' : state, Clight.step1 tge s2 t s2' /\ pmatch_state se (s1', pe') s2'.
  Proof.
    induction 1; intros S2 MS; inv MS.
    (* assign *)
    - monadInv TRS. pose proof H2 as HA.
      eapply eval_lvalue_correct in H; eauto.
      eapply eval_expr_correct in H0; eauto.
      inv MP. clear pe. rename pe0 into pe.
      pose proof (sem_cast_mse _ (penv_footprint_dec pe)).
      transport H1. subst.
      pose proof (assign_loc_mse _ (penv_footprint_dec pe)).
      transport H2.
      eexists. split.
      + econstructor; eauto.
        erewrite <- !transl_expr_typeof; eauto.
        erewrite <- !transl_expr_typeof; eauto.
        monadInv TRANSL. eauto.
      + constructor; eauto.
        constructor; eauto.
        intros id pv Hpv. specialize (MDIFF _ _ Hpv) as (b & HB1 & HB2).
        exists b. split; eauto.
        eapply unchanged_on_pvalue_match; eauto.
        instantiate (1 := locsp se (penv_footprint pe)).
        * inv H5.
          -- eapply Mem.store_unchanged_on; eauto.
             intros i Hi contra.
             eapply diff_perm; eauto.
             inv HA.
             ++ exploit Mem.store_valid_access_3; eauto. intros [A B].
                assert (Mem.perm m loc i Cur Writable); eauto with mem.
                apply A. replace chunk0 with chunk by congruence. eauto.
             (* this case is legit when array is considered *)
             ++ congruence.
          -- eapply Mem.storebytes_unchanged_on; eauto.
             intros i Hi contra.
             eapply diff_perm; eauto.
             inv HA.
             ++ congruence.
             ++ assert (Mem.perm m loc i Cur Writable); eauto with mem.
                eapply Mem.storebytes_range_perm in H18. apply H18.
                pose proof (loadbytes_mse _ (penv_footprint_dec pe)).
                transport H17. subst. replace x1 with bytes by congruence.
                eauto.
          -- inv H2. eapply Mem.store_unchanged_on; eauto.
             intros i Hi contra.
             eapply diff_perm. apply MSAME. apply contra.
             assert (Mem.perm m loc i Cur Writable).
             2: { clear - H2. eauto with mem. }
             inv HA. inv H17.
             exploit Mem.store_valid_access_3. apply H25. intros [A B].
             apply A. eauto.
        * intros i Hi. eapply penv_footprint_in; eauto.
    (* set *)
    - monadInv TRS.
      eapply eval_expr_correct in H; eauto.
      eexists. split; constructor; eauto.
    (* update *)
    - monadInv TRS.
      exploit eval_expr_type_same. apply H1. intros Hty.
      eapply eval_expr_correct in H1; eauto.
      inv MP. clear pe. rename pe0 into pe.
      exploit MDIFF. apply H. intros (b & HB1 & HB2).
      inv HB2. eapply Mem.valid_access_store in H10 as (m' & Hm').
      eexists. split.
      + econstructor.           (* assign *)
        * eapply eval_Evar_global.
          edestruct (e ! id) eqn: X.
          exfalso. eapply DISJ; eauto. reflexivity.
          apply HB1.
        * eauto.
        * cbn in *.
          exploit transl_expr_typeof. apply EQ.
          intros Hty2.
          replace (typeof x) with ty by congruence.
          apply cast_val_casted; eauto.
        * eapply assign_loc_value; eauto.
      + constructor; eauto.     (* match *)
        * eapply pmatch_cont_set_pe; eauto.
        * constructor.
          -- erewrite footprint_same; eauto.
             eapply mse_preserve; eauto.
             intros i Hi. eapply penv_footprint_in; eauto.
             cbn. erewrite <- size_type_chunk; eauto.
          -- intros idx vx Hx.
             destruct (peq id idx).
             ++ subst. rewrite PTree.gss in Hx. inv Hx.
                exists b. split; eauto. econstructor; eauto.
                (* load same value *)
                eapply Mem.load_store_same in Hm'.
                exploit val_casted_has_type; eauto.
                intros contra. subst. inv H0.
                intros HTY.
                rewrite Hm'. f_equal.
                apply Val.load_result_same in HTY.
                erewrite <- load_result_same; eauto.
                (* valid_access *)
                eapply Mem.store_valid_access_1; eauto.
                eapply Mem.store_valid_access_3; eauto.
             ++ rewrite PTree.gso in Hx; eauto.
                exploit MDIFF. apply Hx.
                intros (bx & BX1 & BX2). exists bx. split; auto.
                assert (b <> bx).
                {
                  intros contra. subst.
                  apply n. eapply Genv.find_symbol_injective; eauto.
                }
                eapply unchanged_on_pvalue_match; eauto.
                eapply Mem.store_unchanged_on. apply Hm'.
                instantiate (1 := fun bi _ => bi = bx).
                intuition. intuition.
        * intros idx [bx ofsx] vx HE HPE.
          destruct (peq idx id). subst.
          -- rewrite PTree.gss in HPE. inv HPE.
             eapply DISJ; eauto.
          -- rewrite PTree.gso in HPE; eauto.

    (* call *)
    - monadInv TRS. clear pe. rename pe0 into pe.
      eapply eval_expr_correct in H0; eauto.
      eapply eval_exprlist_correct in H1; eauto.
      exploit functions_translated. eauto. intros (i & tfd & HFD1 & HFD2).
      eexists. split.
      + econstructor; eauto.
        erewrite <- transl_expr_typeof; eauto.
        cbn. unfold ClightP.genv_genv in *. cbn in H2.
        exploit type_of_fundef_preserved. eauto. intros <-. eauto.
      + constructor; eauto.
        constructor; eauto.

    (* builtin *)
    - monadInv TRS.
      eapply eval_exprlist_correct in H; eauto.
      exploit external_call_match; eauto. intros (mt' & HEC & HM).
      eexists. split.
      + econstructor; eauto.
      + constructor; eauto.

    (* sequence *)
    - monadInv TRS.
      eexists. split; repeat (constructor; eauto).

    (* skip sequence *)
    - monadInv TRS. inv MK.
      eexists. split. constructor. constructor; eauto.

    (* continue sequence *)
    - monadInv TRS. inv MK.
      eexists. split. constructor. constructor; eauto.

    (* break sequence *)
    - monadInv TRS. inv MK.
      eexists. split. constructor. constructor; eauto.

    (* ifthenelse *)
    - monadInv TRS. clear pe. rename pe0 into pe.
      inv MP.
      pose proof (bool_val_mse _ (penv_footprint_dec pe)).
      transport H0. subst.
      eapply eval_expr_correct in H; eauto.
      eexists. split. econstructor; eauto.
      cbn. erewrite <- transl_expr_typeof; eauto.
      constructor; eauto. destruct x2; eauto.
      all: constructor; eauto.

    (* loop *)
    - monadInv TRS. eexists. split.
      constructor. repeat (constructor; eauto).

    (* skip-or-continue loop *)
    - inv MK. destruct H; subst; monadInv TRS;
        eexists; split; repeat (constructor; eauto).

    (* break loop1 *)
    - monadInv TRS. inv MK. eexists; split.
      eapply step_break_loop1.
      constructor; eauto.

    (* skip loop2 *)
    - monadInv TRS. inv MK. eexists; split.
      constructor. constructor; eauto.
      cbn. rewrite H4. cbn. rewrite H5. reflexivity.

    (* break loop2 *)
    - monadInv TRS. inv MK. eexists; split.
      constructor. constructor; eauto.

    (* return None *)
    - monadInv TRS.
      exploit free_list_match; eauto. intros (tm' & HFL & HM).
      eexists; split.
      constructor. rewrite <- blocks_of_env_same; eauto.
      constructor; eauto.
      apply pmatch_call_cont. auto.

    (* return Some *)
    - monadInv TRS.
      exploit eval_expr_correct; eauto. intros HEV.
      exploit free_list_match; eauto. intros (tm' & HFL & HM).
      inv MP. clear pe. rename pe0 into pe.
      pose proof (sem_cast_mse _ (penv_footprint_dec pe)).
      transport H0. subst.
      eexists. split.
      econstructor; eauto.
      erewrite <- transl_expr_typeof; eauto.
      monadInv TRF. apply H3.
      rewrite <- blocks_of_env_same. apply HFL.
      constructor; eauto.
      apply pmatch_call_cont. eauto.

    (* skip call *)
    - monadInv TRS.
      exploit free_list_match; eauto. intros (tm' & HFL & HM).
      eexists. split.
      constructor. eapply pmatch_is_call_cont; eauto.
      rewrite <- blocks_of_env_same. eauto.
      constructor; eauto.

    (* switch *)
    - monadInv TRS.
      eapply eval_expr_correct in H; eauto. cbn in *.
      eexists; split.
      econstructor; eauto.
      erewrite <- transl_expr_typeof; eauto.
      constructor; eauto.
      apply transl_seq_of_labeled_statement. apply transl_select_switch. eauto.
      constructor. eauto.

    (* skip-break switch *)
    - inv MK. destruct H; subst;
        monadInv TRS; eexists; split; constructor; eauto.

    (* continue switch *)
    - monadInv TRS. inv MK. eexists. split.
      eapply step_continue_switch.
      constructor; eauto.

    (* label *)
    - monadInv TRS. eexists; split; constructor; eauto.

    (* goto *)
    - monadInv TRS. pose proof TRF. monadInv TRF.
      exploit pmatch_find_label; eauto.
      intros (ts' & tk' & HLB & HS & HK).
      eexists; split.
      constructor; eauto.
      constructor; eauto.

    (* internal function *)
    - exploit functions_translated; eauto. intros (i & tfd & HFD & HTF).
      monadInv HTF.
      exploit pmatch_function_entry1; eauto. intros (tm' & HFE & HM & HE).
      eexists. split.
      constructor; eauto.
      constructor; eauto.
      monadInv EQ. cbn. eauto.

    (* external function *)
    - exploit functions_translated; eauto. intros (i & tfd & HFD & HTF).
      monadInv HTF.
      exploit external_call_match; eauto. intros (tm' & HEC & HM).
      eexists. split.
      econstructor; eauto.
      constructor; eauto.

    (* return *)
    - inv MK.
      eexists. split. constructor. constructor; eauto.
  Qed.

End PRESERVATION.

Theorem transl_program_correct prog tprog:
  transl_program prog = OK tprog ->
  forward_simulation cc_id cc_penv (ClightP.clightp1 prog) (Clight.semantics1 tprog).
Proof.
  intros H. constructor. econstructor.
  - admit.
  - admit.
  - intros se1 se2 wb Hse Hse1. instantiate (1 := fun _ _ _ => _). cbn beta.
    eapply forward_simulation_step with (match_states := pmatch_state se2).
    + admit.
    + admit.
    + admit.
    + cbn.
      intros. destruct s1, s1'.
      eapply step_correct; eauto.
      inv Hse. eauto.
Admitted.


(*
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
*)
