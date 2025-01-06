Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Ctypes Cop Ctyping.
Require Import Globalenvs.
Require Import Rusttypes RustOp Rustlight Rustlightown.
Require Import RustIR RustIRown.
Require Import Errors Maps.
Require Archi.

Import ListNotations.
Local Open Scope error_monad_scope.

(* To move *)
Definition type_unop (op: unary_operation) (ty: Rusttypes.type) : res type :=
  match op with
  | Onotbool =>
      match classify_bool ty with
      | bool_default => Error (msg "operator !")
      | _ => OK (Tint IBool Signed )
      end
  | Onotint =>
      match classify_notint ty with
      | notint_case_i sg => OK (Tint I32 sg )
      | notint_case_l sg => OK (Tlong sg )
      | notint_default   => Error (msg "operator ~")
      end
  | Oneg =>
      match classify_neg ty with
      | neg_case_i sg => OK (Tint I32 sg )
      | neg_case_f => OK (Tfloat F64 )
      | neg_case_s => OK (Tfloat F32 )
      | neg_case_l sg => OK (Tlong sg )
      | neg_default   => Error (msg "operator prefix -")
      end
  | Oabsfloat =>
      match classify_neg ty with
      | neg_default   => Error (msg "operator __builtin_fabs")
      | _             => OK (Tfloat F64 )
      end
  end.


Definition numeric_type (ty: type) :=
  match ty with
  (** NB : We do not support i/u8 i/u16 in binary operation otherwise
  we need to consider the signed/zero extension of the result, which
  is conflict with the val_casted properties. A solution is to change
  the definition of sem_add... to consider signed extension after add
  operation. But it is complicated. *)
  | Tint I32 _
  | Tlong _ 
  | Tfloat _ => true
  | _ => false
  end.

Definition numeric_ctype (ty: Ctypes.type) :=
  match ty with
  | Ctypes.Tint I32 _ _
  | Ctypes.Tlong _  _
  | Ctypes.Tfloat _ _ => true
  | _ => false
  end.

Definition binarith_type (ty1 ty2: type) (m: string): res type :=
  (* To avoid complicated type cast, we restrict that ty1 must be
  equal to ty2 in binary operation and both of them are numeric
  type *)
  if type_eq ty1 ty2 then
    if numeric_type ty1 then
      OK ty1
    else Error (msg m)
  else Error (msg m).
  (* match classify_binarith ty1 ty2 with *)
  (* | bin_case_i sg => OK (Tint I32 sg noattr) *)
  (* | bin_case_l sg => OK (Tlong sg noattr) *)
  (* | bin_case_f => OK (Tfloat F64 noattr) *)
  (* | bin_case_s => OK (Tfloat F32 noattr) *)
  (* | bin_default   => Error (msg m) *)
  (* end. *)

Definition binarith_int_type (ty1 ty2: type) (m: string): res type :=
  if type_eq_except_origins ty1 ty2 then
    match ty1 with
    | Tint _ _
    | Tlong _ => OK ty1
    | _ =>  Error (msg m)
    end
  else  Error (msg m).
  (* match classify_binarith ty1 ty2 with *)
  (* | bin_case_i sg => OK (Tint I32 sg noattr) *)
  (* | bin_case_l sg => OK (Tlong sg noattr) *)
  (* | _ => Error (msg m) *)
  (* end. *)

Definition shift_op_type (ty1 ty2: type) (m: string): res type :=
  match classify_shift ty1 ty2 with
  | shift_case_ii sg | shift_case_il sg => OK (Tint I32 sg )
  | shift_case_li sg | shift_case_ll sg => OK (Tlong sg )
  | shift_default => Error (msg m)
  end.

Definition comparison_type (ty1 ty2: type) (m: string): res type :=
  if type_eq ty1 ty2 then
    if numeric_type ty1 then
      OK type_bool
    else Error (msg m)
  else Error (msg m).

  (* match classify_binarith ty1 ty2 with *)
  (* | bin_default => Error (msg m) *)
  (* | _ => OK (Tint I32 Signed noattr) *)
  (* end. *)

Definition type_binop (op: binary_operation) (ty1 ty2: type) : res type :=
  match op with
  | Oadd => binarith_type ty1 ty2 "operator infix +"
  | Osub => binarith_type ty1 ty2 "operator infix -"
  | Omul => binarith_type ty1 ty2 "operator infix *"
  | Odiv => binarith_type ty1 ty2 "operator /"
  | Omod => binarith_int_type ty1 ty2 "operator %"
  | Oand => binarith_int_type ty1 ty2 "operator &"
  | Oor => binarith_int_type ty1 ty2 "operator |"
  | Oxor => binarith_int_type ty1 ty2 "operator ^"
  | Oshl => shift_op_type ty1 ty2 "operator <<"
  | Oshr => shift_op_type ty1 ty2 "operator >>"
  | Oeq => comparison_type ty1 ty2 "operator =="
  | One => comparison_type ty1 ty2 "operator !="
  | Olt => comparison_type ty1 ty2 "operator <"
  | Ogt => comparison_type ty1 ty2 "operator >"
  | Ole => comparison_type ty1 ty2 "operator <="
  | Oge => comparison_type ty1 ty2 "operator >="
  end.

(** * Syntactic type checking  *)

Definition type_deref (ty: type) : res type :=
  match ty with
  (* Only support box type to be dereferenced for now *)
  | Tbox tyelt => OK tyelt
  (* | Treference _ _ tyelt => OK tyelt *)
  | _ => Error (msg "type_deref error")
  end.

Lemma type_deref_some: forall ty1 ty2,
    type_deref ty1 = OK ty2 ->
    ty1 = Tbox ty2.
Proof.
  destruct ty1; intros; simpl in *; try congruence.
Qed.


(* Some simple type checking (move to Rusttyping.v) *)

(* We do not support array type and reference type for now *)
Definition valid_type (ty: type) : bool :=
  match ty with
  | Tarray _ _
  | Treference _ _ _
  | Tfunction _ _ _ _ _ => false
  | _ => true
  end.

Definition not_composite (ty: type) : bool :=
  match ty with
  | Tstruct _ _
  | Tvariant _ _ => false
  | _ => true
  end.

Definition typenv := PTree.t type.

Section TYPING.

Variable te: typenv.
Variable ce: composite_env.

Inductive wt_place : place -> Prop :=
| wt_local: forall id ty
    (WT1: te ! id = Some ty)
    (VTY: valid_type ty = true),
    wt_place (Plocal id ty)
| wt_deref: forall p ty
    (WT1: wt_place p)
    (WT2: type_deref (typeof_place p) = OK ty),
    (* (VTY: valid_type ty = true), *)
    wt_place (Pderef p ty)
| wt_field: forall p ty fid co orgs id
    (WT1: wt_place p)
    (WT2: typeof_place p = Tstruct orgs id)
    (WT3: ce ! id = Some co)
    (WT4: field_type fid co.(co_members) = OK ty)
    (WT5: co.(co_sv) = Struct),
    wt_place (Pfield p fid ty)
| wt_downcast: forall p ty fid co orgs id
    (WT1: wt_place p)
    (WT2: typeof_place p = Tvariant orgs id)
    (WT3: ce ! id = Some co)
    (WT4: field_type fid co.(co_members) = OK ty)
    (WT5: co.(co_sv) = TaggedUnion),
    wt_place (Pdowncast p fid ty).

Inductive wt_pexpr: pexpr -> Prop :=
| wt_Eunit:
  wt_pexpr Eunit
| wt_Econst_int: forall n sz si,
    wt_pexpr (Econst_int n (Tint sz si))
| wt_Econst_float: forall f sz,
    wt_pexpr (Econst_float f (Tfloat sz))
| wt_Econst_single: forall f sz,
    wt_pexpr (Econst_single f (Tfloat sz))
| wt_Econst_long: forall n si,
    wt_pexpr (Econst_long n (Tlong si))
| wt_Eplace: forall p
    (WTP1: wt_place p),
    wt_pexpr (Eplace p (typeof_place p))
| wt_Ecktag: forall p fid orgs id
    (WTP1: typeof_place p = Tvariant orgs id)
    (WTP2: wt_place p),
    wt_pexpr (Ecktag p fid)
| wt_Eref: forall p org mut
    (WTP1: wt_place p),
    wt_pexpr (Eref org mut p (Treference org mut (typeof_place p)))
| wt_Eunop: forall uop pe ty
    (WTP1: wt_pexpr pe)
    (WTP2: type_unop uop (typeof_pexpr pe) = OK ty),
    wt_pexpr (Eunop uop pe ty)
| wt_Ebinop: forall bop pe1 pe2 ty
    (WTP1: wt_pexpr pe1)
    (WTP2: wt_pexpr pe2)
    (** FIXME: we use a very restrictive type checking for binary operation *)
    (WTP2: type_binop bop (typeof_pexpr pe1) (typeof_pexpr pe2) = OK ty),
    wt_pexpr (Ebinop bop pe1 pe2 ty).
    
Inductive wt_expr: expr -> Prop :=
| wt_move_place: forall p
    (WT1: wt_place p)
    (SCALAR: scalar_type (typeof_place p) = false),
    wt_expr (Emoveplace p (typeof_place p))
| wt_pure_expr: forall pe
    (SCALAR: scalar_type (typeof_pexpr pe) = true)
    (WT1: wt_pexpr pe),
    wt_expr pe
.

Definition wt_exprlist al : Prop :=
  Forall wt_expr al.

Inductive wt_stmt: statement -> Prop :=
| wt_Sassign: forall p e
    (WT1: wt_place p)
    (WT2: wt_expr e),
    (* Require the type of p equal to the type of e? *)
    wt_stmt (Sassign p e)
| wt_Sassign_variant: forall p id fid e co
    (WT1: wt_place p)
    (WT2: wt_expr e)
    (WT3: ce ! id = Some co)
    (* used to prove assign_loc_variant_sound *)
    (WT4: co.(co_sv) = TaggedUnion),
    wt_stmt (Sassign_variant p id fid e)
| wt_Sbox: forall p e ty
    (WT1: wt_place p)
    (WT2: wt_expr e)
    (WT3: typeof_place p = Tbox ty)
    (* used to prove wt_fooprint *)
    (SZEQ: sizeof ce ty = sizeof ce (typeof e))
    (SZCK: 0 < sizeof ce (typeof e) <= Ptrofs.max_unsigned),
    wt_stmt (Sbox p e)
| wt_Scall: forall p al id ty orgs rels tyl rty cc
    (WT1: wt_place p)
    (WT2: wt_exprlist al)
    (WT3: ty = Tfunction orgs rels tyl rty cc),
    (* We only support this kind of function call *)
    wt_stmt (Scall p (Eglobal id ty) al)
| wt_Sifthenelse: forall e s1 s2
    (WT1: wt_expr e)
    (WT2: wt_stmt s1)
    (WT3: wt_stmt s2),    
    wt_stmt (Sifthenelse e s1 s2)
| wt_Sreturn: forall p
    (WT1: wt_place p)
    (WT2: not_composite (typeof_place p) = true),
    wt_stmt (Sreturn p)
.

End TYPING.

Coercion env_to_tenv (e: env) : typenv :=
  PTree.map1 snd e.


Lemma get_tenv_some: forall e id ty,
    (env_to_tenv e) ! id = Some ty ->
    exists b, e ! id = Some (b, ty).
Proof.
  intros. unfold env_to_tenv in H. erewrite PTree.gmap1 in H.
  unfold option_map in H. destruct (e!id) eqn: A; try congruence.
  destruct p. simpl in H. inv H. eauto.
Qed.

Lemma sizeof_by_value:
  forall ce ty chunk,
  Rusttypes.access_mode ty = Ctypes.By_value chunk -> size_chunk chunk = sizeof ce ty.
Proof.
  unfold Rusttypes.access_mode; intros.
  assert (size_chunk chunk = sizeof ce ty).
  {
    destruct ty; try destruct i; try destruct s; try destruct f; inv H; auto;
    unfold Mptr; simpl; destruct Archi.ptr64; auto.
  }
  lia.
Qed.

Lemma alignof_by_value:
  forall ce ty chunk,
  Rusttypes.access_mode ty = Ctypes.By_value chunk -> (align_chunk chunk | alignof ce ty).
Proof.
  unfold Rusttypes.access_mode; intros.
  destruct ty; try destruct i; try destruct s; try destruct f; inv H; auto;
    unfold Mptr; simpl; destruct Archi.ptr64; try apply Z.divide_refl.
  exists 2. auto.
  exists 2. auto.
Qed.

Lemma wt_place_wt_local: forall p (e: env) ce,
    wt_place e ce p ->
    exists b ty, e ! (local_of_place p) = Some (b, ty).
Proof.
  induction p; intros.
  - inv H. simpl. unfold env_to_tenv in WT1. rewrite PTree.gmap1 in WT1.
    destruct (e!i) eqn: A. inv WT1. destruct p. eauto.
    inv WT1.
  - inv H. simpl. eauto.
  - inv H. simpl. eauto.
  - inv H. simpl. eauto.
Qed.

Fixpoint typeof_cont_call (ttop: type) (k: cont) : type :=
  match k with
  | Kcall p _ _ _ _ =>
      typeof_place p
  | Kstop => ttop
  | Kseq _ k
  | Kloop _ k
  (* impossible? *)
  | Kdropplace _ _ _ _ _ k
  | Kdropcall _ _ _ _ k => typeof_cont_call ttop k
  end.


(** Typing of functions and programs *)

Fixpoint bind_vars (te: typenv) (l: list (ident * type)) : typenv :=
  match l with
  | nil => te
  | (id, ty) :: l' =>
      bind_vars (PTree.set id ty te) l'
  end.

Lemma bind_vars_app: forall l1 l2 le,
    bind_vars (bind_vars le l1) l2 = bind_vars le (l1 ++ l2).
Proof.
  induction l1; simpl; auto.
  intros. destruct a; auto.
Qed.
  
Inductive wt_function (ce: composite_env) : function -> Prop :=
  | wt_function_intro: forall f
      (WTS1: wt_stmt (bind_vars (bind_vars (PTree.empty _) f.(fn_params)) f.(fn_vars)) ce f.(fn_body)),
      wt_function ce f.

Inductive wt_fundef (ce: composite_env) : fundef -> Prop :=
| wt_fundef_internal: forall f,
    wt_function ce f ->
    wt_fundef ce (Internal f)
| wt_fundef_external: forall ef targs tres cc orgs rels,
    (* (ef_sig ef).(sig_res) = rettype_of_type tres -> *)
    wt_fundef ce (External orgs rels ef targs tres cc).

Inductive wt_program : program -> Prop :=
| wt_program_intro: forall p,
    (forall id fd,
        In (id, Gfun fd) p.(prog_defs) ->
        wt_fundef p.(prog_comp_env) fd) ->
    wt_program p.

Section PRESERVATION.

Variable prog: program.
Hypothesis WTPROG: wt_program prog.
Variable se: Genv.symtbl.
Let ge := globalenv se prog.

Variable sg: rust_signature.
(* Well-typed continuation and state *)

Inductive wt_cont : typenv -> function -> cont -> Prop :=
| wt_Kseq: forall s k f te
    (WT1: wt_stmt te ge s)
    (WT2: wt_cont te f k),
    wt_cont te f (Kseq s k)
| wt_Kcall: forall k p f f' le own te
    (WT1: wt_call_cont (Kcall p f' le own k) f.(fn_return)),
    wt_cont te f (Kcall p f' le own k)

with wt_call_cont : cont -> type -> Prop :=
| wt_call_Kstop:
  wt_call_cont  Kstop (rs_sig_res sg)
| wt_call_Kcall: forall p f (le: env) own k
    (WT1: wt_cont le f k)
    (WT2: wt_place le ge p),
    (* For simplicity, we do not consider casting in function call *)
  wt_call_cont (Kcall p f le own k) (typeof_place p)
.


Inductive wt_state : state -> Prop :=
| wt_regular_state: forall f s k (e: env) own m
    (WT1: wt_stmt e ge s)                  
    (WT2: wt_cont e f k),
    wt_state (State f s k e own m)
| wt_callstate: forall vf fd orgs rels tyl rty cc k m vl
    (FIND: Genv.find_funct ge vf = Some fd)
    (FTY: type_of_fundef fd = Tfunction orgs rels tyl rty cc)
    (WT1: wt_call_cont k rty),
    wt_state (Callstate vf vl k m)
| wt_returnstate: forall k rty m v
    (WT1: wt_call_cont k rty),
    wt_state (Returnstate v k m)
| wt_dropplace_state: forall f st drops k own m (e: env)
    (WT1: Forall (fun p => wt_place e ge p) (map fst drops)),
    wt_state (Dropplace f st drops k e own m)
.

Lemma wt_call_cont_type_eq: forall k ty1,
    wt_call_cont k ty1 ->
    typeof_cont_call (rs_sig_res sg) k = ty1.
Proof.
  induction 1; intros; simpl in *; auto.
Qed.

Lemma is_wt_call_cont:
  forall te f k,
    is_call_cont k -> wt_cont te f k -> wt_call_cont k f.(fn_return).
Proof.
  intros. inv H0; simpl in H; try contradiction. auto.
Qed.

Lemma wt_cont_call_cont: forall k le f ck,
    wt_cont le f k ->
    call_cont k = Some ck ->
    wt_cont le f ck.
Proof.
  induction 1; intros CC; simpl in *; auto; try (inv CC; econstructor; eauto).
Qed.

Lemma call_cont_wt_call_cont:
  forall te f k ck,
    call_cont k = Some ck ->
    wt_cont te f k -> wt_call_cont ck f.(fn_return).
Proof.
  intros. eapply (is_wt_call_cont te).
  eapply call_cont_correct. eauto.
  eapply wt_cont_call_cont; eauto.
Qed.


End PRESERVATION.

(** Type checking algorithm *)

Section COMP_ENV.

  Variable ce: composite_env.
  Variable te: typenv.
  
  Fixpoint type_check_place (p: place) : res unit :=
    match p with
    | Plocal id ty1 =>
        match te ! id with
        | Some ty2 =>
            if type_eq ty1 ty2 && valid_type ty1 then
              OK tt
            else
              Error [CTX id; MSG "has wrong type"]
        | _ =>
            Error [CTX id; MSG "is not declared"]
        end
    | Pderef p ty =>
        do _ <- type_check_place p;
        do ty1 <- type_deref (typeof_place p);
        if type_eq ty ty1 then
          OK tt
        else
          Error (msg "deref has wrong type")
    | Pfield p fid fty =>
        do _ <- type_check_place p;
        match typeof_place p with
        | Tstruct orgs id =>
            match ce ! id with
            | Some co =>
                match co_sv co with
                | Struct =>
                    do fty1 <- field_type fid (co_members co);
                    if type_eq fty fty1 then
                  OK tt
                    else
                      Error (msg "wrong field type")
                | _ => Error (msg "not struct in field type")
                end
            | _ => Error (msg "no composite")
            end
        | _ =>  Error (msg "wrong struct type")
        end
    | Pdowncast p fid fty =>
        do _ <- type_check_place p;
        match typeof_place p with
        | Tvariant orgs id =>
            match ce ! id with
            | Some co =>
                match co_sv co with
                | TaggedUnion =>
                    do fty1 <- field_type fid (co_members co);
                    if type_eq fty fty1 then
                  OK tt
                    else
                      Error (msg "wrong field type")
                | _ => Error (msg "not variant in downcast type")
                end
            | _ => Error (msg "no composite")
            end
        | _ =>  Error (msg "wrong enum type")
        end
    end.
    
End COMP_ENV.

(** Soundness of type checking  *)

Lemma type_check_place_sound: forall ce te p,
    type_check_place ce te p = OK tt ->
    wt_place te ce p.
Proof.
  induction p; intros; simpl in *.
  - destruct (te!i) eqn: A1; try congruence.
    destruct (type_eq t t0 && valid_type t) eqn: A2; try congruence.
    eapply andb_true_iff in A2 as (A3 & A4).
    destruct type_eq in A3; simpl in A3; try congruence. subst.
    econstructor; eauto.
  - monadInv H.
    destruct (typeof_place p) eqn: PTY; try congruence.
    destruct (ce!i0) eqn: CO; try congruence.
    destruct (co_sv c) eqn: SV; try congruence.
    monadInv EQ0.
    destruct type_eq; try congruence. subst.
    destruct x.
    econstructor; eauto. 
  - monadInv H.    
    destruct type_eq; try congruence. subst.
    destruct x.
    econstructor; eauto.
  - monadInv H.
    destruct (typeof_place p) eqn: PTY; try congruence.
    destruct (ce!i0) eqn: CO; try congruence.
    destruct (co_sv c) eqn: SV; try congruence.
    monadInv EQ0.
    destruct type_eq; try congruence. subst.
    destruct x.
    econstructor; eauto.
Qed.

(** End of syntactic type checking  *)

(** Some properties of is_prefix of well-typed places *)

Lemma paths_contain_app_one_inv: forall l1 l2 ph,
    paths_contain l1 (l2 ++ [ph]) = true ->
    l1 = l2 ++ [ph] \/ paths_contain l1 l2 = true.
Proof.
  induction l1; intros; simpl in *; auto.
  destruct l2; simpl in *.
  + destruct path_eq; subst.
    * destruct l1; simpl in H; try congruence. auto.
    * congruence.
  + destruct path_eq; subst.
    * exploit IHl1; eauto.
      intros [A|B].
      -- subst. left. auto.
      -- auto.
    * congruence.
Qed.

Lemma path_of_place_nil: forall p id,
    path_of_place p = (id, nil) ->
    exists ty, p = Plocal id ty.
Proof.
  induction p; intros id A; simpl in *.
  - inv A; eauto.
  - destruct (path_of_place p) eqn: P. inv A.
    exploit app_eq_nil. eapply H1. intros (A1 & A2). inv A2.
  - destruct (path_of_place p) eqn: P. inv A.
    exploit app_eq_nil. eapply H1. intros (A1 & A2). inv A2.
  - destruct (path_of_place p) eqn: P. inv A.
    exploit app_eq_nil. eapply H1. intros (A1 & A2). inv A2.
Qed.  

Lemma path_of_place_field: forall p id fid l,
    path_of_place p = (id, l ++ [ph_field fid]) ->
    exists p' fty,
      p = Pfield p' fid fty
      /\ path_of_place p' = (id, l).
Proof.
  induction p; intros id fid l A; simpl in *.
  - inv A. exploit app_eq_nil. symmetry. eapply H1.
    intros (A1 & A2). inv A2.
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2. subst.
    eauto.
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2.
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2.
Qed.

Lemma path_of_place_deref: forall p id l,
    path_of_place p = (id, l ++ [ph_deref]) ->
    exists p' ty,
      p = Pderef p' ty
      /\ path_of_place p' = (id, l).
Proof.
  induction p; intros id l A; simpl in *.
  - inv A. exploit app_eq_nil. symmetry. eapply H1.
    intros (A1 & A2). inv A2.
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2.    
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2. 
    eauto.
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2.
Qed.

Lemma path_of_place_downcast: forall p id ty fid l,
    path_of_place p = (id, l ++ [ph_downcast ty fid]) ->
    exists p' fty,
      p = Pdowncast p' fid fty
      /\ path_of_place p' = (id, l).
Proof.
  induction p; intros id ty fid l A; simpl in *.
  - inv A. exploit app_eq_nil. symmetry. eapply H1.
    intros (A1 & A2). inv A2.
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2.    
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2.
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2. subst.
    eauto.
Qed.

Lemma path_of_wt_place_eq: forall le ce p1 p2,
    wt_place le ce p1 ->
    wt_place le ce p2 ->
    path_of_place p1 = path_of_place p2 ->
    p1 = p2.
Proof.
  induction p1; intros p2 WT1 WT2 PEQ; simpl in *; destruct (path_of_place p2) eqn: P2; try (destruct (path_of_place p1) eqn: P1).
  - inv PEQ.
    eapply path_of_place_nil in P2 as (ty & A1). subst.
    inv WT1. inv WT2. rewrite WT0 in WT1. inv WT1. auto.
  - inv PEQ. eapply path_of_place_field in P2 as (p' & fty & A1 & A2).
    subst. inv WT1. inv WT2.
    exploit IHp1. eapply WT0. eapply WT1. eauto. intros. subst.
    rewrite WT3 in WT7. inv WT7. rewrite WT4 in WT8. inv WT8.
    rewrite WT5 in WT9. inv WT9. auto.
  - inv PEQ. eapply path_of_place_deref in P2 as (p' & ty & A1 & A2).
    subst. inv WT1. inv WT2.
    exploit IHp1. eapply WT0. eapply WT1. eauto. intros. subst.
    rewrite WT3 in WT4. inv WT4. auto.
  - inv PEQ. eapply path_of_place_downcast in P2 as (p' & fty & A1 & A2).
    subst. inv WT1. inv WT2.
    exploit IHp1. eapply WT0. eapply WT1. eauto. intros. subst.
    rewrite WT3 in WT7. inv WT7. rewrite WT4 in WT8. inv WT8.
    rewrite WT5 in WT9. inv WT9. auto.
Qed.

(** is_prefix and is_prefix_type are equivalent under two well-type places *)
Lemma is_prefix_wt: forall ce le p2 p1,
    wt_place le ce p1 ->
    wt_place le ce p2 ->
    is_prefix p1 p2 = true ->
    is_prefix_type p1 p2 = true.
Proof.
  induction p2; intros p1 WT1 WT2 PRE; simpl in *.
  - destr_prefix. inv POP0.
    destruct l; simpl in PRE1; try congruence.
    eapply path_of_place_nil in POP as (ty & A1). subst.
    inv WT1. inv WT2.
    rewrite WT0 in WT1. inv WT1.
    unfold is_prefix_type.
    destruct place_eq; try congruence. auto.    
  - inv WT2.
    destr_prefix.
    destruct (path_of_place p2) eqn: POP2. inv POP0.
    exploit paths_contain_app_one_inv. eapply PRE1.
    intros [A|B].
    + subst. eapply path_of_place_field in POP as (p' & fty & A1 & A2).
      subst. inv WT1.
      exploit path_of_wt_place_eq. eapply WT0. eapply WT2.
      rewrite POP2. rewrite A2. auto. intros. subst.
      rewrite WT3 in WT7. inv WT7. rewrite WT4 in WT8. inv WT8.
      rewrite WT5 in WT9. inv WT9.
      eapply orb_true_iff. left.
      destruct place_eq; try congruence; auto.
    + exploit IHp2. eapply WT1. eapply WT0.
      unfold is_prefix. rewrite POP. rewrite POP2. rewrite B.
      destruct ident_eq; try congruence; auto.
      intros PRE2.
      eapply orb_true_iff. right.
      eapply proj_sumbool_is_true. simpl.       
      unfold is_prefix_type in PRE2.
      eapply orb_true_iff in PRE2.
      destruct PRE2 as [A1|A1]; try apply proj_sumbool_true in A1; subst; auto.
  - inv WT2.
    destr_prefix.
    destruct (path_of_place p2) eqn: POP2. inv POP0.
    exploit paths_contain_app_one_inv. eapply PRE1.
    intros [A|B].
    + subst. eapply path_of_place_deref in POP as (p' & ty & A1 & A2).
      subst. inv WT1.
      exploit path_of_wt_place_eq. eapply WT0. eapply WT2.
      rewrite POP2. rewrite A2. auto. intros. subst.
      rewrite WT3 in WT4. inv WT4.
      eapply orb_true_iff. left.
      eapply proj_sumbool_is_true. auto.
    + exploit IHp2. eapply WT1. eapply WT0.
      unfold is_prefix. rewrite POP. rewrite POP2. rewrite B.
      rewrite proj_sumbool_is_true; auto.
      intros PRE2.
      eapply orb_true_iff. right.
      eapply proj_sumbool_is_true. simpl.       
      unfold is_prefix_type in PRE2.
      eapply orb_true_iff in PRE2.
      destruct PRE2 as [A1|A1]; try apply proj_sumbool_true in A1; subst; auto.
  - inv WT2.
    destr_prefix.
    destruct (path_of_place p2) eqn: POP2. inv POP0.
    exploit paths_contain_app_one_inv. eapply PRE1.
    intros [A|B].
    + subst. eapply path_of_place_downcast in POP as (p' & fty & A1 & A2).
      subst. inv WT1.
      exploit path_of_wt_place_eq. eapply WT0. eapply WT2.
      rewrite POP2. rewrite A2. auto. intros. subst.
      rewrite WT3 in WT7. inv WT7. rewrite WT4 in WT8. inv WT8.
      rewrite WT5 in WT9. inv WT9.
      eapply orb_true_iff. left.
      eapply proj_sumbool_is_true. auto.
    + exploit IHp2. eapply WT1. eapply WT0.
      unfold is_prefix. rewrite POP. rewrite POP2. rewrite B.
      rewrite proj_sumbool_is_true; auto.
      intros PRE2.
      eapply orb_true_iff. right.
      eapply proj_sumbool_is_true. simpl.       
      unfold is_prefix_type in PRE2.
      eapply orb_true_iff in PRE2.
      destruct PRE2 as [A1|A1]; try apply proj_sumbool_true in A1; subst; auto.
Qed.      
  
