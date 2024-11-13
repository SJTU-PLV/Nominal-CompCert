Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Ctypes Cop Ctyping.
Require Import Rusttypes RustOp Rustlight.
Require Import Errors Maps.
Require Archi.

Local Open Scope error_monad_scope.

(* This file is not used for now *)

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


(** Try to prove that evaluaiton of expression produces val_casted value *)

Definition typenv := PTree.t type.

Section TYPING.
  
Variable te: typenv.
Variable ce: composite_env.

Lemma wt_int_dec: forall n sz sg, {wt_int n sz sg} + {~ wt_int n sz sg}.
Proof.
  intros. destruct sz, sg;simpl;try eapply Int.eq_dec.
  auto. auto.
Qed.  

Fixpoint wt_place (p: place) : res type :=
  match p with
  | Plocal id ty =>
      match te!id with
      | Some ty' =>
          if type_eq_except_origins ty ty' then
            OK ty
          else Error (msg "local type error")
      | None => Error (msg "local type error")
      end
  | Pderef p ty =>
      do ty' <- wt_place p;
      if type_eq_except_origins ty ty' then
        OK ty
      else Error (msg "deref type error")
  | Pfield p fid ty =>
      do pty <- wt_place p;
      match pty with
      | Tstruct _ sid =>
          match ce!sid with
          | Some co =>
              do fty <- field_type fid co.(co_members);
              if type_eq_except_origins ty fty then
                OK ty
              else Error (msg "field type error")
          | None => Error (msg "field type error")
          end
      | _ => Error (msg "field type error")
      end
  | Pdowncast p fid ty =>
      do pty <- wt_place p;
      match pty with
      | Tvariant _ sid =>
          match ce!sid with
          | Some co =>
              do fty <- field_type fid co.(co_members);
              if type_eq_except_origins ty fty then
                OK ty
              else Error (msg "downcast type error")
          | None => Error (msg "downcast type error")
          end
      | _ => Error (msg "downcast type error")
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

        
(* strict typing *)
Fixpoint wt_pexpr (pe: pexpr) : res type :=
  match pe with
  | Eunit => OK Tunit
  (* some adhoc case: we do not support non zero/one cast to bool *)
  | Econst_int i (Tint IBool sg) =>
      if Int.eq i Int.zero || Int.eq i Int.one then
        OK (Tint IBool sg)
      else Error (msg "const bool")              
  | Econst_int i (Tint sz sg) =>
      if wt_int_dec i sz sg then
        OK (Tint sz sg)
      else Error (msg "const int")
  | Econst_float f (Tfloat F64 ) => OK (Tfloat F64 )
  | Econst_single f (Tfloat F32) => OK (Tfloat F32)
  | Econst_long i (Tlong sg) => OK (Tlong sg)
  | Eplace p ty =>
      do pty <- wt_place p;
      if type_eq_except_origins ty pty then
        OK ty
      else Error (msg "Eplace type error")
  | Ecktag p fid =>
      OK type_bool
  | Eref orgs mut p ty =>
      do pty <- wt_place p;
      if type_eq_except_origins ty (Treference orgs mut pty) then
        OK ty
      else Error (msg "Eref type error")
  | Eunop uop pe ty =>
      do ety <- wt_pexpr pe;
      do oty <- type_unop uop ety;
      if type_eq_except_origins ty oty then
        OK ty
      else Error (msg "Eunop type error")
  | Ebinop bop pe1 pe2 ty =>
      do ety1 <- wt_pexpr pe1;
      do ety2 <- wt_pexpr pe2;
      do oty <- type_binop bop ety1 ety2;
      if type_eq_except_origins ty oty then
        OK ty
      else Error (msg "Ebinop type error")
  | _ => Error (msg "other type error in pexpr")
  end.

Lemma typeof_wt_pexpr: forall pe ty,
    wt_pexpr pe = OK ty ->
    typeof_pexpr pe = ty.
Proof.
  induction pe;intros ty;simpl;intros WT;inv WT;auto.
  - destruct t;try congruence. destruct wt_int_dec;try congruence.
    destruct i0; try congruence.
    destruct (Int.eq i Int.zero || Int.eq i Int.one);try congruence.
    destruct i0; try congruence.
    destruct (Int.eq i Int.zero || Int.eq i Int.one);try congruence.    
  - destruct t;try congruence. destruct f0;try congruence.
  - destruct t;try congruence. destruct f0;try congruence.
  - destruct t;try congruence.
  - monadInv H0. destruct type_eq_except_origins;try congruence.
  - monadInv H0. destruct type_eq_except_origins;try congruence.
  - monadInv H0. destruct type_eq_except_origins;try congruence.
  - monadInv H0. destruct type_eq_except_origins;try congruence.
Qed.


Lemma sem_notbool_type: forall v1 v2 ty m,
    sem_notbool v1 ty m = Some v2 ->
    Cop.val_casted v2 (Ctypes.Tint IBool Signed noattr).
Proof.
  unfold sem_notbool.
  intros. destruct (bool_val v1 ty m);simpl in H;inv H.
  destruct b;simpl; econstructor;auto.
Qed.

Lemma wt_sem_unary_operation_casted: forall u t1 t2 v1 v2 m,
    type_unop u t1 = OK t2 ->
    sem_unary_operation u v1 (to_ctype t1) m = Some v2 ->
    Cop.val_casted v2 (to_ctype t2).
Proof.
  intros until m. destruct u;simpl. intros TYOP SEM.
  - eapply sem_notbool_type in SEM.
    destruct (classify_bool t1); try congruence; inv TYOP;auto.
  - destruct (classify_notint t1) eqn: A; try congruence; intros B C;inv B.
    + destruct t1;simpl in A; try congruence.
      simpl.
      unfold sem_notint in C. simpl in C.
      destruct i; destruct s0; destruct v1; try congruence;inv C; econstructor; auto.
    + destruct t1;simpl in A; try congruence.
      simpl.
      unfold sem_notint in C. simpl in C.
      destruct i; destruct s0; destruct v1; try congruence;inv C; econstructor; auto.
      inv A. unfold sem_notint in C. simpl in C.
      destruct v1; try congruence;inv C; econstructor; auto.
  - unfold sem_neg. destruct t1; simpl; try congruence; intros B C.
    + destruct i; inv B.
      * destruct v1; try congruence. inv C.
        simpl. econstructor. auto.
      * destruct v1; try congruence. inv C.
        simpl. econstructor. auto.
      * destruct s. inv H0.
        destruct v1; try congruence. inv C.
        simpl. econstructor. auto.
        inv H0. destruct v1; try congruence. inv C.
        simpl. econstructor. auto.
      * destruct v1; try congruence. inv C.
        simpl. econstructor. auto.
    + inv B. destruct v1; try congruence. inv C.
      simpl. econstructor.
    + destruct f; inv B.
      * destruct v1; try congruence. inv C.
        simpl. econstructor.
      * destruct v1; try congruence. inv C.
        simpl. econstructor.
  - unfold sem_absfloat. destruct t1; simpl; try congruence; intros B C.
    + destruct i;destruct s;try congruence; inv B.
      1-8 : destruct v1; try congruence; inv C; simpl; econstructor. 
    + inv B. destruct v1; try congruence; inv C; simpl; econstructor.
    + destruct f;inv B.
      1-2: destruct v1; try congruence; inv C; simpl; econstructor.
Qed.

Lemma binarith_type_ctype: forall t1 t2 t s,
  binarith_type t1 t2 s = OK t ->
  Cop.binarith_type (classify_binarith (to_ctype t1) (to_ctype t2)) = to_ctype t.
Admitted.

Lemma binarith_type_strict: forall t1 t2 t s,
    binarith_type t1 t2 s = OK t ->
    to_ctype t1 = to_ctype t /\ to_ctype t2 = to_ctype t.
Admitted.

Lemma binarith_type_numeric: forall t1 t2 t s,
    binarith_type t1 t2 s = OK t ->
    numeric_type t = true.
Admitted.

Lemma to_ctype_numeric: forall t,
    numeric_type t = numeric_ctype (to_ctype t).
Admitted.


Lemma binarith_add_casted: forall t1 t2 t v1 v2 v m s,
    binarith_type t1 t2 s = OK t ->
    Cop.val_casted v1 (to_ctype t1) ->
    Cop.val_casted v2 (to_ctype t2) ->
    sem_add_rust v1 (to_ctype t1) v2 (to_ctype t2) m = Some v ->
    Cop.val_casted v (to_ctype t).
Proof.
  
  unfold sem_add_rust. unfold sem_binarith.
  intros until s. intros BINTY CAST1 CAST2.
  erewrite binarith_type_ctype;eauto.
  exploit binarith_type_strict;eauto. intros (T1 & T2).
  rewrite T1 in *. rewrite T2 in *.
  erewrite cast_val_casted;eauto. erewrite cast_val_casted;eauto.
  (* ct is numeric *)
  exploit to_ctype_numeric. instantiate (1 := t).
  rewrite (binarith_type_numeric t1 t2 t s).
  intros NUM. symmetry in NUM.  
  set (ct:= to_ctype t) in *.
  destruct (classify_add ct ct); try congruence.
  destruct ct eqn: CT; simpl; try congruence.
  destruct i;destruct s0;
    destruct v1; try congruence; destruct v2;try congruence; intros ADD; inv ADD; try econstructor;simpl in NUM; try congruence.
  1-2:simpl;auto.
  destruct s;destruct s0;
    destruct v1; try congruence; destruct v2;try congruence; intros ADD; inv ADD; try econstructor;simpl in NUM; try congruence.
  destruct f;destruct v1; try congruence; destruct v2;try congruence; intros ADD; inv ADD; try econstructor;simpl in NUM; try congruence.
  auto.
Qed.

Lemma wt_sem_binary_operation_casted: forall bop t1 t2 t v1 v2 v m,
    type_binop bop t1 t2 = OK t ->
    Cop.val_casted v1 (to_ctype t1) ->
    Cop.val_casted v2 (to_ctype t2) ->    
    sem_binary_operation_rust bop v1 (to_ctype t1) v2 (to_ctype t2) m = Some v ->
    Cop.val_casted v (to_ctype t).
Proof.
  destruct bop; intros until m; simpl.
  - eapply binarith_add_casted.
    (* similar to above *)    
Admitted.

(* To move *)
Lemma type_eq_except_origins_to_ctype: forall ty1 ty2,
    type_eq_except_origins ty1 ty2 = true ->
    to_ctype ty1 = to_ctype ty2.
Proof.
  induction ty1;simpl; intros; try eapply proj_sumbool_true in H;subst;auto.
  - destruct ty2; try eapply proj_sumbool_true in H; try congruence.
    destruct m; destruct m0.
    simpl; f_equal. eapply IHty1;auto.
    congruence. congruence.
    simpl; f_equal. eapply IHty1;auto.
  - destruct ty2;try eapply proj_sumbool_true in H; try congruence.
    subst. auto.
  - destruct ty2;try eapply proj_sumbool_true in H; try congruence.
    subst. auto.
Qed.

Lemma wt_pexpr_typeof: forall pe ty,
    wt_pexpr pe = OK ty ->
    typeof_pexpr pe = ty.
Proof.
  induction pe; simpl; intros ty WT; inv WT;auto.
  - destruct t; inv H0.
    destruct i0; inv H1. destruct wt_int_dec; inv H0; auto.
    destruct wt_int_dec; inv H0; auto.
    destruct wt_int_dec; inv H0; auto.
    destruct orb;inv H0;auto.
  - destruct t; inv H0. destruct f0; inv H1.
    auto.
  - destruct t; inv H0. destruct f0; inv H1.
    auto.
  - destruct t; inv H0. auto.
  - monadInv H0. destruct (type_eq_except_origins);inv EQ0. auto.
  - monadInv H0. destruct (type_eq_except_origins);inv EQ0. auto.
  - monadInv H0. destruct (type_eq_except_origins);inv EQ2. auto.
  - monadInv H0. destruct (type_eq_except_origins);inv EQ3. auto.
Qed.

Lemma access_mode_ctype: forall ty,
    access_mode ty = Ctypes.access_mode (to_ctype ty).
Proof.
  intros.
  destruct ty;simpl;auto.
Qed.

Lemma wt_deref_loc:
  forall ty m b ofs v,
  deref_loc ty m b ofs v ->
  wt_val v (to_ctype ty).
Proof.
  induction 1.
  - simpl in H0. exploit Mem.load_result; eauto. intros EQ; rewrite EQ.
    apply wt_decode_val. erewrite <-access_mode_ctype. auto.
  - destruct ty; simpl in *; try discriminate; auto with ty.
    destruct i; destruct s; discriminate.
    destruct f; discriminate.
- (* by copy *)
  destruct ty; simpl in *; try discriminate; auto with ty.
  destruct i; destruct s; discriminate.
  destruct f; discriminate.
Qed.

Section SEM.

Variable e: env.
Variable m: mem.

Lemma wt_int_casted: forall n sz sg,
    sz <> IBool ->
    wt_int n sz sg ->
    cast_int_int sz sg n = n.
Proof.
  unfold wt_int, cast_int_int.
  intros n sz sg.
  destruct sz;try congruence.
  destruct sg;auto.
  destruct sg;auto.
Qed.

  

Lemma eval_pexpr_casted: forall pe v ety,
    wt_pexpr pe = OK ety ->
    eval_pexpr ce e m pe v ->
    Cop.val_casted v (to_ctype (typeof_pexpr pe)).
Proof.
  (* induction hypothesis is useless *)
  induction pe; intros v ety; simpl; intros WT EVAL; inv WT; inv EVAL; auto.
  - destruct t; try congruence. 
    destruct i0 eqn: SZ; econstructor.
    + try destruct wt_int_dec;try congruence. eapply wt_int_casted. congruence. auto.
    + try destruct wt_int_dec;try congruence. eapply wt_int_casted. congruence. auto.
    + try destruct wt_int_dec;try congruence. eapply wt_int_casted. congruence. auto.
    + destruct (Int.eq i Int.zero || Int.eq i Int.one) eqn: EQ; try congruence.
      inv H0. simpl.
      eapply orb_true_iff in EQ. destruct EQ.
      rewrite H. exploit Int.eq_spec. rewrite H. auto.
      exploit Int.eq_spec. rewrite H. intros.
      destruct (Int.eq i Int.zero) eqn: EQ;auto.
      exploit Int.eq_spec. rewrite EQ. intros.
      exfalso.
      eapply Int.one_not_zero. subst. auto.
  - destruct t; try congruence. destruct f0; try congruence.
    inv H0. simpl. econstructor.
  - destruct t; try congruence. destruct f0; try congruence.
    inv H0. simpl. econstructor.
  - destruct t; try congruence. 
    inv H0. simpl. econstructor.
  - monadInv H0. destruct (type_eq_except_origins t x) eqn: TYEQ;try congruence.
    inv EQ0.
  (* add type checking after deref_loc in eval_pexpr *)
    exploit wt_deref_loc;eauto. intros WT.
    
    inv WT; simpl; try econstructor; eauto.
    (* Three cases unresolved: Tarray, Tfunction and Vundef. We can
    restrict it in eval_pexpr place case. *)
    admit. admit. admit. admit.
    
  - destruct (Int.unsigned tag =? tagz) eqn:CKTAG.
    econstructor. simpl. erewrite Int.eq_false. auto. eapply Int.one_not_zero.
    econstructor. simpl. erewrite Int.eq_true. auto.
  - monadInv H0.
    destruct (type_eq_except_origins t (Treference o m0 x)) eqn: TYEQ.
    admit. congruence.
  (* unop *)
  - monadInv H0.
    (* exploit IHpe;eauto. intros CASTED. *)
    destruct (type_eq_except_origins t x0) eqn: TYEQ; try congruence.
    inv EQ2.
    erewrite type_eq_except_origins_to_ctype;eauto.
    eapply wt_sem_unary_operation_casted;eauto.
    erewrite typeof_wt_pexpr in H6;eauto.
  (* binop *)
  - monadInv H0.
    exploit IHpe1;eauto. intros CASTED1.
    exploit IHpe2;eauto. intros CASTED2.
    destruct type_eq_except_origins; try congruence. inv EQ3.
Admitted.

End SEM.
End TYPING.


