Require Import Coqlib Integers Errors.
Require Import Hex encode.Bits Memdata.
Require Import Encode.
Import String Ascii.
Import List.
Import ListNotations.
Import Hex Bits.
(* Require Import Intersection. *)
Require Import Coq.Logic.Eqdep_dec ListDestruct.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.



Definition assertLength {A} (l:list A) n: {length l = n} +
                                          {length l <> n}.
Proof.
  decide equality.
Defined.

Definition builtIn (n:nat): Type := {d:list bool| length d = n}.

Lemma builtin_inj: forall {n} (a b:builtIn n),
    proj1_sig a = proj1_sig b -> a = b.
Proof.
  intros n a b H.
  induction a, b.
  simpl in H.
  subst x0.
  f_equal.
  apply UIP_dec.
  apply Nat.eq_dec.
Qed.


Ltac unravel_all_branch:=
match goal with
|[H: ?L \/ ?R|-_] => destruct H as [H|H]
end.

Definition binary := list byte.


Axiom bit_patterns_extensionality :
forall f g : (bits -> bool), (forall x : bits, f x = g x) -> f = g.

Definition bpt_neq (f g: bits -> bool) :=
exists x, f x <> g x.

Lemma bpt_neq_sound : forall f g,
  bpt_neq f g -> f <> g.
Proof.
intros.
red in H.
destruct H.
intros NE.
subst.
congruence.
Qed.

Lemma bpt_neq_sym: forall f g,
  bpt_neq f g -> bpt_neq g f.
Proof.
intros f g H.
unfold bpt_neq in *.
destruct H as (x & H).
exists x. auto.
Qed.

(** new way to define bp *)

(* Parameter bp_and : bits -> bits -> bits. *)
(* Parameter bp_or : bits -> bits -> bits. *)
(* Parameter bp_eq : bits -> bits -> bool. *)
(* Parameter bp_neq : bits -> bits -> bool. *)

(** give a coq implementation to test *)
Fixpoint bp_and (b1 b2:bits): bits :=
  match b1, b2 with
  |[], _ => []
  |_ , [] => []
  |true::t1, true::t2 => true::(bp_and t1 t2)
  |_::t1, _::t2 => false::(bp_and t1 t2)
  end.

(* Unused *)
Fixpoint bp_or (b1 b2:bits): bits :=
  match b1, b2 with
  |[], _ => []
  |_ , [] => []
  |false::t1, false::t2 => false::(bp_or t1 t2)
  |_::t1, _::t2 => true::(bp_or t1 t2)
  end.

Fixpoint bp_eq (b1 b2:bits): bool :=
  match b1, b2 with
  |[], _ => true
  |_ , [] => true
  |false::t1, false::t2 => true && (bp_eq t1 t2)
  |true::t1, true::t2 => true && (bp_eq t1 t2)
  |_::t1, _::t2 => false
  end.

Fixpoint bp_neq (b1 b2:bits): bool :=
  match b1, b2 with
  |[], _ => false
  |_ , [] => false
  |false::t1, false::t2 => bp_neq t1 t2
  |true::t1, true::t2 => bp_neq t1 t2
  |_::t1, _::t2 => true
  end.


Lemma bp_and_eq: forall l1 l2 b1 b2,
    bp_and (b1::l1) (b2::l2) = if b1 then b2::bp_and l1 l2 else false::bp_and l1 l2.
Proof.
  intros. simpl. destruct b1;auto.
  destruct b2;auto.
Qed.

Lemma bp_eq_eq: forall l1 l2 b1 b2,
    bp_eq (b1::l1) (b2::l2) = (bool_eq b1 b2) && bp_eq l1 l2.
Proof.
  intros. destruct b1;destruct b2;auto.
Qed.

Lemma bp_neq_eq: forall l1 l2 b1 b2,
    bp_neq (b1::l1) (b2::l2) = (negb (bool_eq b1 b2)) || bp_neq l1 l2.
Proof.
  intros. destruct b1;destruct b2;auto.
Qed.


(* little endian *)
Definition nat_to_bits8 n : bits :=
  [(n mod 2 =? 1);
  ( n/2 mod 2 =? 1);
  ( n/4 mod 2 =? 1);
  ( n/8 mod 2 =? 1);
  ( n/16 mod 2 =? 1);
  ( n/32 mod 2 =? 1);
  ( n/64 mod 2 =? 1);
  ( n/128 mod 2 =? 1)].

Fixpoint bytes_to_bits (lb:list byte) : bits :=
  match lb with
  | [] => []
  | b::lb' =>(nat_to_bits8 (Z.to_nat(Byte.unsigned b))) ++ (bytes_to_bits lb')
  end.



(* bits must be a multiple of 8 *)
Fixpoint bits_to_bytes (bs:bits) : res (list byte) :=
  match bs with
  |[] => OK ([])
  |b0::b1::b2::b3::b4::b5::b6::b7::tail =>
   let head := bB[b7::b6::b5::b4::b3::b2::b1::b0::[]] in
   do tailBytes <- bits_to_bytes tail;
   OK(head::tailBytes)
  |_ => Error(msg"Bits is not a multiple of 8")
  end.


Lemma destruct_bits8: forall b:bits,
  length b = 8%nat ->
  exists b0 b1 b2 b3 b4 b5 b6 b7, b = b7::b6::b5::b4::b3::b2::b1::b0::[].
Proof.
  intros.
  destruct b as [|b7 b];[simpl in *; congruence|].
  destruct b as [|b6 b];[simpl in *; congruence|].
  destruct b as [|b5 b];[simpl in *; congruence|].
  destruct b as [|b4 b];[simpl in *; congruence|].
  destruct b as [|b3 b];[simpl in *; congruence|].
  destruct b as [|b2 b];[simpl in *; congruence|].
  destruct b as [|b1 b];[simpl in *; congruence|].
  destruct b as [|b0 b];[simpl in *; congruence|].
  destruct b. repeat eexists.
  simpl in H. congruence.
Qed.

Lemma bytes_to_bits_correct : forall b,
    length b = 8%nat -> (*also 8*n*)
    bytes_to_bits [bB[rev b]] = b.
Proof.
  intros.
  generalize (destruct_bits8 b H).
  intros (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & HBEq).
  subst b. cbn [rev app].
  destruct b7; destruct b6; destruct b5; destruct b4;
  destruct b3; destruct b2; destruct b1; destruct b0; reflexivity.
Qed.

Lemma bytes_to_bits_cons_correct :forall b l,
  length b = 8%nat ->
  bytes_to_bits (bB[rev b]::l) = b ++ bytes_to_bits l.
Proof.
  intros.
  apply bytes_to_bits_correct in H.
  unfold bytes_to_bits in *.
  rewrite app_nil_r in H. rewrite H. auto.
Qed.

Lemma byte_to_bits_correct : forall b,
  length b = 8%nat ->
  nat_to_bits8 (Z.to_nat(Byte.unsigned bB[rev b])) = b.
Proof.
  intros.
  apply bytes_to_bits_correct in H.
  unfold bytes_to_bits in H.
  rewrite app_nil_r in H. auto.
Qed.


Lemma unfold_bB : forall int intrange,
    {|Byte.intval := int; Byte.intrange := intrange |} = Byte.repr int.
Proof.
  intros. erewrite Byte.eqm_repr_eq. reflexivity. simpl.  apply Byte.eqm_refl.
Qed.

Lemma byte_modulus_pos:
  Byte.modulus = 256%Z.
Proof.
  auto.
Qed.
Lemma byte_destruct: forall byt,
    exists b7 b6 b5 b4 b3 b2 b1 b0,
      byt = bB[b7::b6::b5::b4::b3::b2::b1::[b0]].
Proof.
  intros. destruct byt.
  rewrite unfold_bB.
  assert (exists b7 b6 b5 b4 b3 b2 b1 b0, intval = bits_to_Z [b7;b6;b5;b4;b3;b2;b1;b0]) as H0.
  destruct intval.
  - repeat exists false. auto.
  - induction p. rewrite byte_modulus_pos in *.
    + exploit IHp. lia.
      intros (b7 & b6 & b5 & b4 & b3 & b2 & b1 & b0 & Hz).
      exists b6,b5,b4,b3,b2,b1,b0,true.
      unfold bits_to_Z in *. unfold bits_to_Z_acc in *.
      assert (b7 = false).
      destruct b7. rewrite Pos2Z.pos_xI in intrange.
      assert (256 < 2*Z.pos p +1)%Z.
        rewrite Hz.
        destruct b6;destruct b5; destruct b4; destruct b3;
          destruct b2; destruct b1; destruct b0; simpl; lia.
        apply Z.lt_asymm in H.
        destruct intrange. congruence. auto.
      rewrite H in Hz.
      rewrite Pos2Z.pos_xI. rewrite Hz. auto.
   + exploit IHp. lia. rewrite byte_modulus_pos in *.
      intros (b7 & b6 & b5 & b4 & b3 & b2 & b1 & b0 & Hz).
      exists b6,b5,b4,b3,b2,b1,b0,false.
      unfold bits_to_Z in *. unfold bits_to_Z_acc in *.
      assert (b7 = false).
      destruct b7. rewrite Pos2Z.pos_xO in intrange.
      assert (256 <= 2*Z.pos p)%Z.
      rewrite Hz.
      destruct b6;destruct b5; destruct b4; destruct b3;
      destruct b2; destruct b1; destruct b0; simpl; lia.
      apply Zle_not_lt in H.
      destruct intrange. congruence. auto.
      rewrite H in Hz.
      rewrite Pos2Z.pos_xO. rewrite Hz.
      destruct b6;destruct b5;  destruct b4; destruct b3;
      destruct b2; destruct b1; destruct b0; auto.
   + exists false,false,false,false,false,false,false,true. auto.
  - lia.
  - destruct H0 as (b7 & b6 & b5 & b4 & b3 & b2 & b1 & b0 & H).
    rewrite H. repeat eexists.
Qed.





Ltac destr_byte b:=
  let b7 := fresh "b7" in
  let b6 := fresh "b6" in
  let b5 := fresh "b5" in
  let b4 := fresh "b4" in
  let b3 := fresh "b3" in
  let b2 := fresh "b2" in
  let b1 := fresh "b1" in
  let b0 := fresh "b0" in
  let HBEq := fresh "HBEq" in
  match goal with
  |_ => generalize (byte_destruct b);
        intros (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & HBEq);
        subst b
  end.


Ltac destr_const_byte n :=
  let b00 := fresh "b00" in
  set (b00 := Byte.repr n);
  destr_byte b00.

Ltac hexize_byte_value n:=
  let HHex := fresh "HHex" in
  assert(HHex: Byte.repr n = bB[ bytes_to_bits [Byte.repr n]]);[ 
    unfold bytes_to_bits;rewrite Byte.unsigned_repr;
    simpl; auto;
    unfold Byte.max_unsigned;
    simpl; lia|];
  unfold bytes_to_bits in HHex;
  rewrite Byte.unsigned_repr in HHex;
  [simpl in HHex|unfold Byte.max_unsigned;simpl;lia].



Ltac solve_neq ce :=
match goal with
|[|- context G [bpt_neq ?f1 ?f2]] =>
 unfold bpt_neq;
 exists ce;
 unfold f1; unfold f2; simpl; congruence
end.


Hint Resolve  bpt_neq_sym: bpneq.




(* begin from lst@[0] change into nth_error *)
Notation "lst @[ n ]":= (nth_error lst n) (at level 20).
(* exclusive, meaning that lst~@[0]=[] *)
Notation "lst ~@[ n ]":= (firstn  n lst) (at level 20).
(* exclusive, meaning that lst-@[0]=lst *)
Notation "lst >@[ n ]" := (skipn n lst) (at level 20).



Definition try_first_n {A:Type} (l:list A) (n:nat): res (list A) :=
  if length l <? n then
    Error(msg"list too short in first n")
  else
    OK(firstn n l).

Lemma first_n_prefix: forall {A} (prefix:list A) suffix,
    firstn (length prefix) (prefix++suffix) = prefix.
Proof.
  intros A0 prefix suffix.
  rewrite<- (Nat.add_0_r (Datatypes.length prefix)).
  rewrite (firstn_app_2 0 _ _).
  rewrite firstn_O.
  rewrite app_nil_r.
  reflexivity.
Qed.




Definition try_skip_n {A:Type} (l:list A) (n:nat): res (list A) :=
  if length l <? n then
    Error(msg"list too short in skip n")
  else
    OK(skipn n l).

Lemma skip_n_prefix: forall {A} (prefix:list A) suffix,
    skipn (length prefix) (prefix++suffix) = suffix.
Proof.
  intros A0 prefix suffix.
  rewrite skipn_app.
  rewrite Nat.sub_diag.
  rewrite skipn_O.
  rewrite skipn_all.
  rewrite app_nil_l.
  auto.
Qed.


Definition try_get_n {A:Type} (l:list A) (n:nat): res A :=
  if length l <? n+1 then
    Error(msg"list too short in get n")
  else
    match nth_error l n with
    |Some a => OK a
    |_ => Error(msg"impossible")
    end.


Lemma get_last_element: forall {A: Type} (l: list A) element prefix,
      l = prefix ++ [element]
      -> l @[(length l) -1] = Some element.
Proof.
  induction l.
  - destruct prefix; simpl in *; congruence.
  - intros. simpl. destruct prefix.
    + simpl in *. inv H. simpl. auto.
    + simpl in H.
      assert ( H0:a::l = [a]++l). auto. rewrite H0.
      rewrite nth_error_app2; inv H.
      exploit IHl. eauto.
      rewrite Nat.sub_0_r. auto.
      destruct prefix; simpl; lia.
Qed.

Lemma get_prefix: forall {A: Type} (l: list A) element prefix,
      l = prefix ++ [element]
      -> l ~@[(length l) -1] = prefix.
Proof.
  induction l.
  - destruct prefix; simpl; congruence.
  - intros. destruct prefix.
    + inv H. auto.
    + inv H. exploit IHl; eauto. intro.
      assert ( H0:a0::prefix++[element] = [a0]++(prefix++[element])). auto. rewrite H0.
      assert ((Datatypes.length([a0]++prefix++[element]) -1) =
              (Datatypes.length [a0]) + (Datatypes.length(prefix ++ [element]) -1)).
      destruct prefix; simpl; lia. rewrite H10.
      rewrite firstn_app_2. rewrite H. auto.
Qed.


(* complete induction on natural numbers *)
Lemma bits_to_bytes_len_induc: forall n bs bytes,
    length bs <= n ->
    bits_to_bytes bs = OK bytes ->
    length bytes = length bs /8.
Proof.
  induction n.
  - intros. destruct bs. inv H10. auto. simpl in H. lia.
  - intros.
    destruct bs; inv H10. auto.
    destruct bs; try congruence.
    destruct bs; try congruence.
    destruct bs; try congruence.
    destruct bs; try congruence.
    destruct bs; try congruence.
    destruct bs; try congruence.
    destruct bs; try congruence.
    apply bind_inversion in H12.
    destruct H12 as (x & H1 & H2).
    inv H2.
    assert (b::b0::b1::b2::b3::b4::b5::b6::bs = [b;b0;b1;b2;b3;b4;b5;b6]++bs).
    auto. rewrite H10. rewrite app_length.
    transitivity (S(Datatypes.length bs/8)).
    erewrite <- IHn; eauto. simpl. auto.
    simpl in H. lia.
    assert (Datatypes.length[b;b0;b1;b2;b3;b4;b5;b6] = 1*8 ). simpl. auto.
    rewrite H11.
    rewrite Nat.div_add_l. auto. auto.
Qed.

Lemma bits_to_bytes_len: forall bs bytes,
            bits_to_bytes bs = OK bytes ->
            length bytes = length bs / 8.
Proof.
  intros. eapply bits_to_bytes_len_induc; eauto.
Qed.

Lemma bytes_to_bits_app: forall l1 l2,
    bytes_to_bits (l1++l2) = (bytes_to_bits l1) ++ (bytes_to_bits l2).
Proof.
  induction l1.
  - simpl. auto.
  - intros.
    transitivity ((nat_to_bits8(Z.to_nat(Byte.unsigned a))) ++ bytes_to_bits(l1++l2)). auto.
    rewrite IHl1. auto.
Qed.

Lemma bytes_to_bits_cons :forall b l,
    bytes_to_bits (b::l) = (bytes_to_bits [b]) ++ (bytes_to_bits l).
Proof.
  intros.
  assert (b::l = [b]++l). auto. rewrite H.
  apply bytes_to_bits_app.
Qed.

Lemma bytes_to_bits_len: forall bytes,
    length(bytes_to_bits bytes) = 8*(length bytes).
Proof.
  intros. induction bytes.
  - auto.
  - simpl. rewrite IHbytes. lia.
Qed.

(* complete induction on natural numbers *)
Lemma bits_to_bytes_to_bits_induc: forall n bs bytes,
    length bs <= n ->
    bits_to_bytes bs = OK bytes ->
    bytes_to_bits bytes = bs.
Proof.
  induction n.
  - intros. destruct bs. inv H10. auto. simpl in H. lia.
  - intros.
    destruct bs; inv H10. auto.
    destruct bs; try congruence.
    destruct bs; try congruence.
    destruct bs; try congruence.
    destruct bs; try congruence.
    destruct bs; try congruence.
    destruct bs; try congruence.
    destruct bs; try congruence.
    apply bind_inversion in H12.
    destruct H12 as (x & H1 & H2).
    inv H2.
    assert (b::b0::b1::b2::b3::b4::b5::b6::bs = [b;b0;b1;b2;b3;b4;b5;b6]++bs).
    auto. rewrite H10.
    rewrite bytes_to_bits_cons.
    assert ([b6; b5; b4; b3; b2; b1; b0; b] = rev [b; b0; b1; b2; b3; b4; b5; b6]) by reflexivity.
    rewrite H11.
    rewrite bytes_to_bits_correct.
    erewrite IHn; eauto. simpl in H. lia. auto.
Qed.

Lemma bits_to_bytes_to_bits: forall bytes bs,
            bits_to_bytes bs = OK bytes
            -> bytes_to_bits bytes = bs.
Proof.
  intros. eapply bits_to_bytes_to_bits_induc; eauto.
Qed.

Ltac byte_range:=
  unfold Byte.max_unsigned; simpl; lia.

(*autoproof modify*)
Ltac _solve_try_skip_n:=
  let EQL := fresh "EQL" in
  match goal with
  |[|-context G[try_skip_n (?x ++ ?l) (length ?x)]]
   => unfold try_skip_n at 1;
       destruct Nat.ltb eqn:EQL at 1;
       [apply Nat.ltb_lt in EQL;
        repeat rewrite app_length in EQL;
        lia|
        rewrite skip_n_prefix;cbn [bind]];clear EQL
  |[|-context G[try_skip_n _ _]]
   => (*repeat rewrite<-app_assoc*)
      unfold try_skip_n at 1;
       destruct Nat.ltb eqn:EQL at 1;
       [apply Nat.ltb_lt in EQL;
        repeat rewrite app_length in EQL;
        simpl in EQL;
        lia|
        cbn [skipn];cbn [bind]];clear EQL
 end.


Ltac solve_try_skip_n:=
  let EQL := fresh "EQL" in
  match goal with
  |[|-context G[try_skip_n (?x ++ ?l) (length ?x)]]
   => _solve_try_skip_n
  |[H: length ?x = ?n |- context G[try_skip_n (?x++?l) ?n ]]
   => rewrite <- H at 1; _solve_try_skip_n
  |[|-context G[try_skip_n _ _]]
   => _solve_try_skip_n
  end.

(*autoproof modify*)
Ltac _solve_try_first_n :=
  let EQL := fresh "EQL" in
  match goal with
  |[|-context G[try_first_n (?x++?suffix) (length ?x)]]
   =>
    unfold try_first_n at 1;
    destruct Nat.ltb eqn:EQL at 1;
    [apply Nat.ltb_lt in EQL; 
     repeat rewrite app_length in EQL;
     lia
    |rewrite first_n_prefix;cbn [bind]];clear EQL
  |[|-context G[try_first_n _ _]]
   => (*repeat rewrite<-app_assoc*)
      unfold try_first_n at 1;
       destruct Nat.ltb eqn:EQL at 1;
       [apply Nat.ltb_lt in EQL;
        repeat rewrite app_length in EQL;
        simpl in EQL;
        lia|
        cbn [firstn];cbn [bind]];clear EQL
  end.

(*add for jmp_ap*)
Ltac solve_try_first_n :=
  let HLen:=fresh"HLen" in
  match goal with
  | |- context G[ try_first_n (?x ++ ?suffix) (Datatypes.length ?n) ]
    => _solve_try_first_n
  | H:Datatypes.length ?x = ?n
    |- context G[ try_first_n (?x ++ ?suffix) ?n ] => 
    rewrite <- H  at 1; _solve_try_first_n
  | H1:length ?x = _ , H2:bits_to_bytes ?x = OK ?l |-
    context G [try_first_n (?l ++ ?suffix) _] =>
    generalize (bits_to_bytes_len _ _ H2); intros HLen;
    rewrite H1 in HLen; simpl in HLen;
    rewrite <- HLen at 1; _solve_try_first_n
  | |- context G[ try_first_n _ _ ] =>
    _solve_try_first_n
  end.

Ltac solve_assertion :=
  let EQA := fresh "EQA" in
  let lef := fresh "lef" in
  match goal with
  | |- context G[ assertLength (_ _) _ ] =>
      destruct assertLength as [lef| rig] eqn:EQA in |- * at 1; [  | simpl in rig; congruence ];
      clear EQA
  end.





(*add*)
Ltac solve_try_get_n :=
       match goal with
       |[|- context G[try_get_n ?x 0]]
        => simpl x at 1;
          unfold try_get_n at 1;
          destruct Nat.ltb eqn:EQL at 1;
          [apply Nat.ltb_lt in EQL;
           repeat rewrite app_length in EQL;
           simpl in EQL;
           lia|
           cbn [nth_error];cbn [bind]];clear EQL
       end.

(*need to correct:repeated conclusion appear*)
Ltac get_len_facts:=
  let HLen := fresh "HLen" in
  match goal with
  |[HL: length ?l = ?n, HBs: bits_to_bytes ?l = OK ?x |- _]
   => generalize (bits_to_bytes_len _ _ HBs);
     intros HLen;
     rewrite HL in HLen;
     simpl in HLen
  end.


Ltac enc_dec_normalize :=
  repeat rewrite<- app_assoc;
  repeat rewrite app_length;
  try lia.

Ltac solve_bytes_to_bits :=
  match goal with
  |[|- context G[bytes_to_bits [bB[?l]]]]
   => rewrite bytes_to_bits_correct;enc_dec_normalize;auto
  end.

Ltac everything := try solve_try_skip_n; try solve_try_first_n;
                   try enc_dec_normalize; try solve_assertion;
                   try solve_bytes_to_bits;
                   simpl.

Lemma len_exists: forall {A} l n,
    length l = S n
    ->exists (b:A) tail, l = b::tail /\ length tail = n.
Proof.
  intros. destruct l eqn:Hl.
  - simpl in H. congruence.
  - exists a,l0. auto.
Qed.

Ltac destr_token l :=
  match goal with
  | [H: length l = 8, l: list _ |- _ ] =>
      generalize (list_length8_destruct _ l H);
      intros (? & ? & ? & ? & ? & ? & ? & ? & ?);subst l;try clear H
  |[H: length l = 32, l: list _ |- _ ] =>
     generalize (list_length32_destruct _ l H);
     intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?);subst l;try clear H
  | [H: 8 = length l, l: list _ |- _ ] =>
      symmetry in H;
      generalize (list_length8_destruct _ l H);
      intros (? & ? & ? & ? & ? & ? & ? & ? & ?);subst l;try clear H
  |[H: 32 = length l, l: list _ |- _ ] =>
     symmetry in H;
     generalize (list_length32_destruct _ l H);
     intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?);subst l;try clear H
  end.


Ltac destr_all_lists :=
  match goal with
  |[H: length ?l = 1, l: list _ |- _ ] =>
     generalize (list_length1_destruct _ l H);
    intros (? & ?);subst l;try clear H    
  |[H: length ?l = 2, l: list _ |- _ ] =>
     generalize (list_length2_destruct _ l H);
    intros (? & ? & ?);subst l;try clear H
  |[H: length ?l = 3, l: list _ |- _ ] =>
     generalize (list_length3_destruct _ l H);
    intros (? & ? & ? & ?);subst l;try clear H
  |[H: length ?l = 4, l: list _ |- _ ] =>
     generalize (list_length4_destruct _ l H);
    intros (? & ? & ? & ? & ?);subst l;try clear H
  |[H: length ?l = 5, l: list _ |- _ ] =>
     generalize (list_length5_destruct _ l H);
    intros (? & ? & ? & ? & ? & ?);subst l;try clear H
  |[H: length ?l = 6, l: list _ |- _ ] =>
     generalize (list_length6_destruct _ l H);
    intros (? & ? & ? & ? & ? & ? & ?);subst l;try clear H
  |[H: length ?l = 7, l: list _ |- _ ] =>
     generalize (list_length7_destruct _ l H);
    intros (? & ? & ? & ? & ? & ? & ? & ?);subst l;try clear H
  |[H: length ?l = 8, l: list _ |- _ ] =>
     generalize (list_length8_destruct _ l H);
    intros (? & ? & ? & ? & ? & ? & ? & ? & ?);subst l;try clear H
  |[H: length ?l = 9, l: list _ |- _ ] =>
     generalize (list_length9_destruct _ l H);
    intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ?);subst l;try clear H
  |[H: length ?l = 10, l: list _ |- _ ] =>
     generalize (list_length10_destruct _ l H);
    intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?);subst l;try clear H
  |[H: length ?l = 11, l: list _ |- _ ] =>
     generalize (list_length11_destruct _ l H);
    intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?);subst l;try clear H
  |[H: length ?l = 12, l: list _ |- _ ] =>
     generalize (list_length12_destruct _ l H);
    intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?);subst l;try clear H
  |[H: length ?l = 20, l: list _ |- _ ] =>
     generalize (list_length20_destruct _ l H);
    intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?);subst l;try clear H
  |[H: length ?l = 32, l: list _ |- _ ] =>
     generalize (list_length32_destruct _ l H);
    intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?);subst l;try clear H
  end.

(* Lemma test: forall (l:list bool), *)
(*     length l = 32 -> *)
(*   length l = 32. *)
(* Proof. *)
(* intros. repeat destr_all_lists. *)

Ltac solve_length_equal :=
  simpl; repeat rewrite app_length; try lia;
  auto.

Ltac solve_equal:=
  repeat ((apply builtin_inj; simpl; auto)||f_equal);
  autounfold with *; auto;
  solve_length_equal.


  
(*autoproof add*)
(* deprecated *)
Ltac destruct_builtIn :=
      let HHex := fresh "HHex" in
      match goal with
      |[H:?enc ?p1 (?write (Byte.repr 0) ?x) = OK ?x0 |-
        context G [try_get_n (?x0 ++ ?l) 0]] =>
        hexize_byte_value 0%Z;
        rewrite HHex in H;
        destr_list x;
        autounfold with bitfields in H;
        rewrite bytes_to_bits_correct in H;
        [simpl in H|auto]
      end.


(* for list len*)
Lemma list_split_add_n:
  forall A (l1:list A) l2 x1 x2 n, l1++l2=x1++x2 -> n+length x1=length l1->
                   exists x3 x4, length x3=n /\ x2=x3++x4/\ l1=x1++x3.
Proof.
  induction l1.
  - intros. simpl in *; destruct n; try lia.
    destruct x1; simpl in *; try congruence.
    simpl in *. exists nil. exists x2. auto.
  - intros. destruct x1.
    + simpl in *. exists (a::l1),l2.
      split. simpl. lia.
      split. auto. auto.
    + simpl in *. inv H.
      assert (n+Datatypes.length x1=Datatypes.length l1). lia.
      exploit IHl1; eauto.
      intros (x3 & x4 & A & B & C).
      exists x3,x4. split. auto. split. auto. rewrite C. auto.
Qed.

Lemma bytes_to_bits_to_bytes:
  forall b ,bits_to_bytes (bytes_to_bits b) = OK b.
Proof.
  induction b.
  - auto.
  - rewrite bytes_to_bits_cons.
    exploit byte_destruct. instantiate (1:=a).
    intros (b7&b6&b5&b4&b3&b2&b1&b0&H).
    rewrite H.
    assert ([b7; b6; b5; b4; b3; b2; b1; b0]=rev [b0; b1; b2; b3; b4; b5; b6; b7]) by reflexivity.
    rewrite H10.
    rewrite bytes_to_bits_correct.
    simpl. rewrite IHb. auto. auto.
Qed.

Lemma try_first_n_success:
  forall A (l:list A) n l1 ,
    try_first_n l n = OK l1->
    exists l2, l=l1++l2/\length l1=n.
Proof.
  intros. unfold try_first_n in H.
  destruct (Datatypes.length l<?n) eqn:H0. congruence.
  inversion H.
  exists (l >@[n]). split.
  rewrite firstn_skipn. auto.
  apply firstn_length_le.
  apply Nat.ltb_ge. auto.
Qed.

(*ltac for proof*)
(*definition of builtin type*)
(* Definition u? := { data?: list bool| length data? = ?}. *)

Definition u1 := builtIn 1.
Definition u2 := builtIn 2.
Definition u3 := builtIn 3.
Definition u4 := builtIn 4.
Definition u5 := builtIn 5.
Definition u6 := builtIn 6.
Definition u7 := builtIn 7.
Definition u8 := builtIn 8.
Definition u9 := builtIn 9.
Definition u10 := builtIn 10.
Definition u11 := builtIn 11.
Definition u12 := builtIn 12.
Definition u13 := builtIn 13.
Definition u14 := builtIn 14.
Definition u15 := builtIn 15.
Definition u16 := builtIn 16.
Definition u17 := builtIn 17.
Definition u18 := builtIn 18.
Definition u19 := builtIn 19.
Definition u20 := builtIn 20.
Definition u21 := builtIn 21.
Definition u22 := builtIn 22.
Definition u23 := builtIn 23.
Definition u24 := builtIn 24.
Definition u25 := builtIn 25.
Definition u26 := builtIn 26.
Definition u27 := builtIn 27.
Definition u28 := builtIn 28.
Definition u29 := builtIn 29.
Definition u30 := builtIn 30.
Definition u31 := builtIn 31.
Definition u32 := builtIn 32.

Definition u64 := builtIn 64.


Definition builtin_eq_dec:=list_eq_dec bool_dec.


(*so builtin ltac*)

Ltac decision_inv :=
  match goal with
  | H:context G[ if builtin_eq_dec _ _ then Error _ else _ ]
    |- _ => destruct builtin_eq_dec in H;try congruence
  end.

Ltac ind_builtIn:=
    match goal with
    |[H: u1|- _] =>
     induction H
    |[H: u2|- _] =>
     induction H
    |[H: u3|- _] =>
      induction H
    |[H: u4|-_] =>
     induction H
    |[H: u5|-_] =>
     induction H
    |[H: u6|- _] =>
     induction H
    |[H: u7|- _] =>
     induction H
    |[H: u8|- _] =>
      induction H
    |[H: u9|-_] =>
     induction H
    |[H: u10|-_] =>
     induction H
    |[H: u11|- _] =>
     induction H
    |[H: u12|- _] =>
     induction H
    |[H: u13|- _] =>
      induction H
    |[H: u14|-_] =>
     induction H
    |[H: u15|-_] =>
     induction H
    |[H: u16|-_] =>
     induction H
    |[H: u20|-_] =>
     induction H
    |[H: u32|-_] =>
     induction H
    |[H: u64|-_] =>
     induction H
    end.

(*some list ltac*)
Ltac goOver:=
  match goal with
  |[|- context G [?x = ?x]] =>
   (right; goOver)||left
  end.


(*Ltac for dec consistency*)
Ltac monadInv_decode H :=
  let Decode_Len:= fresh "Decode_Len" in
    match type of H with
  | (OK _ = OK _) => 
    injection H;intro Decode_Len;intros;
    try subst;clear H
  | (Error _ = OK _) =>
      discriminate
  | (bind ?F ?G = OK ?X) =>
      let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion F G H) as [x [EQ1 EQ2]];
      clear H;
      try (monadInv_decode EQ2))))
  | (bind2 ?F ?G = OK ?X) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion F G H) as [x1 [x2 [EQ1 EQ2]]];
      clear H;
      try (monadInv_decode EQ2)))))
  | (match ?X with left _ => _ | right _ => Error _  end = OK _) =>
      destruct X; [try (monadInv_decode H) | discriminate]
  | (match (negb ?X) with true => _ | false => Error _  end = OK _) =>
      destruct X as [] eqn:?; simpl negb in H; [discriminate | try (monadInv_decode H)]
  | (match ?X with true => _ | false => Error _  end = OK _) =>
      destruct X as [] eqn:?; [try (monadInv_decode H) | discriminate]
  | (mmap ?F ?L = OK ?M) =>
      generalize (mmap_inversion F L H); intro
    end.

Ltac simpl_branch_decode Dec:=
  match type of Dec with 
  | (if ?cond then _ else _ ) = _ =>
    destruct cond;
    [monadInv_decode Dec;congruence|try congruence]
  end.

Ltac solve_try_get_n_decode H:=
    match type of H with
    |try_get_n (?b::?l) 0 = OK ?x1 =>
     unfold try_get_n in H;
     destruct Nat.ltb in H;[congruence|simpl in H;injection H as H;subst x1]
    | try_get_n ?l 0 = OK ?x1 =>
     unfold try_get_n in H;
     destruct Nat.ltb in H;[congruence|destruct l as [|il l];simpl in H;[congruence|destr_byte il;injection H as H;subst x1]]                             
    end.

  
 Ltac solve_try_skip_n_decode H:=
    match type of H with
 
    | try_skip_n (?x++_) ?n = OK ?x1 =>
      match goal with
        | [H1:length ?x = ?n |- _]=>
          rewrite <- H1 in H;
          unfold try_skip_n in H;
          destruct Nat.ltb in H;[congruence|];
          (* may compute the skipn *)
          rewrite skipn_app in H;
          rewrite <- minus_diag_reverse in H;
          rewrite skipn_all in H;
          simpl in H;
          injection H as H;subst x1
        | [H1:?n = length ?x |- _]=>
          rewrite -> H1 in H;
          unfold try_skip_n in H;
          destruct Nat.ltb in H;[congruence|];
          (* may compute the skipn *)
          rewrite skipn_app in H;
          rewrite <- minus_diag_reverse in H;
          rewrite skipn_all in H;
          simpl in H;
          injection H as H;subst x1
      end
    | try_skip_n _ (S _) = OK _ =>
      unfold try_skip_n in H;
      destruct Nat.ltb in H;[congruence|];
      (* may compute the skipn *)
      simpl in H;
      match type of H with
      | OK (skipn (length ?x) (?x++_)) = OK ?x1 =>
        rewrite skipn_app in H;
        rewrite <- minus_diag_reverse in H;
        rewrite skipn_all in H;
        simpl in H;
        injection H as H;subst x1
      | OK _ = OK ?x1 => injection H as H;subst x1
      end
    | try_skip_n _ ?n = OK ?x1 =>
      (* just unfold and simpl *)
      unfold try_skip_n in H;
      destruct Nat.ltb in H;[congruence|];
      (* may compute the skipn *)
      simpl in H;
      try injection H as H;
      subst x1
    | _ => idtac "error: no try_skip_n"                
    end.

Ltac destruct_const_byte_rewrite n:=
    let HHex := fresh "HHex" in
    assert(HHex: Byte.repr n = bB[ bytes_to_bits [Byte.repr n]]);[ 
    unfold bytes_to_bits;rewrite Byte.unsigned_repr;
    simpl; auto;
    unfold Byte.max_unsigned;
    simpl; lia|];
  unfold bytes_to_bits in HHex;
  rewrite Byte.unsigned_repr in HHex;
  [simpl in HHex|unfold Byte.max_unsigned;simpl;lia];
  rewrite HHex in *;clear HHex.

Ltac destruct_conjunction H :=
  match type of H with
  | (?b = _) /\ _ => destruct H as [? H];subst b;destruct_conjunction H
  | ?b = _ => subst b
  | _ /\ _ => destruct H as [? H];destruct_conjunction H
  | _ => idtac
  end.


Ltac rename_firstn_result H :=
  let name := fresh "firstn_result" in
  match type of H with
  | try_first_n _ _ = OK ?x =>
      rename x into name
  end.


Ltac solve_try_first_n_decode H Decode_Len:=
  let N:=fresh "FIR_APP" in
  let LEN:=fresh "LEN" in
  let APP:=fresh "APP" in
  match type of H with
  | try_first_n (?x++_) ?n = OK ?x1 =>
    match goal with
       (*symmetry*)
      | H1: ?n = length ?x |- _ =>
        rewrite -> H1 in H; unfold try_first_n in H;
        destruct Nat.ltb in H; [ congruence |  ];
        rewrite firstn_app in H; rewrite <- minus_n_n in H;
        rewrite firstn_all in H; simpl in H;
        try rewrite app_nil_r in H; 
        injection H as H;subst x1
      | [H1:length ?x = ?n |- _]=>
        rewrite <- H1 in H;
        unfold try_first_n in H;
        destruct Nat.ltb in H;[congruence|];
        (* may compute the firstn *)
        rewrite firstn_app in H;
        rewrite <- minus_diag_reverse in H;
        rewrite firstn_all in H;
        simpl in H;
        try rewrite app_nil_r in H;
        injection H as H;subst x1
    end
  | try_first_n (_::_) (S _) = OK _ =>
    unfold try_first_n in H;
    destruct Nat.ltb in H;[congruence|];
    (* may compute the firstn *)
    simpl in H;
    match type of H with
    | OK (firstn (length ?x) (?x++_)) = OK ?x1 =>
      rewrite firstn_app in H;
      rewrite <- minus_diag_reverse in H;
      rewrite firstn_all in H;
      simpl in H;
      try rewrite app_nil_r in H;
      injection H as H;subst x1
    | ( OK _ = OK ?x1) =>injection H as H;subst x1
    end
  | try_first_n (?l1++?l2) _ = OK _=>
    generalize (try_first_n_success _ _ _ _ H);
    intros [? [APP LEN]]; try rewrite N in *; clear H;
    (* normalize the plus *)
    rewrite <- LEN in Decode_Len;
    rewrite <- Nat.add_1_l in Decode_Len;
    rewrite Nat.add_comm in Decode_Len;
    try rewrite <- Nat.add_assoc in Decode_Len;
    (* more than one *)
    repeat
      (rewrite <- Nat.add_1_l in Decode_Len;
       rewrite <- Nat.add_assoc in Decode_Len;
       rewrite Nat.add_comm in Decode_Len;
       try rewrite <- Nat.add_assoc in Decode_Len);        
    simpl in Decode_Len; rewrite Nat.add_comm in Decode_Len;
    (* apply list_split_add *)
    generalize (list_split_add_n _ _ _ _ _ _ APP Decode_Len);
    clear APP;clear Decode_Len;
    intros [? [? [? [l2fact lfact]]] ];
    try rewrite  l2fact in *;clear l2fact;
    try rewrite lfact in *;clear lfact;
    try rewrite <- app_assoc in *
  | try_first_n _ _ = OK _ =>
       generalize (try_first_n_success _ _ _ _ H);
       intros [? [N ?]]; try rewrite N in *; clear H
  | _ => idtac "error: no try_first_n"
  end.

Ltac solve_builtin_eq_dec_decode:=
    let Bindec := fresh "Bindec" in
    match goal with
    | [|- context G[builtin_eq_dec]] =>
      repeat rewrite bytes_to_bits_correct by auto;
      destruct builtin_eq_dec as [Bindec|];
      [unfold char_to_bool in Bindec;
      simpl in Bindec;
      rewrite Bindec in *;
      congruence|]
    
    end.


  (* EQ Decode_Len consistency_theorem decode_function *)
  Ltac solve_kls_decode H Decode_Len ConThe Decode:=
    let APP := fresh "APP" in
    let LEN := fresh "LEN" in
    let l2fact:= fresh "l2fact" in
    let lfact := fresh "lfact" in
    simpl in H;
    match type of H with
    | Decode (_::_) = OK _ =>
      apply ConThe in H;
      (* staticaly determined *)
      destruct H as [?[?[APP[LEN H]]]];
      try rewrite APP in *;
      try rewrite LEN in *;
      (* split the l++l' *)
      (* first SSS n -> 3+n... *)
      simpl in Decode_Len;
      try injection Decode_Len as Decode_Len;
      (* len a = len b-> 0+len a=len b *)
      match type of Decode_Len with
      | S _ = _ =>
        (* first time *)
        rewrite <- Nat.add_1_l in Decode_Len;
        rewrite Nat.add_comm in Decode_Len;
        try rewrite <- Nat.add_assoc in Decode_Len;
        (* more than one *)
        repeat
          (rewrite <- Nat.add_1_l in Decode_Len;
           rewrite <- Nat.add_assoc in Decode_Len;
           rewrite Nat.add_comm in Decode_Len;
           try rewrite <- Nat.add_assoc in Decode_Len);
        simpl in Decode_Len; rewrite Nat.add_comm in Decode_Len 
      | ?x = _ =>
        rewrite <- (Nat.add_0_l x) in Decode_Len
      end;       
      generalize (list_split_add_n _ _ _ _ _ _ APP Decode_Len);
      clear LEN;clear APP;clear Decode_Len;
      intros [? [? [? [l2fact lfact]]] ];
      rewrite  l2fact in *;clear l2fact;
      rewrite lfact in *;clear lfact;
      (* unfold all write read function *)
      autounfold with bitfields in *;
      (* adhoc: destruct Byte 0 , may fail*)
      try destruct_const_byte_rewrite 0%Z;
    (* adhoc: common prefix is one byte *)
      repeat rewrite bytes_to_bits_correct in * by auto;
      simpl in H;
      (* solve char_to_bool ,simpl may stuck!*)
      (* reg_op may not be const! *)
      cbn [proj1_sig];
      repeat rewrite bytes_to_bits_correct by auto;
      unfold char_to_bool in *;
      simpl;
      rewrite H;
      clear H;
      cbn [bind]      
    | _ =>
      idtac "solve_Eaddr_decode error: common prefix?"
    end.

Ltac solve_zero_len_list:=
    match goal with
    | [H:length ?x=0 |- context G [?x]] =>
      apply length_zero_iff_nil in H;
      subst x;
      rewrite app_nil_r
    end.



(*Ltac for enc consistency*)
Ltac simpl_branch_encode HIN BPfact Enc Orth:=
  match goal with 
  | [H:?a ?code = true,
     HInst: Enc _ _ = OK _ |-
     context G [(if ?b ?code then _ else _ ) = _ ]] =>
      assert(HFalse: b code = false);[
        eapply Orth;[apply HIN | eapply HInst | apply bpt_neq_sym;apply BPfact]
     |];
    rewrite HFalse;
    clear HFalse
  end.


Ltac simpl_branch_encode_last :=
  match goal with
  | [H:?a ?code  = true |-
     context G [(if ?a ?code then _ else _ ) = _ ]]
    => rewrite H
  end.

Ltac simpl_branch_encode_instr HIN BPfact Enc Orth:=
  match goal with 
  | [H:?a ?code = true,
     HInst: Enc _ = OK _ |-
     context G [(if ?b ?code then _ else _ ) = _ ]] =>
      assert(HFalse: b code = false);[
        eapply Orth;[apply HIN | eapply HInst | apply bpt_neq_sym;apply BPfact]
     |];
    rewrite HFalse;
    clear HFalse
  end.

Ltac destruct_exists H:=
  match type of H with
  |exists _,_ =>
   destruct H as [? H];destruct_exists H
  |_ =>idtac
  end.

Ltac solve_preserve_klass Enc Preserve:=
  let HXEq := fresh "HXEq" in 
  match goal with
  |[H: Enc _ [_;_;_;_;_;_;_;_] = OK _ |-  _]
   => generalize(Preserve _ _ _ _ _ _ _ _ _ _ H);
     intros HXEq;
     destruct_exists HXEq;
     subst 
  end.


Ltac solve_klass Enc Consistency :=
  match goal with
  | HEv:Enc _ _ = _ |- _ => autounfold with * in HEv;simpl in HEv; erewrite Consistency; eauto; cbn[bind2]
  end.


 Ltac destruct_uncare_bit:=
    match goal with
    |[|- context G[if ?b then _ else _]]=>
     destruct b;destruct_uncare_bit
    |_ => idtac
    end.

Ltac destruct_neq_list:=
      match goal with
      | [H:[?b1;?b2] <> _ |- _] =>
        unfold char_to_bool in H;simpl in H;
        destruct b1;destruct b2;try congruence;
        clear H
      | [H:[?b1;?b2;?b3] <> _ |- _] =>        
        unfold char_to_bool in H;simpl in H;
        destruct b1;destruct b2;destruct b3;try congruence;
        clear H
      | _ => idtac                                         
      end. 


Ltac rewrite_const_byte_in_goal:=
  match goal with
  |[|- context G[Byte.repr ?n]]=>
   destruct_const_byte_rewrite n
  |_ =>idtac
  end.

Ltac destruct_list_in_Enc H:=
  match goal with
  |[x:list bool |- _]=>
   match goal with
   | [Len:(length x = ?n) |- _]=>
     match type of H with
     |context G [x] =>
      destr_list x
     |_=>idtac
     end
   |_=>idtac "no len fact"
   end
  |_=>idtac       
  end.

Ltac rewrite_const_byte_in_hypo H:=
  match type of H with
  |context G[Byte.repr ?n]=>
   destruct_const_byte_rewrite n
  end.

Ltac destr_builtin_rec Write:=
  match Write with
  |(?write ?b ?x)=>
   try destr_list x;
   destr_builtin_rec b
  |_=>idtac
  end.

Ltac simpl_klass_encode H :=
      match type of H with
      |(?enc _ ?inb = OK _) =>
       repeat rewrite_const_byte_in_hypo H;
       destr_builtin_rec inb;
       autounfold with bitfields in H; cbn[proj1_sig] in H;
       repeat rewrite bytes_to_bits_cons_correct in H by auto;
       unfold char_to_bool in H; simpl in H
      |_ =>idtac "simpl_klass_encode error"       
      end.

Ltac simpl_imm_encode H:=
  repeat destruct_list_in_Enc H;
  cbn [proj1_sig] in H;
  simpl in H;
  monadInv H.

Ltac solve_klass_ret_nil H Len:=
  match type of H with
    |?enc _ _ = OK ?x =>
    match goal with
    |[N:?x ++ ?y =[] |- _]=>
     apply app_eq_nil in N;
     destruct N;subst;
     apply Len in H;
     simpl in H;
     lia
    |[N:?x = [] |- _]=>
     subst;
     apply Len in H;
     simpl in H;
     lia
    |_ =>
     apply Len in H;
     simpl in H;
     try lia
    end
  end.

