(** * The semantics of relocatable program using only the symbol table *)

(** The key feature of this semantics: it uses mappings from the ids
    of global symbols to memory locations in deciding their memory
    addresses. These mappings are caculated by using the symbol table.
    *)

Require Import Coqlib Maps AST Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgram Globalenvs.
Require Import Locations Stacklayout Conventions.
Require Import Linking Errors.
Require Import LocalLib.
Require Import RelocProgGlobalenvs.

Remark in_norepet_unique_r:
  forall T (gl: list (ident * T)) id g,
  In (id, g) gl -> list_norepet (map fst gl) ->
  exists gl1 gl2, gl = gl1 ++ (id, g) :: gl2 /\ ~In id (map fst gl2).
Proof.
  induction gl as [|[id1 g1] gl]; simpl; intros.
  contradiction.
  inv H0. destruct H.
  inv H. exists nil, gl. auto.
  exploit IHgl; eauto. intros (gl1 & gl2 & X & Y).
  exists ((id1, g1) :: gl1), gl2; split;auto. rewrite X; auto.
Qed.

Section WITH_INSTR_SIZE.
  Variable instr_size : instruction -> Z.
  Let exec_instr:= exec_instr instr_size.
  
(** Small step semantics *)

  
(** Initialization of the global environment *)
Definition gen_global (id:ident) (e:symbentry) : (block*ptrofs) :=
  match e.(symbentry_secindex) with
  | secindex_normal sec =>
    (Global sec, Ptrofs.repr e.(symbentry_value))
  | _ =>
    (Global id, Ptrofs.zero)
  end.

Definition gen_symb_map (symbtbl: symbtable) : PTree.t (block * ptrofs) :=
  PTree.map gen_global symbtbl.


Definition acc_instr_map r (i:instruction) :=
  let '(ofs, map) := r in
  let map' := fun o => if Ptrofs.eq_dec ofs o then Some i else (map o) in
  let ofs' := Ptrofs.add ofs (Ptrofs.repr (instr_size i)) in
  (ofs', map').

Definition gen_instr_map (c:code) :=
  let '(_, map) := fold_left acc_instr_map c (Ptrofs.zero, fun o => None) in
  map.

Definition acc_code_map {D: Type} r (id:ident) (sec:RelocProg.section instruction D) :=
  match sec with
  | sec_text c =>
    NMap.set _ (Global id) (gen_instr_map c) r
  | _ => r
  end.

Definition gen_code_map {D: Type} (sectbl: RelocProg.sectable instruction D) :=
  PTree.fold acc_code_map sectbl (NMap.init _ (fun o => None)).

Definition acc_extfuns (idg: ident * gdef) extfuns :=
  let '(id, gdef) := idg in
  match gdef with
  | Gfun (External ef) => NMap.set  _ (Global id) (Some ef) extfuns
  | _ => extfuns
  end.

Definition gen_extfuns (idgs: list (ident * gdef)) :=
  fold_right acc_extfuns (NMap.init _ None) idgs.

Lemma PTree_Properteis_of_list_get_extfuns : forall defs i f,
    list_norepet (map fst defs) ->
    (PTree_Properties.of_list defs) ! i = (Some (Gfun (External f))) ->
    (gen_extfuns defs) (Global i) = Some f.
Proof.
  induction defs as [|def defs].
  - cbn. intros. rewrite PTree.gempty in H0. congruence.
  - intros i f NORPT OF. destruct def as (id, def).
    inv NORPT.
    destruct (ident_eq id i).
    + subst. erewrite PTree_Properties_of_list_cons in OF; auto.
      inv OF. cbn. rewrite NMap.gss. auto.
    + erewrite PTree_Properties_of_list_tail in OF; eauto.
      cbn. repeat (destr; eauto; subst).
      erewrite NMap.gso;auto.
      unfold not. intros. inv H;congruence.
Qed.

Definition globalenv {D: Type} (p: RelocProg.program fundef unit instruction D) : Genv.t :=
  let symbmap := gen_symb_map (prog_symbtable p) in
  let imap := gen_code_map (prog_sectable p) in
  let extfuns := gen_extfuns p.(prog_defs) in
  Genv.mkgenv symbmap extfuns imap p.(prog_senv).

Lemma gen_instr_map_inv_aux: forall n c ofs i ofs1 m1,
    length c = n ->
    fold_left acc_instr_map c
              (Ptrofs.zero, fun _ : ptrofs => None) = (ofs1,m1) ->
    m1 ofs = Some i ->
    In i c.
Proof.
  induction n;intros.
  rewrite length_zero_iff_nil in H. subst.
  simpl in H0. inv H0.  inv H1.
  
  exploit LocalLib.length_S_inv;eauto.
  intros (l' & a1 & A1 & B1). subst.
  clear H.
  rewrite fold_left_app in H0. simpl in H0.
  destruct ((fold_left acc_instr_map l'
            (Ptrofs.zero, fun _ : ptrofs => None))) eqn: FOLD.
  unfold acc_instr_map in H0 at 1. inv H0.
  destr_in H1.
  + inv H1. apply in_app.
    right. constructor. auto.
  +  apply in_app. left. eapply IHn;eauto.
Qed.

Lemma gen_instr_map_inv: forall c ofs i,
    gen_instr_map c ofs = Some i ->
    In i c.
Proof.
  unfold gen_instr_map. intros.
  destruct (fold_left acc_instr_map c (Ptrofs.zero, fun _ : ptrofs => None)) eqn: FOLD.
  eapply gen_instr_map_inv_aux;eauto.
Qed.


(* code map = code *)
Lemma gen_code_map_inv: forall D (sectbl : RelocProg.sectable instruction D) b ofs i,
    (gen_code_map sectbl) b ofs = Some i ->
    (exists id c, b = Global id /\ sectbl ! id = Some (sec_text c) /\ In i c).
Proof.
  unfold gen_code_map. intros.
  rewrite PTree.fold_spec in H.
  assert (exists id c, b = Global id /\ In (id, sec_text c) (PTree.elements sectbl) /\ In i c).
  { set (l:= (PTree.elements sectbl)) in *.
    generalize H.
    generalize l i ofs b.
    clear H l i ofs b. clear sectbl.
    intro l.
    assert (LEN: exists n, length l = n).
    { induction l. exists O. auto.
      destruct IHl.
      eexists. simpl. auto. }

    destruct LEN. generalize x l H.
    clear H x l.
    induction x;intros.
    rewrite length_zero_iff_nil in H. subst.
    simpl in H0. rewrite NMap.gi in H0. inv H0.

    exploit LocalLib.length_S_inv;eauto.
    intros (l' & a1 & A1 & B1). subst.
    clear H.
    rewrite fold_left_app in H0.
    simpl in H0. destruct a1. simpl in *.
    destruct (eq_block (Global p) b);subst.
    - destruct s;simpl in H0.
      + rewrite NMap.gss in H0.
        exists p, code. split;eauto.
        rewrite in_app_iff. split. right. constructor.
        auto. eapply gen_instr_map_inv. eauto.
      + eapply IHx in H0;eauto.
        destruct H0 as (id & c & P1 & P2 & P3).
        inv P1. exists id,c.
        split;auto. split;auto.
        apply in_app.
        left. auto.
      + eapply IHx in H0;eauto.
        destruct H0 as (id & c & P1 & P2 & P3).
        inv P1. exists id,c.
        split;auto. split;auto.
        apply in_app.
        left. auto.
    - destruct s;simpl in H0.
      + rewrite NMap.gso in H0;auto.
        eapply IHx in H0;eauto.
        destruct H0 as (id & c & P1 & P2 & P3).
        inv P1. exists id,c.
        split;auto. split;auto.
        apply in_app.
        left. auto.
      + eapply IHx in H0;eauto.
        destruct H0 as (id & c & P1 & P2 & P3).
        inv P1. exists id,c.
        split;auto. split;auto.
        apply in_app.
        left. auto.
      + eapply IHx in H0;eauto.
        destruct H0 as (id & c & P1 & P2 & P3).
        inv P1. exists id,c.
        split;auto. split;auto.
        apply in_app.
        left. auto.   }
  destruct H0 as (id & c & P1 & P2 & P3).
  exists id,c. split;auto. split;auto.
  apply PTree.elements_complete.
  auto.
Qed.

        
(** Initialization of memory *)
Section WITHGE1.

Variable ge:Genv.t.

Definition store_init_data (m: mem) (b: block) (p: Z) (id: init_data) : option mem :=
  match id with
  | Init_int8 n => Mem.store Mint8unsigned m b p (Vint n)
  | Init_int16 n => Mem.store Mint16unsigned m b p (Vint n)
  | Init_int32 n => Mem.store Mint32 m b p (Vint n)
  | Init_int64 n => Mem.store Mint64 m b p (Vlong n)
  | Init_float32 n => Mem.store Mfloat32 m b p (Vsingle n)
  | Init_float64 n => Mem.store Mfloat64 m b p (Vfloat n)
  | Init_addrof gloc ofs =>
    (* match Genv.find_symbol ge gloc with *)
    (* | None => None *)
    (* | Some (b',ofs') => Mem.store Mptr m b p (Vptr b' (Ptrofs.add ofs ofs')) *)
    (* end       *)
    Mem.store Mptr m b p (Genv.symbol_address ge gloc ofs)
  (* store zero to common data, which simplify the relocbingenproof, but make symbtablegenproof harder *)
  | Init_space n => store_zeros m b p (Z.max n 0)
  end.

Fixpoint store_init_data_list (m: mem) (b: block) (p: Z) (idl: list init_data)
                              {struct idl}: option mem :=
  match idl with
  | nil => Some m
  | id :: idl' =>
      match store_init_data m b p id with
      | None => None
      | Some m' => store_init_data_list m' b (p + init_data_size id) idl'
      end
  end.

Definition alloc_external_comm_symbol (r: option mem) (id: ident) (e:symbentry): option mem :=
  match r with
  | None => None
  | Some m =>
  match symbentry_type e with
  | symb_notype => None
  (* impossible *)
  (* match symbentry_secindex e with *)
    (* | secindex_undef => *)
    (*   let (m1, b) := Mem.alloc_glob id m 0 0 in Some m1 *)
    (* | _ => None *)
    (* end *)
  | symb_func =>
    match symbentry_secindex e with
    | secindex_undef =>
      let (m1, b) := Mem.alloc_glob id m 0 1 in
      Mem.drop_perm m1 b 0 1 Nonempty
    | secindex_comm =>
      None (**r Impossible *)
    | secindex_normal _ => Some m
    end
  | symb_data =>
    match symbentry_secindex e with
    | secindex_undef =>
      (* let sz := symbentry_size e in *)
      let (m1, b) := Mem.alloc_glob id m 0 1 in
      match store_zeros m1 b 0 1 with
      | None => None
      | Some m2 =>
        Mem.drop_perm m2 b 0 1 Nonempty
      end
    | secindex_comm =>
      let sz := Z.max (symbentry_size e) 0 in
      let (m1, b) := Mem.alloc_glob id m 0 sz in
      match store_zeros m1 b 0 sz with
      | None => None
      | Some m2 =>
       (* writable for common symbol *)
        Mem.drop_perm m2 b 0 sz Writable
      end        
    | secindex_normal _ => Some m
    end
  end
end.

Definition alloc_external_symbols (m: mem) (t: symbtable) : option mem :=
  PTree.fold alloc_external_comm_symbol t (Some m).


Definition alloc_section (r: option mem) (id: ident) (sec: section) : option mem :=
  match r with
  | None => None
  | Some m =>
    let sz := sec_size instr_size sec in
    match sec with
      | sec_rwdata init =>
        let '(m1, b) := Mem.alloc_glob id m 0 sz in
        match store_zeros m1 b 0 sz with
        | None => None
        | Some m2 =>
          match store_init_data_list m2 b 0 init with
          | None => None
          | Some m3 => Mem.drop_perm m3 b 0 sz Writable
          end       
        end
      | sec_rodata init =>
        let '(m1, b) := Mem.alloc_glob id m 0 sz in
        match store_zeros m1 b 0 sz with
        | None => None
        | Some m2 =>
          match store_init_data_list m2 b 0 init with
          | None => None
          | Some m3 => Mem.drop_perm m3 b 0 sz Readable
          end
        end
      | sec_text code =>        
        let (m1, b) := Mem.alloc_glob id m 0 (Z.max sz 1) in
        Mem.drop_perm m1 b 0 (Z.max sz 1 )Nonempty
    end
  end.

Definition alloc_sections (sectbl: sectable) (m:mem) :option mem :=
  PTree.fold alloc_section sectbl (Some m).

(** init data to bytes *)
Definition bytes_of_init_data (i: init_data): list memval :=
  match i with
  | Init_int8 n => inj_bytes (encode_int 1%nat (Int.unsigned n))
  | Init_int16 n => inj_bytes (encode_int 2%nat (Int.unsigned n))
  | Init_int32 n => inj_bytes (encode_int 4%nat (Int.unsigned n))
  | Init_int64 n => inj_bytes (encode_int 8%nat (Int64.unsigned n))
  | Init_float32 n => inj_bytes (encode_int 4%nat (Int.unsigned (Float32.to_bits n)))
  | Init_float64 n => inj_bytes (encode_int 8%nat (Int64.unsigned (Float.to_bits n)))
  | Init_space n => list_repeat (Z.to_nat n) (Byte Byte.zero)
  | Init_addrof id ofs =>
      match Genv.find_symbol ge id with
      | Some (b,ofs') => inj_value (if Archi.ptr64 then Q64 else Q32) (Vptr b (Ptrofs.add ofs ofs'))
      | None   => list_repeat (if Archi.ptr64 then 8%nat else 4%nat) Undef
      end
  end.

Fixpoint bytes_of_init_data_list (il: list init_data): list memval :=
  match il with
  | nil => nil
  | i :: il => bytes_of_init_data i ++ bytes_of_init_data_list il
  end.

(** load_store_init_data *)
Fixpoint load_store_init_data (m: mem) (b: block) (p: Z) (il: list init_data) {struct il} : Prop :=
  match il with
  | nil => True
  | Init_int8 n :: il' =>
      Mem.load Mint8unsigned m b p = Some(Vint(Int.zero_ext 8 n))
      /\ load_store_init_data m b (p + 1) il'
  | Init_int16 n :: il' =>
      Mem.load Mint16unsigned m b p = Some(Vint(Int.zero_ext 16 n))
      /\ load_store_init_data m b (p + 2) il'
  | Init_int32 n :: il' =>
      Mem.load Mint32 m b p = Some(Vint n)
      /\ load_store_init_data m b (p + 4) il'
  | Init_int64 n :: il' =>
      Mem.load Mint64 m b p = Some(Vlong n)
      /\ load_store_init_data m b (p + 8) il'
  | Init_float32 n :: il' =>
      Mem.load Mfloat32 m b p = Some(Vsingle n)
      /\ load_store_init_data m b (p + 4) il'
  | Init_float64 n :: il' =>
      Mem.load Mfloat64 m b p = Some(Vfloat n)
      /\ load_store_init_data m b (p + 8) il'
  | Init_addrof symb ofs :: il' =>
      ((exists b' ofs', Genv.find_symbol ge symb = Some (b',ofs') /\ Mem.load Mptr m b p = Some(Vptr b' (Ptrofs.add ofs ofs'))) \/ (Genv.find_symbol ge symb = None /\ Mem.load Mptr m b p = Some Vundef))
      /\ load_store_init_data m b (p + size_chunk Mptr) il'
  | Init_space n :: il' =>
      Globalenvs.Genv.read_as_zero m b p (Z.max n 0)
      /\ load_store_init_data m b (p + Z.max n 0) il'
  end.



(* unchanged properties *)

Remark store_init_data_unchanged:
  forall (P: block -> Z -> Prop) b i m p m',
  store_init_data m b p i = Some m' ->
  (forall ofs, p <= ofs < p + init_data_size i -> ~ P b ofs) ->
  Mem.unchanged_on P m m'.
Proof.
  intros. destruct i;simpl in *.
  1-7 :try (eapply Mem.store_unchanged_on; eauto; fail).  
  eapply Genv.store_zeros_unchanged;eauto.
  (* Mptr: auto would simplify ptr.64 and I don't know how to solve it (Opaque dose not work) *)
  eapply Mem.store_unchanged_on. eauto.
  unfold Mptr. destruct Archi.ptr64;simpl;auto.
Qed.

Remark store_init_data_list_unchanged:
  forall (P: block -> Z -> Prop) b il m p m',
  store_init_data_list m b p il = Some m' ->
  (forall ofs, p <= ofs -> ~ P b ofs) ->
  Mem.unchanged_on P m m'.
Proof.
  induction il; simpl; intros.
- inv H. apply Mem.unchanged_on_refl.
- destruct (store_init_data m b p a) as [m1|] eqn:?; try congruence.
  apply Mem.unchanged_on_trans with m1.
  eapply store_init_data_unchanged; eauto. intros; apply H0; tauto.
  eapply IHil; eauto. intros; apply H0. generalize (init_data_size_pos a); lia.
Qed.



Lemma store_init_data_loadbytes:
  forall m b p i m',
  store_init_data m b p i = Some m' ->
  Mem.loadbytes m' b p (init_data_size i) = Some (bytes_of_init_data i).
Proof.
  intros; destruct i; simpl in H; try apply (Mem.loadbytes_store_same _ _ _ _ _ _ H).
  -  simpl.
     assert (EQ: Z.of_nat (Z.to_nat z) = Z.max z 0).
     { destruct (zle 0 z). rewrite Z2Nat.id; extlia. destruct z; try discriminate. simpl. extlia. }
     rewrite <- EQ.
     eapply Genv.store_zeros_loadbytes in H.
     apply H. lia. simpl. lia.
- rewrite Genv.init_data_size_addrof. simpl.
  unfold Genv.symbol_address in H.
  destruct (Genv.find_symbol ge i) as [b'|]; try discriminate.
  destruct b'.
  rewrite (Mem.loadbytes_store_same _ _ _ _ _ _ H).
  unfold encode_val, Mptr; destruct Archi.ptr64; reflexivity.
  
  rewrite (Mem.loadbytes_store_same _ _ _ _ _ _ H).
  unfold encode_val,Mptr. destruct Archi.ptr64;auto.
Qed.

Lemma store_init_data_list_loadbytes:
  forall b il m p m',
  store_init_data_list m b p il = Some m' ->
  Mem.loadbytes m' b p (init_data_list_size il) = Some (bytes_of_init_data_list il).
Proof.
  induction il as [ | i1 il]; simpl; intros.
- apply Mem.loadbytes_empty. lia.
- generalize (init_data_size_pos i1) (init_data_list_size_pos il); intros P1 PL.
  destruct (store_init_data m b p i1) as [m1|] eqn:S; try discriminate.
  apply Mem.loadbytes_concat.
  eapply Mem.loadbytes_unchanged_on with (P := fun b1 ofs1 => ofs1 < p + init_data_size i1).
  eapply store_init_data_list_unchanged; eauto.
  intros; lia.
  intros; lia.
  eapply store_init_data_loadbytes; eauto.
  (* red; intros; apply H0. lia. lia. *)
  apply IHil with m1; auto.
  lia. lia.
  (* red; intros. *)
  (* eapply Mem.loadbytes_unchanged_on with (P := fun b1 ofs1 => p + init_data_size i1 <= ofs1). *)
  (* eapply store_init_data_unchanged; eauto. *)
  (* intros; lia. *)
  (* intros; lia. *)
  (* apply H0. lia. lia. *)
  (* auto. auto. *)
Qed.


Lemma store_init_data_list_charact:
  forall b il m p m',
  store_init_data_list m b p il = Some m' ->
  (* Genv.read_as_zero m b p (init_data_list_size il) -> *)
  load_store_init_data m' b p il.
Proof.
  assert (A: forall chunk v m b p m1 il m',
    Mem.store chunk m b p v = Some m1 ->
    store_init_data_list m1 b (p + size_chunk chunk) il = Some m' ->
    Mem.load chunk m' b p = Some(Val.load_result chunk v)).
  {
    intros.
    eapply Mem.load_unchanged_on with (P := fun b' ofs' => ofs' < p + size_chunk chunk).
    eapply store_init_data_list_unchanged; eauto. intros; lia.
    intros; tauto.
    eapply Mem.load_store_same; eauto.
  }  induction il; simpl.
- auto.
- intros. destruct (store_init_data m b p a) as [m1|] eqn:?; try congruence.
  exploit IHil; eauto.
  (* set (P := fun (b': block) ofs' => p + init_data_size a <= ofs'). *)
  (* apply Genv.read_as_zero_unchanged with (m := m) (P := P). *)
  (* (* red; *) intros; (* apply H0; *) auto. (* generalize (init_data_size_pos a); lia. lia. *) *)
  (* eapply store_init_data_unchanged with (P := P); eauto. *)
  (* intros; unfold P. lia. *)
  (* intros; unfold P. lia. *)
  (* intro D. *)
  intros.
  destruct a; simpl in Heqo.
+ split; auto. eapply (A Mint8unsigned (Vint i)); eauto.
+ split; auto. eapply (A Mint16unsigned (Vint i)); eauto.
+ split; auto. eapply (A Mint32 (Vint i)); eauto.
+ split; auto. eapply (A Mint64 (Vlong i)); eauto.
+ split; auto. eapply (A Mfloat32 (Vsingle f)); eauto.
+ split; auto. eapply (A Mfloat64 (Vfloat f)); eauto.
+ split; auto.
  set (P := fun (b': block) ofs' => ofs' < p + init_data_size (Init_space z)).
  (* inv Heqo. *) apply Genv.read_as_zero_unchanged with (m := m1) (P := P).
  eapply Genv.store_zeros_read_as_zero;eauto.
  
  (* red; intros. apply H0; auto. simpl. generalize (init_data_list_size_pos il); extlia. *)
  eapply store_init_data_list_unchanged; eauto.
  intros; unfold P. lia.
  intros; unfold P. simpl; extlia.
+ rewrite Genv.init_data_size_addrof in *.
  split; auto.

  unfold Genv.symbol_address in *.
  
  destruct (Genv.find_symbol ge i); try congruence.
  destruct p0.
  
  left. exists b0,i1; split; auto.
  transitivity (Some (Val.load_result Mptr (Vptr b0 (Ptrofs.add i0 i1)))).
  eapply (A Mptr (Vptr b0 (Ptrofs.add i0 i1))); eauto.
  unfold Val.load_result, Mptr; destruct Archi.ptr64; auto.
  
  right. split;auto.
  transitivity (Some (Val.load_result Mptr Vundef)).
  eapply (A Mptr Vundef); eauto.
  unfold Val.load_result, Mptr; destruct Archi.ptr64; auto.
Qed.


Remark load_store_init_data_invariant:
  forall m m' b,
  (forall chunk ofs, Mem.load chunk m' b ofs = Mem.load chunk m b ofs) ->
  forall il p,
  load_store_init_data m b p il -> load_store_init_data m' b p il.
Proof.
  induction il; intro p; simpl.
  auto.
  rewrite ! H. destruct a; intuition. red; intros; rewrite H; auto.
Qed.


End WITHGE1.
Section INITDATA.

Variable ge: Genv.t.

Remark store_init_data_perm:
  forall k prm b' q i b m p m',
  store_init_data ge m b p i = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  intros. 
  assert (forall chunk v,
          Mem.store chunk m b p v = Some m' ->
          (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm)).
    intros; split; eauto with mem.
    destruct i; simpl in H; eauto.
  eapply Genv.store_zeros_perm.
  eauto.

  (* destruct (Genv.find_symbol ge i); try discriminate. destruct p0. eauto. *)
Qed.

Remark store_init_data_list_perm:
  forall k prm b' q idl b m p m',
  store_init_data_list ge m b p idl = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  induction idl as [ | i1 idl]; simpl; intros.
- inv H; tauto.
- destruct (store_init_data ge m b p i1) as [m1|] eqn:S1; try discriminate.
  transitivity (Mem.perm m1 b' q k prm). 
  eapply store_init_data_perm; eauto.
  eapply IHidl; eauto.
Qed.

Lemma store_init_data_exists:
  forall m b p i,
    Mem.range_perm m b p (p + init_data_size i) Cur Writable ->
    (* Mem.stack_access (Mem.stack m) b p (p + init_data_size i)  -> *)
    (Genv.init_data_alignment i | p) ->
    (* (forall id ofs, i = Init_addrof id ofs -> exists b ofs', Genv.find_symbol ge id = Some (b,ofs')) -> *)
    exists m', store_init_data ge m b p i = Some m'.
Proof.
  intros. 
  assert (DFL: forall chunk v,
          init_data_size i = size_chunk chunk ->
          Genv.init_data_alignment i = align_chunk chunk ->
          exists m', Mem.store chunk m b p v = Some m').
  { intros. destruct (Mem.valid_access_store m chunk b p v) as (m' & STORE).
    split. rewrite <- H1; auto.
    rewrite  <- H2. auto.
    exists m'; auto. }
  destruct i.
  1-7: eauto.
  (* store zero *)
  simpl. eapply Genv.store_zeros_exists.
  simpl in H. auto.

  (* Mptr *)
  simpl. eapply DFL.
  unfold Mptr. simpl. destruct Archi.ptr64;auto.
  unfold Mptr. simpl. destruct Archi.ptr64;auto.
  (* simpl. exploit H1; eauto. intros (b1 & OFS & FS). rewrite FS. eapply DFL. *)
  (* unfold init_data_size, Mptr. destruct Archi.ptr64; auto. *)
  (* unfold Genv.init_data_alignment, Mptr. destruct Archi.ptr64; auto. *)                                                            
Qed.

(* SACC
Lemma store_init_data_stack_access:
  forall m b p i1 m1,
    store_init_data ge m b p i1 = Some m1 ->
    forall b' lo hi,
      stack_access (Mem.stack m1) b' lo hi <-> stack_access (Mem.stack m) b' lo hi.
Proof.
  unfold store_init_data.
  destruct i1; intros; try now (eapply Mem.store_stack_access ; eauto).
  inv H; tauto.
Qed.
*)

Lemma store_init_data_list_exists:
  forall b il m p,
  Mem.range_perm m b p (p + init_data_list_size il) Cur Writable ->
  (* stack_access (Mem.stack m) b p (p + init_data_list_size il) -> *)
  Genv.init_data_list_aligned p il ->
  (* (forall id ofs, In (Init_addrof id ofs) il -> exists b ofs', Genv.find_symbol ge id = Some (b,ofs')) -> *)
  exists m', store_init_data_list ge m b p il = Some m'.
Proof.
  induction il as [ | i1 il ]; simpl; intros.
- exists m; auto.
- destruct H0. 
  destruct (@store_init_data_exists m b p i1) as (m1 & S1); eauto.
  red; intros. apply H. generalize (init_data_list_size_pos il); lia.
  (* generalize (init_data_list_size_pos il); omega. *)
  rewrite S1.
  apply IHil; eauto.
  red; intros. erewrite <- store_init_data_perm by eauto. apply H. generalize (init_data_size_pos i1); lia.
Qed.

Remark store_init_data_load_other:
  forall b' i b m p m' chunk ofs,
  store_init_data ge m b p i = Some m' -> b <> b' ->
  (Mem.load chunk m b' ofs = Mem.load chunk m' b' ofs).
Proof.
  intros.
  assert (forall chunk' v,
          Mem.store chunk' m b p v = Some m' -> b <> b' ->
          (Mem.load chunk m b' ofs = Mem.load chunk m' b' ofs)).
   { intros. eapply Mem.load_store_other in H1; eauto. }
   destruct i. 1-7:  simpl in H; eauto.
   2: simpl in H; eauto.

   eapply Genv.store_zeros_load_other;eauto.
   
  (* destruct (Genv.find_symbol ge i); try discriminate. destruct p0. eauto. *)
Qed.

Remark store_init_data_list_load_other:
  forall b' idl b m p m' chunk ofs,
  store_init_data_list ge m b p idl = Some m' -> b <> b' ->
  (Mem.load chunk m b' ofs = Mem.load chunk m' b' ofs).
Proof.
  induction idl as [ | i1 idl]; simpl; intros.
- inv H; tauto.
- destruct (store_init_data ge m b p i1) as [m1|] eqn:S1; try discriminate.
  transitivity (Mem.load chunk m1 b' ofs).
  eapply store_init_data_load_other; eauto.
  eapply IHidl; eauto.
Qed.

Remark store_init_data_loadbytes_other:
  forall b' i b m p m' lo hi,
  store_init_data ge m b p i = Some m' -> b <> b' ->
  (Mem.loadbytes m b' lo hi = Mem.loadbytes m' b' lo hi).
Proof.
  intros.
  assert (forall chunk' v,
          Mem.store chunk' m b p v = Some m' -> b <> b' ->
          (Mem.loadbytes m b' lo hi = Mem.loadbytes m' b' lo hi)).
  { intros. eapply Mem.loadbytes_store_other in H1; eauto. }
  destruct i. 1-7:  simpl in H; eauto.
   2: simpl in H; eauto
.
   eapply Genv.store_zeros_loadbytes_other;eauto.
   (* destruct (Genv.find_symbol ge i); try discriminate. destruct p0. eauto.    *)
Qed.

Remark store_init_data_list_loadbytes_other:
  forall b' idl b m p m' lo hi,
  store_init_data_list ge m b p idl = Some m' -> b <> b' ->
  (Mem.loadbytes m b' lo hi= Mem.loadbytes m' b' lo hi).
Proof.
  induction idl as [ | i1 idl]; simpl; intros.
- inv H; tauto.
- destruct (store_init_data ge m b p i1) as [m1|] eqn:S1; try discriminate.
  transitivity (Mem.loadbytes m1 b' lo hi).
  eapply store_init_data_loadbytes_other; eauto.
  eapply IHidl; eauto.
Qed.

End INITDATA.


(** globals_initialized *)
Definition globals_initialized (ge: Genv.t) (prog: program) (m:mem):=
  forall id b ofs0,
    (* b = Global id -> *)
    Genv.find_symbol ge id = Some (b,ofs0) ->
    let ofs0 := Ptrofs.unsigned ofs0 in
    match prog.(prog_sectable) ! id with
    | Some sec =>
      (* ofs0 = 0 /\ : required if supporting section merging *)
      match sec with
      | sec_text code =>
        Mem.perm m b ofs0 Cur Nonempty /\
        let sz := Z.max (code_size instr_size code) 1 in
        (forall ofs k p, Mem.perm m b (ofs0+ofs) k p -> 0 <= ofs < sz /\ p = Nonempty)
      | sec_rodata data =>        
        let sz := (init_data_list_size data) in
        Mem.range_perm m b ofs0 sz Cur Readable /\ (forall ofs k p, Mem.perm m b (ofs0+ofs) k p -> 0 <= ofs < sz /\ perm_order Readable p)
        /\ load_store_init_data ge m b ofs0 data
        /\ Mem.loadbytes m b ofs0 sz = Some (bytes_of_init_data_list ge data)
      | sec_rwdata data =>
        let sz := (init_data_list_size data) in
        Mem.range_perm m b ofs0 sz Cur Writable /\ (forall ofs k p, Mem.perm m b (ofs0+ofs) k p -> 0 <= ofs < sz /\ perm_order Writable p)
        /\ load_store_init_data ge m b ofs0 data
        /\ Mem.loadbytes m b ofs0 sz = Some (bytes_of_init_data_list ge data)
      end
    | None =>
      (* common symbol or external function *)
      match prog.(prog_symbtable) ! id with
      | Some e =>
        match e.(symbentry_type),e.(symbentry_secindex) with
        | symb_func,secindex_undef =>
          Mem.perm m b 0 Cur Nonempty /\
          (forall ofs k p, Mem.perm m b ofs k p -> ofs = 0 /\ p = Nonempty)
        | symb_data,secindex_comm =>
          let sz := e.(symbentry_size) in
          let data := Init_space sz :: nil in
          let sz' := Z.max sz 0 in
          Mem.range_perm m b 0 sz' Cur Writable /\ (forall ofs k p, Mem.perm m b ofs k p -> 0 <= ofs < sz' /\ perm_order Writable p)
          /\ load_store_init_data ge m b 0 data
          /\ Mem.loadbytes m b 0 sz' = Some (bytes_of_init_data_list ge data)
        | symb_data,secindex_undef =>
          Mem.perm m b 0 Cur Nonempty /\
          (forall ofs k p, Mem.perm m b ofs k p -> ofs = 0 /\ p = Nonempty)
        (* when id resides in a location of a section *)
        (* if id <> i then in secidx is allowed: the following cases are required *)
        | _,_ => False
        end
      | _ => False
      end
    end.

Definition init_mem (p: program) :=
  let ge := globalenv p in
  match alloc_sections ge p.(prog_sectable) Mem.empty with
  | Some m1 =>
    alloc_external_symbols m1 p.(prog_symbtable)
  | None => None
  end.

Definition well_formed_symbtbl (sectbl:sectable) symbtbl:=
  forall id e,
    symbtbl ! id = Some e ->
    match symbentry_secindex e with
    | secindex_normal i =>        
      symbentry_type e <> symb_notype
      /\ i = id                  (* does not support sections merging *)
      /\ (exists sec, sectbl ! i = Some sec
                /\ sec_size instr_size sec = symbentry_size e
                /\ symbentry_value e = 0)
                (* separation: it should be more complicate. If include the restriction list below, the globals_initialized should be enhanced *)
                (* (i <> id -> (0 <= symbentry_value e + symbentry_size e <= sec_size instr_size sec))) *)
    | secindex_comm =>
      symbentry_type e = symb_data /\ sectbl ! id = None
    | secindex_undef =>
      symbentry_type e <> symb_notype /\ sectbl ! id = None
    end.

Definition globals_initialized_sections ge m b sec :=
  match sec with
  | sec_text code =>
    Mem.perm m b 0 Cur Nonempty /\
    (let sz := Z.max (code_size instr_size code) 1 in
     forall (ofs : Z) (k : perm_kind) (p : permission), Mem.perm m b ofs k p -> 0 <= ofs < sz /\ p = Nonempty)
  | sec_rwdata data =>
    let sz := init_data_list_size data in
    Mem.range_perm m b 0 sz Cur Writable /\
    (forall (ofs : Z) (k : perm_kind) (p : permission),
        Mem.perm m b ofs k p -> 0 <= ofs < sz /\ perm_order Writable p) /\
    load_store_init_data ge m b 0 data /\ Mem.loadbytes m b 0 sz = Some (bytes_of_init_data_list ge data)
  | sec_rodata data =>
    let sz := init_data_list_size data in
    Mem.range_perm m b 0 sz Cur Readable /\
    (forall (ofs : Z) (k : perm_kind) (p : permission),
        Mem.perm m b ofs k p -> 0 <= ofs < sz /\ perm_order Readable p) /\
    load_store_init_data ge m b 0 data /\ Mem.loadbytes m b 0 sz = Some (bytes_of_init_data_list ge data)
  end.                                                                       

Definition globals_initialized_external ge m b e:=
  match e.(symbentry_type),e.(symbentry_secindex) with
  | symb_func,secindex_undef =>
    Mem.perm m b 0 Cur Nonempty /\
    (forall ofs k p, Mem.perm m b ofs k p -> ofs = 0 /\ p = Nonempty)
  | symb_data,secindex_comm =>
    let sz := e.(symbentry_size) in
    let data := Init_space sz :: nil in
    let sz' := Z.max sz 0 in
    Mem.range_perm m b 0 sz' Cur Writable /\ (forall ofs k p, Mem.perm m b ofs k p -> 0 <= ofs < sz' /\ perm_order Writable p)
    /\ load_store_init_data ge m b 0 data
    /\ Mem.loadbytes m b 0 sz' = Some (bytes_of_init_data_list ge data)
  | symb_data,secindex_undef =>
    Mem.perm m b 0 Cur Nonempty /\
    (forall ofs k p, Mem.perm m b ofs k p -> ofs = 0 /\ p = Nonempty)
  | _,_ => False
  end.

(* alloc_glob dose not change the globals_initialized_sections *)
Lemma alloc_glob_pres_globals_initialized_sections: forall b b' id lo hi sec m1 m2 ge,
    globals_initialized_sections ge m1 b sec ->
    Mem.alloc_glob id m1 lo hi = (m2,b') ->
    b <> b' ->
    globals_initialized_sections ge m2 b sec.
Proof.
  unfold globals_initialized_sections.
  intros.
  exploit Mem.alloc_glob_result;eauto;intros. subst.  
  destruct sec.
  - destruct H. split. 
    + eapply Mem.perm_alloc_glob_1 in H0. eapply H0.
      eauto.
      congruence.
    + intros.
      assert (Mem.perm m1 b ofs k p).
      eapply Mem.perm_alloc_glob_1 in H0. eapply H0.
      auto.
      congruence. eapply H2 in H4.
      eauto.
  - destruct H as (P1 & P2 & P3 & P4).
    split.
    (* 1 *)
    unfold Mem.range_perm. intros.
    eapply Mem.perm_alloc_glob_1 in H0. eapply H0.
    eauto.
    congruence.
    (* 2 *)
    split.
    intros.
    assert (Mem.perm m1 b ofs k p).
    eapply Mem.perm_alloc_glob_1 in H0. eapply H0.                   
    auto.
    congruence. eapply P2 in H2.
    eauto.
    (* 3 *)
    split.
    eapply load_store_init_data_invariant.
    2: eapply P3. intros.
    eapply Mem.load_alloc_glob_unchanged;eauto.
    (* 4 *)   
    erewrite Mem.loadbytes_alloc_glob_unchanged;eauto.
    
  - destruct H as (P1 & P2 & P3 & P4).
    split.
    (* 1 *)
    unfold Mem.range_perm. intros.
    eapply Mem.perm_alloc_glob_1 in H0. eapply H0.
    eauto.
    congruence.
    (* 2 *)
    split.
    intros.
    assert (Mem.perm m1 b ofs k p).
    eapply Mem.perm_alloc_glob_1 in H0. eapply H0.                   
    auto.
    congruence. eapply P2 in H2.
    eauto.
    (* 3 *)
    split.
    eapply load_store_init_data_invariant.
    2: eapply P3. intros.
    eapply Mem.load_alloc_glob_unchanged;eauto.
    (* 4 *)   
    erewrite Mem.loadbytes_alloc_glob_unchanged;eauto.
Qed.


Lemma alloc_glob_pres_globals_initialized_external: forall b b' id lo hi e m1 m2 ge,
    globals_initialized_external ge m1 b e ->
    Mem.alloc_glob id m1 lo hi = (m2,b') ->
    b <> b' ->
    globals_initialized_external ge m2 b e.
Proof.
  unfold globals_initialized_external.
  intros.
  exploit Mem.alloc_glob_result;eauto;intros. subst.  
  destr.
  - destr.
    destruct H. split.
    + eapply Mem.perm_alloc_glob_1 in H0. eapply H0.
      eauto.
      congruence.
    + intros.
      assert (Mem.perm m1 b ofs k p).
      eapply Mem.perm_alloc_glob_1 in H0. eapply H0.
      auto.
      congruence. eapply H2 in H4.
      eauto.
  - destr.
    + destruct H as (P1 & P2 & P3 & P4).
      split.
      (* 1 *)
      unfold Mem.range_perm. intros.
      eapply Mem.perm_alloc_glob_1 in H0. eapply H0.
      eauto.
      congruence.
      (* 2 *)
      split.
      intros.
      assert (Mem.perm m1 b ofs k p).
      eapply Mem.perm_alloc_glob_1 in H0. eapply H0.                   
      auto.
      congruence. eapply P2 in H2.
      eauto.
      (* 3 *)
      split.
      eapply load_store_init_data_invariant.
      2: eapply P3. intros.
      eapply Mem.load_alloc_glob_unchanged;eauto.
      (* 4 *)   
      erewrite Mem.loadbytes_alloc_glob_unchanged;eauto.
    + destruct H. split.
      * eapply Mem.perm_alloc_glob_1 in H0. eapply H0.
        eauto.
        congruence.
      * intros.
        assert (Mem.perm m1 b ofs k p).
        eapply Mem.perm_alloc_glob_1 in H0. eapply H0.
        auto.
        congruence. eapply H2 in H4.
        eauto.
Qed.


Lemma store_zeros_pres_globals_initialized_sections: forall b b' sz ofs sec m1 m2 ge,
    globals_initialized_sections ge m1 b sec ->
    store_zeros m1 b' ofs sz = Some m2 ->
    b <> b' ->
    globals_initialized_sections ge m2 b sec.
Proof.
  unfold globals_initialized_sections.
  intros.
  destruct sec.
  - destruct H.
    split.
    + erewrite <- Genv.store_zeros_perm;eauto.
    + intros.
      assert (Mem.perm m1 b ofs0 k p).
      eapply Genv.store_zeros_perm;eauto.
      eapply H2 in H4.
      eauto.
  - destruct H as (P1 & P2 & P3 & P4).
    split.
    (* 1 *)
    unfold Mem.range_perm in *.
    intros.
    erewrite <- Genv.store_zeros_perm;eauto. 
    (* 2 *)
    split.
    intros.
    assert (Mem.perm m1 b ofs0 k p).
    eapply Genv.store_zeros_perm;eauto.
    eapply P2 in H2.
    eauto.
    (* 3 *)
    split.
    eapply load_store_init_data_invariant.
    2: eapply P3.
    intros.
    erewrite <- (Genv.store_zeros_load_other m1);eauto.
    (* 4 *)        
    erewrite <- Genv.store_zeros_loadbytes_other;eauto.

  - destruct H as (P1 & P2 & P3 & P4).
    split.
    (* 1 *)
    unfold Mem.range_perm in *.
    intros.
    erewrite <- Genv.store_zeros_perm;eauto. 
    (* 2 *)
    split.
    intros.
    assert (Mem.perm m1 b ofs0 k p).
    eapply Genv.store_zeros_perm;eauto.
    eapply P2 in H2.
    eauto.
    (* 3 *)
    split.
    eapply load_store_init_data_invariant.
    2: eapply P3.
    intros.
    erewrite <- (Genv.store_zeros_load_other m1);eauto.
    (* 4 *)        
    erewrite <- Genv.store_zeros_loadbytes_other;eauto.
Qed.


Lemma store_zeros_pres_globals_initialized_external: forall b b' sz ofs e m1 m2 ge,
    globals_initialized_external ge m1 b e ->
    store_zeros m1 b' ofs sz = Some m2 ->
    b <> b' ->
    globals_initialized_external ge m2 b e.
Proof.
  unfold globals_initialized_external.
  intros.
  destr.
  - destr. destruct H. split.
    + erewrite <- Genv.store_zeros_perm;eauto.
    + intros.
      assert (Mem.perm m1 b ofs0 k p).
      eapply Genv.store_zeros_perm;eauto.
      eapply H2 in H4.
      eauto.
  - destr. destruct H as (P1 & P2 & P3 & P4).
    split.
    (* 1 *)
    unfold Mem.range_perm in *.
    intros.
    erewrite <- Genv.store_zeros_perm;eauto. 
    (* 2 *)
    split.
    intros.
    assert (Mem.perm m1 b ofs0 k p).
    eapply Genv.store_zeros_perm;eauto.
    eapply P2 in H2.
    eauto.
    (* 3 *)
    split.
    eapply load_store_init_data_invariant.
    2: eapply P3.
    intros.
    erewrite <- (Genv.store_zeros_load_other m1);eauto.
    (* 4 *)        
    erewrite <- Genv.store_zeros_loadbytes_other;eauto.

     destruct H. split.
    + erewrite <- Genv.store_zeros_perm;eauto.
    + intros.
      assert (Mem.perm m1 b ofs0 k p).
      eapply Genv.store_zeros_perm;eauto.
      eapply H2 in H4.
      eauto.
Qed.


Lemma drop_pres_globals_initialized_sections: forall b b' lo hi p sec m1 m2 ge,
    globals_initialized_sections ge m1 b sec ->
    Mem.drop_perm m1 b' lo hi p = Some m2 ->
    b <> b' ->
    globals_initialized_sections ge m2 b sec.
Proof.
  unfold globals_initialized_sections.
  intros.
  destruct sec.
  - destruct H. split.
    + eapply Mem.perm_drop_3;eauto.
    + intros.
      assert (Mem.perm m1 b ofs k p0).
      eapply Mem.perm_drop_4;eauto.
      eapply H2 in H4.
      eauto.
  - destruct H as (P1 & P2 & P3 & P4).
    split.
    (* 1 *)
    unfold Mem.range_perm in *.
    intros.
    eapply Mem.perm_drop_3;eauto.
    (* 2 *)
    split.
    intros.
    assert (Mem.perm m1 b ofs k p0).
    eapply Mem.perm_drop_4;eauto.
    eapply P2 in H2.
    eauto.
    (* 3 *)
    split.
    eapply load_store_init_data_invariant.
    2: eapply P3. intros.
    erewrite (Mem.load_drop m1);eauto.
    (* 4 *)
    erewrite Mem.loadbytes_drop;eauto.

- destruct H as (P1 & P2 & P3 & P4).
    split.
    (* 1 *)
    unfold Mem.range_perm in *.
    intros.
    eapply Mem.perm_drop_3;eauto.
    (* 2 *)
    split.
    intros.
    assert (Mem.perm m1 b ofs k p0).
    eapply Mem.perm_drop_4;eauto.
    eapply P2 in H2.
    eauto.
    (* 3 *)
    split.
    eapply load_store_init_data_invariant.
    2: eapply P3. intros.
    erewrite (Mem.load_drop m1);eauto.
    (* 4 *)
    erewrite Mem.loadbytes_drop;eauto.
Qed.


Lemma drop_pres_globals_initialized_external: forall b b' lo hi p e m1 m2 ge,
    globals_initialized_external ge m1 b e ->
    Mem.drop_perm m1 b' lo hi p = Some m2 ->
    b <> b' ->
    globals_initialized_external ge m2 b e.
Proof.
  unfold globals_initialized_external.
  intros.
  destr.
  - destr. destruct H. split.
    + eapply Mem.perm_drop_3;eauto.
    + intros.
      assert (Mem.perm m1 b ofs k p0).
      eapply Mem.perm_drop_4;eauto.
      eapply H2 in H4.
      eauto.
  - destr.
    destruct H as (P1 & P2 & P3 & P4).
    split.
    (* 1 *)
    unfold Mem.range_perm in *.
    intros.
    eapply Mem.perm_drop_3;eauto.
    (* 2 *)
    split.
    intros.
    assert (Mem.perm m1 b ofs k p0).
    eapply Mem.perm_drop_4;eauto.
    eapply P2 in H2.
    eauto.
    (* 3 *)
    split.
    eapply load_store_init_data_invariant.
    2: eapply P3. intros.
    erewrite (Mem.load_drop m1);eauto.
    (* 4 *)
    erewrite Mem.loadbytes_drop;eauto.
    
    destruct H. split.
    + eapply Mem.perm_drop_3;eauto.
    + intros.
      assert (Mem.perm m1 b ofs k p0).
      eapply Mem.perm_drop_4;eauto.
      eapply H2 in H4.
      eauto.
Qed.      

     
    
(* FIXME: so verbose and we should use the above lemma to simplify it *)
Lemma alloc_sections_none: forall secs ge,
    fold_left
      (fun (a : option mem) (p0 : positive * section) => alloc_section ge a (fst p0) (snd p0))
      secs None = None.
Proof.
  induction secs;simpl;auto.
Qed.

Lemma alloc_sections_pres_characterization: forall secs sec ge m0 m id ,
    ~ In id  (map fst secs) ->
    globals_initialized_sections ge m0 (Global id) sec ->
    fold_left
      (fun (a : option mem) (p0 : positive * section) => alloc_section ge a (fst p0) (snd p0))
      secs (Some m0) = Some m ->
    globals_initialized_sections ge m (Global id) sec.
Proof.
  induction secs;simpl;intros.
  inv H1. auto.
  eapply Decidable.not_or in H.
  destruct H.
  destruct a. simpl in *.
  destruct s;simpl in *.
  - destruct (Mem.alloc_glob i m0 0 (Z.max (code_size instr_size code) 1)) eqn:ALLOC.
    destruct ((Mem.drop_perm m1 b 0 (Z.max (code_size instr_size code) 1) Nonempty)) eqn:DROP.
    assert (globals_initialized_sections ge m2 (Global id) sec).
    { unfold globals_initialized_sections.
      unfold globals_initialized_sections in H0.
      destruct sec.
      - destruct H0. split.
        + eapply Mem.perm_drop_3;eauto.
          left. eapply Mem.alloc_glob_result in ALLOC.
          subst. congruence.
          eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.
          eauto.
          congruence.
        + intros.
          assert (Mem.perm m0 (Global id) ofs k p).
          eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.                   
          eapply Mem.perm_drop_4;eauto.
          congruence. eapply H3 in H5.
          eauto.
      - destruct H0 as (P1 & P2 & P3 & P4).
        split.
        (* 1 *)
        unfold Mem.range_perm in *.
        intros.
        eapply Mem.perm_drop_3;eauto.
        left. eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.
        eauto.
        congruence.
        (* 2 *)
        split.
        intros.
        assert (Mem.perm m0 (Global id) ofs k p).
        eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.                   
        eapply Mem.perm_drop_4;eauto.
        congruence. eapply P2 in H3.
        eauto.
        (* 3 *)
        split.
        eapply load_store_init_data_invariant.
        2: eapply P3. intros.
        erewrite (Mem.load_drop m1);eauto.
        erewrite Mem.load_alloc_glob_unchanged;eauto.
        congruence. left.
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        (* 4 *)
        erewrite Mem.loadbytes_drop. 2: eapply DROP.        
        erewrite Mem.loadbytes_alloc_glob_unchanged;eauto.
        congruence. left.
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
      - destruct H0 as (P1 & P2 & P3 & P4).
        split.
        (* 1 *)
        unfold Mem.range_perm in *.
        intros.
        eapply Mem.perm_drop_3;eauto.
        left. eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.
        eauto.
        congruence.
        (* 2 *)
        split.
        intros.
        assert (Mem.perm m0 (Global id) ofs k p).
        eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.                   
        eapply Mem.perm_drop_4;eauto.
        congruence. eapply P2 in H3.
        eauto.
        (* 3 *)
        split.
        eapply load_store_init_data_invariant.
        2: eapply P3. intros.
        erewrite (Mem.load_drop m1);eauto.
        erewrite Mem.load_alloc_glob_unchanged;eauto.
        congruence. left.
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        (* 4 *)
        erewrite Mem.loadbytes_drop. 2: eapply DROP.        
        erewrite Mem.loadbytes_alloc_glob_unchanged;eauto.
        congruence. left.
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence. }
    eapply IHsecs;eauto.
    rewrite alloc_sections_none in H1. congruence.

  - destruct (Mem.alloc_glob i m0 0 (init_data_list_size init)) eqn:ALLOC.
    destr_in H1.
    2: { rewrite alloc_sections_none in H1. congruence. }
    destr_in H1.
    2: { rewrite alloc_sections_none in H1. congruence. }
    destruct (Mem.drop_perm m3 b 0 (init_data_list_size init) Writable) eqn:DROP.
    2: { rewrite alloc_sections_none in H1. congruence. }    
    assert (globals_initialized_sections ge m4 (Global id) sec).
    { unfold globals_initialized_sections.
      unfold globals_initialized_sections in H0.
      destruct sec.
      - destruct H0. split.
        + eapply Mem.perm_drop_3;eauto.
          left. eapply Mem.alloc_glob_result in ALLOC.
          subst. congruence.
          erewrite <- store_init_data_list_perm. 2: eapply Heqo0.
          erewrite <- Genv.store_zeros_perm. 2: eapply Heqo.          
          eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.
          eauto.
          congruence.
        + intros.
          assert (Mem.perm m0 (Global id) ofs k p).
          eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.
          eapply Genv.store_zeros_perm;eauto.
          eapply store_init_data_list_perm;eauto.
          eapply Mem.perm_drop_4;eauto.
          congruence. eapply H3 in H5.
          eauto.
      - destruct H0 as (P1 & P2 & P3 & P4).
        split.
        (* 1 *)
        unfold Mem.range_perm in *.
        intros.
        eapply Mem.perm_drop_3;eauto.
        left. eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        erewrite <- store_init_data_list_perm. 2: eapply Heqo0.
        erewrite <- Genv.store_zeros_perm. 2: eapply Heqo.          
        eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.
        eauto.
        congruence.
        (* 2 *)
        split.
        intros.
        assert (Mem.perm m0 (Global id) ofs k p).
        eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.
        eapply Genv.store_zeros_perm;eauto.
        eapply store_init_data_list_perm;eauto.
        eapply Mem.perm_drop_4;eauto.
        congruence. eapply P2 in H3.
        eauto.
        (* 3 *)
        split.
        eapply load_store_init_data_invariant.
        2: eapply P3. intros.
        erewrite (Mem.load_drop m3);eauto.
        erewrite <- store_init_data_list_load_other.
        2: eapply Heqo0.
        erewrite <- (Genv.store_zeros_load_other m1);eauto.
        erewrite Mem.load_alloc_glob_unchanged;eauto.
        congruence.
        eapply Mem.alloc_glob_result in ALLOC. subst.
        congruence.
        eapply Mem.alloc_glob_result in ALLOC. subst.
        congruence. 
        left.
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        (* 4 *)
        erewrite Mem.loadbytes_drop. 2: eapply DROP.
        erewrite <- store_init_data_list_loadbytes_other.
        2: eapply Heqo0.
        erewrite <- Genv.store_zeros_loadbytes_other.
        2: eapply Heqo.        
        erewrite Mem.loadbytes_alloc_glob_unchanged.
        2: eapply ALLOC.
        congruence. congruence. 
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        left.
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
      - destruct H0 as (P1 & P2 & P3 & P4).
        split.
        (* 1 *)
        unfold Mem.range_perm in *.
        intros.
        eapply Mem.perm_drop_3;eauto.
        left. eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        erewrite <- store_init_data_list_perm. 2: eapply Heqo0.
        erewrite <- Genv.store_zeros_perm. 2: eapply Heqo.          
        eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.
        eauto.
        congruence.
        (* 2 *)
        split.
        intros.
        assert (Mem.perm m0 (Global id) ofs k p).
        eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.
        eapply Genv.store_zeros_perm;eauto.
        eapply store_init_data_list_perm;eauto.
        eapply Mem.perm_drop_4;eauto.
        congruence. eapply P2 in H3.
        eauto.
        (* 3 *)
        split.
        eapply load_store_init_data_invariant.
        2: eapply P3. intros.
        erewrite (Mem.load_drop m3);eauto.
        erewrite <- store_init_data_list_load_other.
        2: eapply Heqo0.
        erewrite <- (Genv.store_zeros_load_other m1);eauto.
        erewrite Mem.load_alloc_glob_unchanged;eauto.
        congruence.
        eapply Mem.alloc_glob_result in ALLOC. subst.
        congruence.
        eapply Mem.alloc_glob_result in ALLOC. subst.
        congruence. 
        left.
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        (* 4 *)
        erewrite Mem.loadbytes_drop. 2: eapply DROP.
        erewrite <- store_init_data_list_loadbytes_other.
        2: eapply Heqo0.
        erewrite <- Genv.store_zeros_loadbytes_other.
        2: eapply Heqo.        
        erewrite Mem.loadbytes_alloc_glob_unchanged.
        2: eapply ALLOC.
        congruence. congruence. 
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        left.
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence. }
    eapply IHsecs;eauto.

  - destruct (Mem.alloc_glob i m0 0 (init_data_list_size init)) eqn:ALLOC.
    destr_in H1.
    2: { rewrite alloc_sections_none in H1. congruence. }
    destr_in H1.
    2: { rewrite alloc_sections_none in H1. congruence. }
    destruct (Mem.drop_perm m3 b 0 (init_data_list_size init) Readable) eqn:DROP.
    2: { rewrite alloc_sections_none in H1. congruence. }    
    assert (globals_initialized_sections ge m4 (Global id) sec).
    { unfold globals_initialized_sections.
      unfold globals_initialized_sections in H0.
      destruct sec.
      - destruct H0. split.
        + eapply Mem.perm_drop_3;eauto.
          left. eapply Mem.alloc_glob_result in ALLOC.
          subst. congruence.
          erewrite <- store_init_data_list_perm. 2: eapply Heqo0.
          erewrite <- Genv.store_zeros_perm. 2: eapply Heqo.          
          eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.
          eauto.
          congruence.
        + intros.
          assert (Mem.perm m0 (Global id) ofs k p).
          eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.
          eapply Genv.store_zeros_perm;eauto.
          eapply store_init_data_list_perm;eauto.
          eapply Mem.perm_drop_4;eauto.
          congruence. eapply H3 in H5.
          eauto.
      - destruct H0 as (P1 & P2 & P3 & P4).
        split.
        (* 1 *)
        unfold Mem.range_perm in *.
        intros.
        eapply Mem.perm_drop_3;eauto.
        left. eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        erewrite <- store_init_data_list_perm. 2: eapply Heqo0.
        erewrite <- Genv.store_zeros_perm. 2: eapply Heqo.          
        eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.
        eauto.
        congruence.
        (* 2 *)
        split.
        intros.
        assert (Mem.perm m0 (Global id) ofs k p).
        eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.
        eapply Genv.store_zeros_perm;eauto.
        eapply store_init_data_list_perm;eauto.
        eapply Mem.perm_drop_4;eauto.
        congruence. eapply P2 in H3.
        eauto.
        (* 3 *)
        split.
        eapply load_store_init_data_invariant.
        2: eapply P3. intros.
        erewrite (Mem.load_drop m3);eauto.
        erewrite <- store_init_data_list_load_other.
        2: eapply Heqo0.
        erewrite <- (Genv.store_zeros_load_other m1);eauto.
        erewrite Mem.load_alloc_glob_unchanged;eauto.
        congruence.
        eapply Mem.alloc_glob_result in ALLOC. subst.
        congruence.
        eapply Mem.alloc_glob_result in ALLOC. subst.
        congruence. 
        left.
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        (* 4 *)
        erewrite Mem.loadbytes_drop. 2: eapply DROP.
        erewrite <- store_init_data_list_loadbytes_other.
        2: eapply Heqo0.
        erewrite <- Genv.store_zeros_loadbytes_other.
        2: eapply Heqo.        
        erewrite Mem.loadbytes_alloc_glob_unchanged.
        2: eapply ALLOC.
        congruence. congruence. 
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        left.
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
      - destruct H0 as (P1 & P2 & P3 & P4).
        split.
        (* 1 *)
        unfold Mem.range_perm in *.
        intros.
        eapply Mem.perm_drop_3;eauto.
        left. eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        erewrite <- store_init_data_list_perm. 2: eapply Heqo0.
        erewrite <- Genv.store_zeros_perm. 2: eapply Heqo.          
        eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.
        eauto.
        congruence.
        (* 2 *)
        split.
        intros.
        assert (Mem.perm m0 (Global id) ofs k p).
        eapply Mem.perm_alloc_glob_1 in ALLOC. eapply ALLOC.
        eapply Genv.store_zeros_perm;eauto.
        eapply store_init_data_list_perm;eauto.
        eapply Mem.perm_drop_4;eauto.
        congruence. eapply P2 in H3.
        eauto.
        (* 3 *)
        split.
        eapply load_store_init_data_invariant.
        2: eapply P3. intros.
        erewrite (Mem.load_drop m3);eauto.
        erewrite <- store_init_data_list_load_other.
        2: eapply Heqo0.
        erewrite <- (Genv.store_zeros_load_other m1);eauto.
        erewrite Mem.load_alloc_glob_unchanged;eauto.
        congruence.
        eapply Mem.alloc_glob_result in ALLOC. subst.
        congruence.
        eapply Mem.alloc_glob_result in ALLOC. subst.
        congruence. 
        left.
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        (* 4 *)
        erewrite Mem.loadbytes_drop. 2: eapply DROP.
        erewrite <- store_init_data_list_loadbytes_other.
        2: eapply Heqo0.
        erewrite <- Genv.store_zeros_loadbytes_other.
        2: eapply Heqo.        
        erewrite Mem.loadbytes_alloc_glob_unchanged.
        2: eapply ALLOC.
        congruence. congruence. 
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence.
        left.
        eapply Mem.alloc_glob_result in ALLOC.
        subst. congruence. }
    eapply IHsecs;eauto.
Qed.        
    

    
Lemma alloc_section_characterization: forall sec id m0 m ge,
    alloc_section ge (Some m0) id sec = Some m ->
    globals_initialized_sections ge m (Global id) sec.
Proof.
  unfold alloc_section.
  intros.
  unfold globals_initialized_sections.
  destr;simpl in *.
  - destruct (Mem.alloc_glob id m0 0 (Z.max (code_size instr_size code) 1)) eqn:ALLOC.
    split.
    eapply Mem.alloc_glob_result in ALLOC.
    subst.
    eapply Mem.perm_drop_1;eauto.
    lia.
    intros.
    exploit Mem.alloc_glob_result;eauto. intro. subst.
    exploit Mem.perm_drop_4; eauto.
    intro. exploit Mem.perm_alloc_glob_2; eauto.
    intros. eapply H2 in H1. split.
    eauto. eapply Mem.perm_drop_2 in H0;eauto.
    inv H0;auto.
  (* writable *)
  - destruct ( Mem.alloc_glob id m0 0 (init_data_list_size init)) eqn:FOLD.
    destr_in H.
    destr_in H.
    exploit Mem.alloc_glob_result;eauto. intros. subst.
    split.
    (* 1 *)
    unfold Mem.range_perm. intros.
    eapply Mem.perm_drop_1;eauto.
    (* 2 *)
    split. intros.
    assert (0 <= ofs < init_data_list_size init).
    exploit Mem.perm_drop_4; eauto.
    intro. exploit Mem.perm_alloc_glob_2; eauto.
    intros. exploit Genv.store_zeros_perm;eauto.
    exploit store_init_data_list_perm;eauto. intros.
    eapply H3 in H1. eapply H4 in H1.
    eapply H2. eauto.
    eapply Mem.perm_drop_2 in H;eauto.

    (* 3 *)
    split.
    
    
    eapply load_store_init_data_invariant. intros.
    eapply Mem.load_drop;eauto. repeat right. constructor.
    
    eapply store_init_data_list_charact;eauto.
    (* 4 *)
    erewrite Mem.loadbytes_drop;eauto.
    eapply store_init_data_list_loadbytes;eauto.
    repeat right. constructor.
    
  (* readable *)
  - destruct ( Mem.alloc_glob id m0 0 (init_data_list_size init)) eqn:FOLD.
    destr_in H.
    destr_in H.
    exploit Mem.alloc_glob_result;eauto. intros. subst.
    split.
    (* 1 *)
    unfold Mem.range_perm. intros.
    eapply Mem.perm_drop_1;eauto.
    (* 2 *)
    split. intros.
    assert (0 <= ofs < init_data_list_size init).
    exploit Mem.perm_drop_4; eauto.
    intro. exploit Mem.perm_alloc_glob_2; eauto.
    intros. exploit Genv.store_zeros_perm;eauto.
    exploit store_init_data_list_perm;eauto. intros.
    eapply H3 in H1. eapply H4 in H1.
    eapply H2. eauto.
    eapply Mem.perm_drop_2 in H;eauto.

    (* 3 *)
    split.
    
    
    eapply load_store_init_data_invariant. intros.
    eapply Mem.load_drop;eauto. repeat right. constructor.
    
    eapply store_init_data_list_charact;eauto.
    (* 4 *)
    erewrite Mem.loadbytes_drop;eauto.
    eapply store_init_data_list_loadbytes;eauto.
    repeat right. constructor.
Qed.    
    
    
Lemma alloc_external_symbols_none: forall l,
    fold_left (fun (a : option mem) (p : positive * symbentry) => alloc_external_comm_symbol a (fst p) (snd p))
              l None = None.
Proof.
  induction l;simpl;auto.
Qed.

Lemma alloc_external_symbols_pres_characterization: forall m0 symbtbl sectbl m ge id sec,
    sectbl!id = Some sec ->
    well_formed_symbtbl sectbl symbtbl ->
    alloc_external_symbols m0 symbtbl = Some m ->
    globals_initialized_sections ge m0 (Global id) sec ->
    globals_initialized_sections ge m (Global id) sec.
Proof.
  unfold well_formed_symbtbl,alloc_external_symbols.
  intros m0 symbtbl sectbl m ge id sec G W ALLOC P.
  assert (WF: forall (id : positive) (e : symbentry),
       In (id,e) (PTree.elements symbtbl) ->
       match symbentry_secindex e with
       | secindex_normal i =>
           symbentry_type e <> symb_notype /\
           i = id /\
           (exists sec : RelocProg.section instruction init_data,
              sectbl ! i = Some sec /\ sec_size instr_size sec = symbentry_size e /\ symbentry_value e = 0)
       | secindex_comm => symbentry_type e = symb_data /\ sectbl ! id = None
       | secindex_undef => symbentry_type e <> symb_notype /\ sectbl ! id = None
       end).
  intros. eapply W. eapply PTree.elements_complete. auto.
  clear W.

  rewrite PTree.fold_spec in ALLOC.
  set (l:= (PTree.elements symbtbl)) in *.
  generalize l m m0 WF ALLOC P. clear l m m0 WF ALLOC P.
  induction l;simpl. intros.
  inv ALLOC. auto.
  
  intros.

  (* we should ensure ALLOC return some *)
  destruct a;simpl in *.

  exploit WF. left. eauto.
  intros WF'.
  
  destr_in WF'.
  
  - destr_in ALLOC. 
    eapply IHl. 2: eapply ALLOC.
    intros. eapply WF. auto. auto.
    eapply IHl. 2: eapply ALLOC.
    intros. eapply WF. auto. auto.
  - destruct WF'.
    rewrite H in *.
    destruct (Mem.alloc_glob p m0 0 ((Z.max (symbentry_size s) 0))) eqn:GLOB.
    destr_in ALLOC.
    destruct ((Mem.drop_perm m2 b 0 (Z.max (symbentry_size s) 0) Writable)) eqn:DROP.
    eapply IHl. 2: eapply ALLOC.
    intros. eapply WF. auto.
    assert (p <> id).
    unfold not. intros. subst. congruence.
    exploit Mem.alloc_glob_result;eauto. intros. subst.
    eapply drop_pres_globals_initialized_sections.
    eapply store_zeros_pres_globals_initialized_sections.
    eapply alloc_glob_pres_globals_initialized_sections;eauto.
    congruence. eauto.
    congruence. eauto.
    congruence.

    erewrite alloc_external_symbols_none in ALLOC. congruence.
    erewrite alloc_external_symbols_none in ALLOC. congruence.
  - destruct WF'.
    destr_in ALLOC;try congruence.
    + destruct (Mem.alloc_glob p m0 0 1) eqn:GLOB.
      destruct ((Mem.drop_perm m1 b 0 1 Nonempty)) eqn:DROP.
      eapply IHl. 2: eapply ALLOC.
      intros. eapply WF. auto.
      assert (p <> id).
      unfold not. intros. subst. congruence.
      exploit Mem.alloc_glob_result;eauto. intros. subst.
      eapply drop_pres_globals_initialized_sections.
      eapply alloc_glob_pres_globals_initialized_sections;eauto.
      congruence. eauto.
      congruence.
      
      erewrite alloc_external_symbols_none in ALLOC. congruence.
    + destruct (Mem.alloc_glob p m0 0 1) eqn:GLOB.
      destr_in ALLOC.
      destruct ((Mem.drop_perm m2 b 0 1 Nonempty)) eqn:DROP.
      eapply IHl. 2: eapply ALLOC.
      intros. eapply WF. auto.
      assert (p <> id).
      unfold not. intros. subst. congruence.
      exploit Mem.alloc_glob_result;eauto. intros. subst.
      eapply drop_pres_globals_initialized_sections.
      eapply store_zeros_pres_globals_initialized_sections.
      eapply alloc_glob_pres_globals_initialized_sections;eauto.
      congruence. eauto.
      congruence. eauto.
      congruence.
      erewrite alloc_external_symbols_none in ALLOC. congruence.
      erewrite alloc_external_symbols_none in ALLOC. congruence.
Qed.


Lemma alloc_external_symbols_pres_external_characterization: 
  forall symbs symb ge m0 m id,
    ~ In id (map fst symbs) ->
    globals_initialized_external ge m0 (Global id) symb ->
    fold_left (fun (a : option mem) (p : positive * symbentry) => alloc_external_comm_symbol a (fst p) (snd p))
              symbs (Some m0) = Some m ->
    globals_initialized_external ge m (Global id) symb.
Proof.
  induction symbs;simpl;intros.
  inv H1. auto.
  destruct a;simpl in *.
  eapply Decidable.not_or in H.
  destruct H.

  rename H1 into ALLOC.
  destr_in ALLOC.
  - destr_in ALLOC.
    + eapply IHsymbs;eauto.
    + erewrite alloc_external_symbols_none in ALLOC. congruence.
    + destruct (Mem.alloc_glob i m0 0 1) eqn:GLOB.      
      destruct ((Mem.drop_perm m1 b 0 1 Nonempty)) eqn:DROP.
      eapply IHsymbs. 3: eapply ALLOC. auto.
      exploit Mem.alloc_glob_result;eauto. intros. subst.
      eapply drop_pres_globals_initialized_external.
      eapply alloc_glob_pres_globals_initialized_external;eauto.
      congruence. eauto.
      congruence. eauto.
      
      erewrite alloc_external_symbols_none in ALLOC. congruence.
  - destr_in ALLOC.
    + eapply IHsymbs;eauto.
    + destruct (Mem.alloc_glob i m0 0 (Z.max (symbentry_size s) 0)) eqn:GLOB.
      destr_in ALLOC.
      destruct ((Mem.drop_perm m2 b 0 (Z.max (symbentry_size s) 0) Writable)) eqn:DROP.
      eapply IHsymbs. 3: eapply ALLOC. auto.
      exploit Mem.alloc_glob_result;eauto. intros. subst.
      eapply drop_pres_globals_initialized_external.
      eapply store_zeros_pres_globals_initialized_external.
      eapply alloc_glob_pres_globals_initialized_external;eauto.
      congruence. eauto.
      congruence. eauto.
      congruence.
      erewrite alloc_external_symbols_none in ALLOC. congruence.
      erewrite alloc_external_symbols_none in ALLOC. congruence.
    + destruct (Mem.alloc_glob i m0 0 1) eqn:GLOB.
      destr_in ALLOC.
      destruct ((Mem.drop_perm m2 b 0 1 Nonempty)) eqn:DROP.
      eapply IHsymbs. 3: eapply ALLOC. auto.
      exploit Mem.alloc_glob_result;eauto. intros. subst.
      eapply drop_pres_globals_initialized_external.
      eapply store_zeros_pres_globals_initialized_external.
      eapply alloc_glob_pres_globals_initialized_external;eauto.
      congruence. eauto.
      congruence. eauto.
      congruence.
      erewrite alloc_external_symbols_none in ALLOC. congruence.
      erewrite alloc_external_symbols_none in ALLOC. congruence.

  - erewrite alloc_external_symbols_none in ALLOC. congruence.
Qed.

Lemma alloc_external_characterization: forall symb id m0 m ge ,
    symbentry_secindex symb = secindex_comm \/ symbentry_secindex symb = secindex_undef ->
    alloc_external_comm_symbol (Some m0) id symb = Some m ->
    globals_initialized_external ge m (Global id) symb.
Proof.
  unfold alloc_external_comm_symbol, globals_initialized_external.
  intros.
  rename H0 into ALLOC.
  destruct H;rewrite H in *.
  - destr.
    + destruct (Mem.alloc_glob id m0 0 (Z.max (symbentry_size symb) 0)) eqn:GLOB.
      destr_in ALLOC.
      exploit Mem.alloc_glob_result;eauto. intros. subst.
      split.
      (* 1 *)
      unfold Mem.range_perm. intros.
      eapply Mem.perm_drop_1;eauto.
      (* 2 *)
      split. intros.
      assert (0 <= ofs < Z.max (symbentry_size symb) 0).
      exploit Mem.perm_drop_4; eauto.
      intro. exploit Mem.perm_alloc_glob_2; eauto.
      intros. exploit Genv.store_zeros_perm;eauto.
      intros.
      eapply H3 in H1. eapply H2 in H1.
      auto.
      split. auto.
      eapply Mem.perm_drop_2 in ALLOC;eauto.
      
      (* 3 *)
      split.          
      eapply load_store_init_data_invariant. intros.
      eapply Mem.load_drop;eauto. repeat right. constructor.
      simpl. split;auto.

      eapply Genv.store_zeros_read_as_zero;eauto.
      (* rewrite store_zeros_equation in *. destr_in Heqo. *)

      (* assert ((Z.max (symbentry_size symb) 0) = 0). lia. *)
      (* rewrite H0. rewrite zle_true. eapply Heqo. lia. *)
      (* assert (Z.max (symbentry_size symb) 0 = (symbentry_size symb)) by lia. *)
      (* destr. rewrite H0. auto. *)

      (* 4 *)
      erewrite Mem.loadbytes_drop;eauto.
      simpl.

      
      generalize (Genv.store_zeros_loadbytes _ _ _ Heqo).
      unfold Genv.readbytes_as_zero. intros. rewrite app_nil_r.
      rewrite <- Z_to_nat_max.
      
      eapply H0.
      lia. lia.

      repeat right. constructor.
      
  - destr.  
    + destruct (Mem.alloc_glob id m0 0 1) eqn:GLOB.
      exploit Mem.alloc_glob_result;eauto;intros;subst.
      split.
      * eapply Mem.perm_drop_1;eauto. lia.
      * intros. exploit Mem.perm_drop_4; eauto.
        intro. exploit Mem.perm_alloc_glob_2; eauto.
        intros. eapply H2 in H1. split.
        lia. eapply Mem.perm_drop_2 in H0;eauto.
        inv H0;auto.
    + destruct (Mem.alloc_glob id m0 0 1) eqn:GLOB.
      destr_in ALLOC.
      exploit Mem.alloc_glob_result;eauto;intros;subst.
      split.
      * eapply Mem.perm_drop_1;eauto. lia.
      * intros. exploit Mem.perm_drop_4; eauto.
        intro. exploit Mem.perm_alloc_glob_2; eauto.
        intros.
        exploit Genv.store_zeros_perm;eauto. intros.
        eapply H3 in H1. eapply H2 in H1. split.
        lia. eapply Mem.perm_drop_2 in H0;eauto.
        inv H0;auto.
Qed.    

(** Properties about init_mem *)
Lemma init_mem_characterization_gen: forall p m,
    well_formed_symbtbl (prog_sectable p) (prog_symbtable p) ->
    init_mem p = Some m ->
    globals_initialized (globalenv p) p m.
Proof.
   unfold init_mem.
   unfold globals_initialized.
   intros p m WF H id b ofs0 G. destr_in H.
   
   (* symbentry exists *)
   unfold globalenv in G. unfold Genv.find_symbol in G.
   unfold gen_symb_map in G.
   simpl in G. rewrite PTree.gmap in G. unfold option_map in G.
   destr_in G.

   unfold well_formed_symbtbl in WF.
   generalize (WF id s Heqo0). rename WF into WF0. intros WF.
   unfold gen_global in G.
   (* destruct symbentry_secindex s *)
   
   generalize (PTree.elements_keys_norepet (prog_sectable p)).
   generalize (PTree.elements_keys_norepet (prog_symbtable p)).
   intros NOREP1 NOREP2.
   
   destruct (symbentry_secindex s) eqn:SECIDX.
   - inv G. 
     destruct WF as (P1 & P2 & sec & P3 & P4 & P5).
     rewrite P5. rewrite Ptrofs.unsigned_repr. simpl.
     subst. rewrite P3.
     2: { unfold Ptrofs.max_unsigned. unfold Ptrofs.modulus.
          unfold Ptrofs.wordsize. unfold Wordsize_Ptrofs.wordsize.
          destr;simpl;lia. }
     
     unfold alloc_sections in Heqo. rewrite PTree.fold_spec in Heqo.
     exploit PTree.elements_correct;eauto. 
     intros INELE.
     unfold section in *.
     set (l:= (PTree.elements (prog_sectable p))) in *.
     eapply in_norepet_unique in INELE;eauto. destruct INELE as (gl1 & gl2 & Q1 & Q2 & Q3).
     rewrite Q1 in *.
     rewrite fold_left_app in Heqo.
     simpl in Heqo.
     unfold ident in *.
     set (m0':=(fold_left
                  (fun (a : option mem) (p0 : positive * RelocProg.section instruction init_data) =>
                     alloc_section (globalenv p) a (fst p0) (snd p0)) gl1 (Some Mem.empty))) in Heqo.
     destruct m0'.
     + destruct ((alloc_section (globalenv p) (Some m1) id sec)) eqn:ALLOC.
       * eapply alloc_section_characterization in ALLOC.
         exploit alloc_sections_pres_characterization. eapply Q2.
         eapply ALLOC. eauto.
         intros Q.
         exploit alloc_external_symbols_pres_characterization;eauto.
       * erewrite alloc_sections_none in Heqo.
         congruence.
     + simpl in Heqo.
       erewrite alloc_sections_none in Heqo.
       congruence.
   - destruct WF as (P1 & P2).
     rewrite P2. rewrite P1.
     inv G. 
     unfold alloc_external_symbols in H. rewrite PTree.fold_spec in H.
     exploit PTree.elements_correct;eauto. 
     intros INELE.
     unfold section in *.
     set (l:= (PTree.elements (prog_symbtable p))) in *.
     eapply in_norepet_unique in INELE;eauto. destruct INELE as (gl1 & gl2 & Q1 & Q2 & Q3).
     rewrite Q1 in *.
     rewrite fold_left_app in H.
     simpl in H.
     unfold ident in *.
     set (m0':=(fold_left
           (fun (a : option mem) (p : positive * symbentry) => alloc_external_comm_symbol a (fst p) (snd p)) gl1
           (Some m0))) in *.
     destruct m0'.
     + destruct (alloc_external_comm_symbol (Some m1) id s) eqn:ALLOC.
       * eapply alloc_external_characterization in ALLOC.
         exploit alloc_external_symbols_pres_external_characterization. eapply Q2.
         eapply ALLOC. eauto.
         unfold globals_initialized_external.
         rewrite P1. rewrite SECIDX.
         eauto. auto.
       * erewrite alloc_external_symbols_none in H.
         congruence.
     + simpl in H.
       erewrite alloc_external_symbols_none in H.
       congruence.
   - destruct WF as (P1 & P2).
     rewrite P2. destr.
     (* 2 same goals *)
     { inv G. 
     unfold alloc_external_symbols in H. rewrite PTree.fold_spec in H.
     exploit PTree.elements_correct;eauto. 
     intros INELE.
     unfold section in *.
     set (l:= (PTree.elements (prog_symbtable p))) in *.
     eapply in_norepet_unique in INELE;eauto. destruct INELE as (gl1 & gl2 & Q1 & Q2 & Q3).
     rewrite Q1 in *.
     rewrite fold_left_app in H.
     simpl in H.
     unfold ident in *.
     set (m0':=(fold_left
           (fun (a : option mem) (p : positive * symbentry) => alloc_external_comm_symbol a (fst p) (snd p)) gl1
           (Some m0))) in *.
     destruct m0'.
     + destruct (alloc_external_comm_symbol (Some m1) id s) eqn:ALLOC.
       * eapply alloc_external_characterization in ALLOC.
         generalize (alloc_external_symbols_pres_external_characterization gl2 s (globalenv p) m2 m id Q2 ALLOC H). 
         unfold globals_initialized_external.
         rewrite Heqs0. rewrite SECIDX.
         eauto. auto.
       * erewrite alloc_external_symbols_none in H.
         congruence.
     + simpl in H.
       erewrite alloc_external_symbols_none in H.
       congruence. }

     inv G.
     unfold alloc_external_symbols in H. rewrite PTree.fold_spec in H.
     exploit PTree.elements_correct;eauto. 
     intros INELE.
     unfold section in *.
     set (l:= (PTree.elements (prog_symbtable p))) in *.
     eapply in_norepet_unique in INELE;eauto. destruct INELE as (gl1 & gl2 & Q1 & Q2 & Q3).
     rewrite Q1 in *.
     rewrite fold_left_app in H.
     simpl in H.
     unfold ident in *.
     set (m0':=(fold_left
           (fun (a : option mem) (p : positive * symbentry) => alloc_external_comm_symbol a (fst p) (snd p)) gl1
           (Some m0))) in *.
     destruct m0'.
     + destruct (alloc_external_comm_symbol (Some m1) id s) eqn:ALLOC.
       * eapply alloc_external_characterization in ALLOC.
         generalize (alloc_external_symbols_pres_external_characterization gl2 s (globalenv p) m2 m id Q2 ALLOC H). 
         unfold globals_initialized_external.
         rewrite Heqs0. rewrite SECIDX.
         eauto. auto.
       * erewrite alloc_external_symbols_none in H.
         congruence.
     + simpl in H.
       erewrite alloc_external_symbols_none in H.
       congruence.
Qed.       


Lemma store_init_data_nextblock : forall v ge m b ofs m',
  store_init_data ge m b ofs v = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.

         
Proof.
  intros. destruct v; simpl in *; try now (eapply Mem.nextblock_store; eauto).
  eapply Genv.store_zeros_nextblock.
  eauto.

  (* destr_in H. destruct p. eapply Mem.nextblock_store;eauto. *)
  
Qed.
    
Lemma store_init_data_list_nextblock : forall l ge m b ofs m',
  store_init_data_list ge m b ofs l = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
 Proof.
  induction l; intros.
  - inv H. auto.
  - inv H. destr_match_in H1; inv H1.
    exploit store_init_data_nextblock; eauto.
    exploit IHl; eauto. intros. congruence.
Qed.

Lemma store_init_data_list_support: forall l ge m b ofs m',
    store_init_data_list ge m b ofs l = Some m' ->
    Mem.support m' = Mem.support m.
Proof.
  induction l;intros.
  - inv H. auto.
  - inv H. destr_match_in H1;inv H1.
    transitivity (Mem.support m0). eapply IHl. eauto.
    destruct a;simpl in EQ;try (eapply Mem.support_store;eauto;fail).
    eapply Genv.store_zeros_support. eauto.

    (* destr_in EQ. destruct p. eapply Mem.support_store;eauto. *)
Qed.

Lemma store_init_data_stack : forall v ge (m m' : mem) (b : block) (ofs : Z),
       store_init_data ge m b ofs v = Some  m' -> Mem.stack (Mem.support m') = Mem.stack (Mem.support m).
Proof.
  intros v ge0 m m' b ofs H. destruct v; simpl in *;try (f_equal;now eapply Mem.support_store; eauto).
  eapply Genv.store_zeros_stack.
  eauto.

  (* destr_in H. destruct p. f_equal;eapply Mem.support_store; eauto. *)
Qed.

Lemma store_init_data_list_stack : forall l ge (m m' : mem) (b : block) (ofs : Z),
       store_init_data_list ge m b ofs l = Some m' -> Mem.stack (Mem.support m') = Mem.stack (Mem.support m).
Proof.
  induction l; intros.
  - simpl in H. inv H. auto.
  - simpl in H. destr_match_in H; inv H.
    exploit store_init_data_stack; eauto.
    exploit IHl; eauto.
    intros. congruence.
Qed.

Lemma alloc_section_stack: forall ge id sec m m',
    alloc_section ge (Some m) id sec = Some m' ->
    Mem.stack (Mem.support m) = Mem.stack (Mem.support m').
Proof.
  unfold alloc_section. intros.
  repeat destr_in H.
  exploit Mem.support_drop;eauto.
  exploit Mem.support_alloc_glob;eauto. intros.
  rewrite H0. rewrite H. auto.
  exploit Mem.support_drop;eauto.
  exploit Mem.support_alloc_glob;eauto. intros.
  exploit Genv.store_zeros_stack;eauto. intros (?&?).
  exploit store_init_data_list_stack;eauto. intros.
  rewrite H0. rewrite H4. rewrite H2.
  rewrite H. auto.
  exploit Mem.support_drop;eauto.
  exploit Mem.support_alloc_glob;eauto. intros.
  exploit Genv.store_zeros_stack;eauto. intros (?&?).
  exploit store_init_data_list_stack;eauto. intros.
  rewrite H0. rewrite H4. rewrite H2.
  rewrite H. auto.
Qed.  

Definition alloc_property_aux (m: mem) (optm': option mem):=
  forall m', optm' = Some m' ->
        Mem.stack (Mem.support m) = Mem.stack (Mem.support m').

Lemma alloc_sections_stack_aux: forall ge defs m,
     alloc_property_aux m
            (fold_left
    (fun (a : option mem) (p : positive * section) =>
     alloc_section ge a (fst p) (snd p))
    defs (Some m)).
Proof.
  intros. eapply Bounds.fold_left_preserves.
  unfold alloc_property_aux. intros.
  destruct a.
  eapply alloc_section_stack in H0. rewrite <- H0.
  eapply H. auto.
  simpl in H0. inv H0.
  unfold alloc_property_aux. intros. inv H. auto.
Qed.
  
Lemma alloc_sections_stack: forall ge sectbl m m',
    alloc_sections ge sectbl m = Some m' ->
    Mem.stack (Mem.support m) = Mem.stack (Mem.support m').
Proof.
  
  unfold alloc_sections. intros ge sectbl m m'.
  rewrite PTree.fold_spec. intros.
  exploit alloc_sections_stack_aux;eauto.
Qed.

Lemma alloc_external_symbol_stack: forall id e m m',
    alloc_external_comm_symbol(Some m) id e = Some m' ->
    Mem.stack (Mem.support m) = Mem.stack (Mem.support m').
Proof.
  unfold alloc_external_comm_symbol.
  intros. repeat destr_in H.
  exploit Mem.support_drop;eauto.
  exploit Mem.support_alloc_glob;eauto. intros.
  rewrite H0. rewrite H. auto.
  exploit Mem.support_drop;eauto.
  exploit Mem.support_alloc_glob;eauto. intros.
  exploit Genv.store_zeros_stack;eauto. intros (?&?).
  rewrite H0. rewrite H2. rewrite H. auto.
  exploit Mem.support_drop;eauto.
  exploit Mem.support_alloc_glob;eauto. intros.
  exploit Genv.store_zeros_stack;eauto. intros (?&?).
  rewrite H0. rewrite H2. rewrite H. auto.
  (* exploit Mem.support_drop;eauto. *)
  (* exploit Mem.support_alloc_glob;eauto. intros. *)
  (* exploit Genv.store_zeros_stack;eauto. intros (?&?). *)
  (* rewrite H0. rewrite H2. rewrite H. auto. *)
  (* exploit Mem.support_drop;eauto. *)
  (* exploit Mem.support_alloc_glob;eauto. intros. *)
  (* exploit Genv.store_zeros_stack;eauto. intros (?&?). *)
  (* rewrite H0. rewrite H2. rewrite H. auto. *)
Qed.



Lemma alloc_external_symbols_stack: forall symbtbl m m',
    alloc_external_symbols m symbtbl = Some m' ->
    Mem.stack (Mem.support m) = Mem.stack (Mem.support m').
Proof.
  unfold alloc_external_symbols. intros.
  rewrite PTree.fold_spec in H.
  assert (alloc_property_aux m (fold_left
        (fun (a : option mem) (p : positive * symbentry) =>
         alloc_external_comm_symbol a (fst p) (snd p))
        (PTree.elements symbtbl) (Some m))).
  eapply Bounds.fold_left_preserves.
  unfold alloc_property_aux.
  intros.
  destruct a.
  eapply alloc_external_symbol_stack in H1.
  rewrite <- H1.  eapply H0. auto.
  simpl in H1. congruence.
  unfold alloc_property_aux.
  intros. inv H0;auto.
  unfold alloc_property_aux in H0.
  eapply H0. auto.
Qed.


Lemma init_mem_stack:
  forall p m,
    init_mem p = Some m ->
    Mem.stack (Mem.support m) = Node None nil nil None.
Proof.
  intros. unfold init_mem in H.
  repeat destr_in H.
  erewrite <- alloc_external_symbols_stack; eauto.
  erewrite <- alloc_sections_stack; eauto.
  simpl. auto.
Qed.





Section STORE_INIT_DATA_PRESERVED.
  Variable ge1: Genv.t.
  Variable ge2: Genv.t.

  Hypothesis symbols_preserved:
    forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

  Lemma store_init_data_pres: forall d m b ofs,
      store_init_data ge1 m b ofs d = store_init_data ge2 m b ofs d.
  Proof.
    destruct d;simpl;auto.
    intros.
    assert (EQ: forall id ofs, Genv.symbol_address ge2 id ofs = Genv.symbol_address ge1 id ofs).
    { unfold Genv.symbol_address; simpl; intros. rewrite symbols_preserved;auto. }
    (* rewrite symbols_preserved. *)
    rewrite EQ.
    auto.
  Qed.

  Lemma store_init_data_list_pres: forall l m b ofs,
      store_init_data_list ge1 m b ofs l = store_init_data_list ge2 m b ofs l.
  Proof.
    induction l;auto.
    intros. simpl. rewrite store_init_data_pres.
    destr.
  Qed.
  
End STORE_INIT_DATA_PRESERVED.


Lemma alloc_sections_valid_aux: forall l b m m' ge,
    fold_left
      (fun (a : option mem)
         (p : positive * RelocProg.section instruction init_data)
       => alloc_section ge a (fst p) (snd p)) l (Some m) = Some m' ->
      sup_In b m.(Mem.support) ->
      sup_In b m'.(Mem.support).
Proof.
  induction l;intros.
  simpl in H. inv H. auto.
  simpl in H. destruct a.
  destruct s.
  - simpl in *.
    destruct Mem.alloc_glob eqn:ALLOC in H.
    apply Mem.support_alloc_glob in ALLOC.
    destruct (Mem.drop_perm) eqn:FOLD in H.
    eapply IHl;eauto.
    eapply Mem.drop_perm_valid_block_1;eauto.
    unfold Mem.valid_block.
    rewrite ALLOC.
    apply Mem.sup_incr_glob_in. right. auto.
    clear IHl.
    induction l;simpl in H.
    inv H.  apply IHl. auto.
  - simpl in *.
    destruct Mem.alloc_glob eqn:ALLOC in H.
    destr_in H. destr_in H.
    apply Mem.support_alloc_glob in ALLOC.
    destruct (Mem.drop_perm) eqn:FOLD in H.
    eapply IHl;eauto.
    eapply Mem.drop_perm_valid_block_1;eauto.
    unfold Mem.valid_block.
    
    eapply store_init_data_list_support in Heqo0.
    rewrite Heqo0.
    eapply Genv.store_zeros_support in Heqo. rewrite Heqo.
    rewrite ALLOC.
    apply Mem.sup_incr_glob_in. right. auto.
    clear IHl.
    induction l;simpl in H.
    inv H.  apply IHl. auto.
    clear IHl.
    induction l;simpl in H.
    inv H.  apply IHl. auto.
        clear IHl.
    induction l;simpl in H.
    inv H.  apply IHl. auto.

  - simpl in *.
    destruct Mem.alloc_glob eqn:ALLOC in H.
    destr_in H. destr_in H.
    apply Mem.support_alloc_glob in ALLOC.
    destruct (Mem.drop_perm) eqn:FOLD in H.
    eapply IHl;eauto.
    eapply Mem.drop_perm_valid_block_1;eauto.
    unfold Mem.valid_block.
    
    eapply store_init_data_list_support in Heqo0.
    rewrite Heqo0.
    eapply Genv.store_zeros_support in Heqo. rewrite Heqo.
    rewrite ALLOC.
    apply Mem.sup_incr_glob_in. right. auto.
    clear IHl.
    induction l;simpl in H.
    inv H.  apply IHl. auto.
    clear IHl.
    induction l;simpl in H.
    inv H.  apply IHl. auto.
        clear IHl.
    induction l;simpl in H.
    inv H.  apply IHl. auto.
Qed.


Lemma alloc_sections_valid: forall id sec sectbl m m' ge,
      sectbl ! id = Some sec ->
      alloc_sections ge sectbl m = Some m' ->     
      sup_In (Global id) m'.(Mem.support).
Proof.
  unfold alloc_sections.
  intros id sec sectbl m m' ge A1 A2 .
  rewrite PTree.fold_spec in A2.
  apply PTree.elements_correct in A1.
  generalize (PTree.elements_keys_norepet sectbl).
  intros NOREP.
  exploit in_norepet_unique_r;eauto.
  intros (gl1 & gl2 & P1 & P2).
  unfold section in *. rewrite P1 in *.
  rewrite fold_left_app in A2.
  simpl in A2.
   unfold ident in *.
  destruct ((alloc_section ge
            (fold_left
               (fun (a : option mem)
                  (p : positive *
                       RelocProg.section instruction init_data) =>
                alloc_section ge a (fst p) (snd p)) gl1 
               (Some m)) id sec)) eqn:FOLD.
  - 
    exploit alloc_sections_valid_aux;eauto.
    unfold alloc_section in FOLD at 1. destr_in FOLD.
    destruct sec.
    + simpl in *.
      destruct Mem.alloc_glob eqn:ALLOC in FOLD.
      apply Mem.support_alloc_glob in ALLOC.
      generalize (Mem.sup_incr_glob_in1 id (Mem.support m1)).
      rewrite <- ALLOC.
      intros.
      exploit Mem.drop_perm_valid_block_1;eauto.
    + simpl in *.     
      destruct Mem.alloc_glob eqn:ALLOC in FOLD.
      repeat destr_in FOLD.
      apply Mem.support_alloc_glob in ALLOC.      
      generalize (Mem.sup_incr_glob_in1 id (Mem.support m1)).
      rewrite <- ALLOC.
      exploit Genv.store_zeros_support;eauto.
      exploit store_init_data_list_support;eauto.
      intros. rewrite <- H1 in *.
      rewrite <- H in *.
      exploit Mem.drop_perm_valid_block_1;eauto.
    + simpl in *.     
      destruct Mem.alloc_glob eqn:ALLOC in FOLD.
      repeat destr_in FOLD.
      apply Mem.support_alloc_glob in ALLOC.      
      generalize (Mem.sup_incr_glob_in1 id (Mem.support m1)).
      rewrite <- ALLOC.
      exploit Genv.store_zeros_support;eauto.
      exploit store_init_data_list_support;eauto.
      intros. rewrite <- H1 in *.
      rewrite <- H in *.
      exploit Mem.drop_perm_valid_block_1;eauto.
  - clear A1 NOREP P1 P2.
    induction gl2.
    simpl in A2. inv A2.
    apply IHgl2. auto.
Qed.

Lemma alloc_external_symbols_valid_aux2: forall l,
        fold_left
          (fun (a : option mem) (p : positive * symbentry) =>
             alloc_external_comm_symbol a (fst p) (snd p)) l None =
        None.
Proof.
  induction l;simpl;auto.
Qed.

Lemma alloc_external_symbols_valid_aux: forall l m m' b,
    fold_left
      (fun (a : option mem) (p : positive * symbentry) =>
         alloc_external_comm_symbol a (fst p) (snd p)) l (Some m) =
    Some m' ->
    sup_In b (Mem.support m) ->
    sup_In b (Mem.support m').
Proof.
  induction l;intros.
  simpl in H. inv H. auto.
  simpl in H.
  destruct (symbentry_type (snd a)).
  - destruct (symbentry_secindex (snd a)).
    + eapply IHl;eauto.
    + rewrite alloc_external_symbols_valid_aux2 in H. inv H.
    + destruct Mem.alloc_glob eqn:ALLOC in H.
      destruct Mem.drop_perm eqn:DROP in H.
      eapply IHl;eauto.
      eapply Mem.drop_perm_valid_block_1;eauto.
      unfold Mem.valid_block. apply Mem.support_alloc_glob in ALLOC.
      rewrite ALLOC. eapply Mem.sup_incr_glob_in.
      right. auto.
      rewrite alloc_external_symbols_valid_aux2 in H. inv H.
  - destruct (symbentry_secindex (snd a)).
    + eapply IHl;eauto.
    + destruct Mem.alloc_glob eqn:ALLOC in H.
      destruct store_zeros eqn:STORE in H.
      destruct Mem.drop_perm eqn:DROP in H.
      eapply IHl;eauto.
      eapply Mem.drop_perm_valid_block_1;eauto.
      unfold Mem.valid_block.
      erewrite Genv.store_zeros_support.
      apply Mem.support_alloc_glob in ALLOC.
      rewrite ALLOC. eapply Mem.sup_incr_glob_in.
      right. auto.  eauto.
      rewrite alloc_external_symbols_valid_aux2 in H. inv H.
      rewrite alloc_external_symbols_valid_aux2 in H. inv H.
    + destruct Mem.alloc_glob eqn:ALLOC in H.
      destruct store_zeros eqn:STORE in H.
      destruct Mem.drop_perm eqn:DROP in H.
      eapply IHl;eauto.
      eapply Mem.drop_perm_valid_block_1;eauto.
      unfold Mem.valid_block.
      erewrite Genv.store_zeros_support.
      apply Mem.support_alloc_glob in ALLOC.
      rewrite ALLOC. eapply Mem.sup_incr_glob_in.
      right. auto.  eauto.
      rewrite alloc_external_symbols_valid_aux2 in H. inv H.
      rewrite alloc_external_symbols_valid_aux2 in H. inv H.
  - rewrite alloc_external_symbols_valid_aux2 in H. inv H.
Qed.            
    
Lemma alloc_external_symbols_valid: forall id e symbtbl m m',
    symbtbl ! id = Some e ->
    alloc_external_symbols m symbtbl = Some m' ->
    match symbentry_secindex e with
    | secindex_normal i =>
      sup_In (Global i) m.(Mem.support) ->
      sup_In (Global i) m'.(Mem.support)
    | secindex_comm =>
      symbentry_type e = symb_data ->
      sup_In (Global id) m'.(Mem.support)
    | secindex_undef =>
      symbentry_type e <> symb_notype ->
      sup_In (Global id) m'.(Mem.support)
    end.
Proof.
  unfold alloc_external_symbols.
  intros id e symbtbl m m' A1 A2.
  rewrite PTree.fold_spec in A2.
  apply PTree.elements_correct in A1.
  generalize (PTree.elements_keys_norepet symbtbl).
  intros NOREP.
  exploit in_norepet_unique_r;eauto.
  intros (gl1 & gl2 & P1 & P2).
  rewrite P1 in *.
  rewrite fold_left_app in A2.
  simpl in A2.
  unfold ident in *.
  destruct (fold_left
               (fun (a : option mem) (p : positive * symbentry) =>
                alloc_external_comm_symbol a (fst p) (snd p)) gl1
               (Some m)) eqn:FOLD.
  simpl in A2.
  - destruct (symbentry_secindex e).
    + destruct (symbentry_type e).
      * intros.
        exploit alloc_external_symbols_valid_aux.
        eapply FOLD. eauto. intros.
        exploit alloc_external_symbols_valid_aux.
        eapply A2. eauto. auto.
      * intros.
        exploit alloc_external_symbols_valid_aux.
        eapply FOLD. eauto. intros.
        exploit alloc_external_symbols_valid_aux.
        eapply A2. eauto. auto.
      * clear A1 P1 P2 NOREP.
        induction gl2.
        simpl in A2. inv A2.
        simpl in A2. apply IHgl2. auto.
    + intros.
      destruct (symbentry_type e);try congruence.
      destruct Mem.alloc_glob eqn:ALLOC in A2.
      destruct store_zeros eqn:STORE in A2.
      * destruct Mem.drop_perm eqn:DROP in A2.
        -- exploit alloc_external_symbols_valid_aux.
           apply A2. eapply Mem.drop_perm_valid_block_1;eauto.
           unfold Mem.valid_block.
           erewrite  Genv.store_zeros_support;eauto.
           apply Mem.support_alloc_glob in ALLOC.
           rewrite ALLOC.
           erewrite Mem.sup_incr_glob_in. left.
           eauto. auto.
        -- clear A1 P1 P2 NOREP.
           induction gl2.
           simpl in A2. inv A2.
           simpl in A2. apply IHgl2. auto.
      * clear A1 P1 P2 NOREP.
        induction gl2.
        simpl in A2. inv A2.
        simpl in A2. apply IHgl2. auto.
    + intros.
      destruct (symbentry_type e);try congruence.
      * destruct Mem.alloc_glob eqn:ALLOC in A2.
        destruct Mem.drop_perm eqn:DROP in A2.
        -- exploit alloc_external_symbols_valid_aux.
           apply A2. eapply Mem.drop_perm_valid_block_1;eauto.
           unfold Mem.valid_block.
           apply Mem.support_alloc_glob in ALLOC.
           rewrite ALLOC.
           erewrite Mem.sup_incr_glob_in. left.
           eauto. auto.
        -- clear A1 P1 P2 NOREP.
           induction gl2.
           simpl in A2. inv A2.
           simpl in A2. apply IHgl2. auto.
      * destruct Mem.alloc_glob eqn:ALLOC in A2.
        destruct store_zeros eqn:STORE in A2.
        -- destruct Mem.drop_perm eqn:DROP in A2.
           ++ exploit alloc_external_symbols_valid_aux.
              apply A2. eapply Mem.drop_perm_valid_block_1;eauto.
              unfold Mem.valid_block.
              erewrite  Genv.store_zeros_support;eauto.
              apply Mem.support_alloc_glob in ALLOC.
              rewrite ALLOC.
              erewrite Mem.sup_incr_glob_in. left.
              eauto. auto.
           ++ clear A1 P1 P2 NOREP.
              induction gl2.
              simpl in A2. inv A2.
              simpl in A2. apply IHgl2. auto.
        --
          clear A1 P1 P2 NOREP.
          induction gl2.
          simpl in A2. inv A2.
          simpl in A2. apply IHgl2. auto.
  - clear A1 P1 P2 NOREP.
    induction gl2.
    simpl in A2. inv A2.
    simpl in A2. apply IHgl2. auto.
Qed.

Lemma find_symbol_not_fresh: forall p id b m ofs,
    well_formed_symbtbl p.(prog_sectable) p.(prog_symbtable) ->
    init_mem p = Some m ->
    Genv.find_symbol (globalenv p) id = Some (b,ofs) ->
    Mem.valid_block m b.
Proof.
  unfold init_mem, globalenv, Genv.find_symbol, gen_symb_map.
  simpl. intros p id b m ofs MATCH INIT GENV.
  destr_in INIT.
  rewrite PTree.gmap in GENV. unfold option_map in GENV.
  destr_in GENV. inv GENV.
  unfold gen_global in H0.

  unfold well_formed_symbtbl in MATCH.
  generalize (MATCH _ _ Heqo0). intros A.  
  unfold Mem.valid_block.
  destr_in A.
  - destruct A as (P1 & sec & P2 & P3 & P4 & P5) .
    eapply alloc_sections_valid in Heqo;eauto.
    eapply alloc_external_symbols_valid in INIT;eauto.
    rewrite Heqs0 in INIT. inv H0. eauto.
  - eapply alloc_external_symbols_valid in INIT;eauto.
    destruct A.
    rewrite Heqs0,H in INIT.
    inv H0. auto.
  - destruct A.
    eapply alloc_external_symbols_valid in INIT;eauto.
    rewrite Heqs0 in INIT.
    inv H0. auto.
Qed.


(** New defined eval_builtin_arg for Genv.t *)
Section EVAL_BUILTIN_ARG.

Variable A: Type.

Variable ge: Genv.t.
Variable e: A -> val.
Variable sp: val.
Variable m:mem. 

Inductive eval_builtin_arg: builtin_arg A -> val -> Prop :=
  | eval_BA: forall x,
      eval_builtin_arg (BA x) (e x)
  | eval_BA_int: forall n,
      eval_builtin_arg (BA_int n) (Vint n)
  | eval_BA_long: forall n,
      eval_builtin_arg (BA_long n) (Vlong n)
  | eval_BA_float: forall n,
      eval_builtin_arg (BA_float n) (Vfloat n)
  | eval_BA_single: forall n,
      eval_builtin_arg (BA_single n) (Vsingle n)
  | eval_BA_loadstack: forall chunk ofs v,
      Mem.loadv chunk m (Val.offset_ptr sp ofs) = Some v ->
      eval_builtin_arg (BA_loadstack chunk ofs) v
  | eval_BA_addrstack: forall ofs,
      eval_builtin_arg (BA_addrstack ofs) (Val.offset_ptr sp ofs)
  | eval_BA_loadglobal: forall chunk id ofs v,
      Mem.loadv chunk m  (Genv.symbol_address ge id ofs) = Some v ->
      eval_builtin_arg (BA_loadglobal chunk id ofs) v
  | eval_BA_addrglobal: forall id ofs,
      eval_builtin_arg (BA_addrglobal id ofs) (Genv.symbol_address ge id ofs)
  | eval_BA_splitlong: forall hi lo vhi vlo,
      eval_builtin_arg hi vhi -> eval_builtin_arg lo vlo ->
      eval_builtin_arg (BA_splitlong hi lo) (Val.longofwords vhi vlo)
  | eval_BA_addptr: forall a1 a2 v1 v2,
      eval_builtin_arg a1 v1 ->
      eval_builtin_arg a2 v2 ->
      eval_builtin_arg (BA_addptr a1 a2) (if Archi.ptr64 then Val.addl v1 v2 else Val.add v1 v2).

                       
Definition eval_builtin_args (al: list (builtin_arg A)) (vl: list val) : Prop :=
  list_forall2 eval_builtin_arg al vl.

Lemma eval_builtin_arg_determ:
  forall a v, eval_builtin_arg a v -> forall v', eval_builtin_arg a v' -> v' = v.
Proof.
  induction 1; intros v' EV; inv EV; try congruence.
  f_equal; eauto.
  destruct Archi.ptr64;f_equal;auto.
Qed.

Lemma eval_builtin_args_determ:
  forall al vl, eval_builtin_args al vl -> forall vl', eval_builtin_args al vl' -> vl' = vl.
Proof.
  induction 1; intros v' EV; inv EV; f_equal; eauto using eval_builtin_arg_determ.
Qed.

 
End EVAL_BUILTIN_ARG.

Hint Constructors eval_builtin_arg: barg.

(* same lemmas as the in Events *)
Section EVAL_BUILTIN_ARG_PRESERVED.

Variables A: Type.
Variable ge1: Genv.t.
Variable ge2: Genv.t.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

Lemma eval_builtin_arg_preserved:
  forall a v, eval_builtin_arg A ge1 e sp m a v -> eval_builtin_arg A ge2 e sp m a v.
Proof.
   assert (EQ: forall id ofs, Genv.symbol_address ge2 id ofs = Genv.symbol_address ge1 id ofs).
  { unfold Genv.symbol_address; simpl; intros. rewrite symbols_preserved; auto. }
  induction 1; eauto with barg. rewrite <- EQ in H; eauto with barg. rewrite <- EQ; eauto with barg.
Qed.

Lemma eval_builtin_args_preserved:
  forall al vl, eval_builtin_args A ge1 e sp m al vl -> eval_builtin_args A ge2 e sp m al vl.
Proof.
  induction 1; constructor; auto; eapply eval_builtin_arg_preserved; eauto.
Qed.

End EVAL_BUILTIN_ARG_PRESERVED.

End WITH_INSTR_SIZE.
