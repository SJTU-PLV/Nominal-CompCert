(** * Encoding of the symbol table into a section *)

Require Import Coqlib lib.Integers AST Maps.
Require Import Errors.
Require Import RelocProg Encode.
Require Import Memdata.
Require Import encode.Hex encode.Bits.
Import Hex Bits.
Import ListNotations.


Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.


(** Symbol entry definition:

   typedef struct {
   Elf32_Word     st_name;
   Elf32_Addr     st_value;
   Elf32_Word     st_size;
   unsigned char  st_info;
   unsigned char  st_other;
   Elf32_Half     st_shndx;
   } Elf32_Sym

  typedef struct
  {
    Elf64_Word	st_name;		/* Symbol name (string tbl index) */
    unsigned char	st_info;		/* Symbol type and binding */
    unsigned char st_other;		/* Symbol visibility */
    Elf64_Section	st_shndx;		/* Section index */
    Elf64_Addr	st_value;		/* Symbol value */
    Elf64_Xword	st_size;		/* Symbol size */
  } Elf64_Sym;

*)

Definition encode_symbtype (t:symbtype) :=
  match t with
  | symb_func => 2
  | symb_data => 1
  | symb_notype => 0
  end.

Definition encode_symbbind (b:bindtype) :=
  match b with
  | bind_local => 0
  | bind_global => 1
  end.

Definition encode_glob_symb_info (b:bindtype) (t:symbtype) := 
  (encode_symbbind b) * (Z.pow 2 4) + encode_symbtype t.

Lemma encode_glob_symb_info_range : forall b t,
    0 <=  encode_glob_symb_info b t < 256.
Proof.
  intros.
  unfold encode_glob_symb_info.
  unfold encode_symbbind, encode_symbtype .
  destruct b;destruct t; lia.
Qed.


Definition encode_secindex (i:secindex) (idxmap: PTree.t Z): res (list byte) :=
  let shn_comm := HZ["FFF2"] in
  let shn_undef := 0 in 
  match i with
  | secindex_comm => OK (encode_int 2 shn_comm)
  | secindex_undef  => OK (encode_int 2 shn_undef)
  | secindex_normal id =>
    match idxmap ! id with
    | None => Error [MSG "Cannot find the index of the symbol "; CTX id]
    | Some idx =>
      if (0 <? idx) && (idx  <? HZ["FFF2"]) then
        OK (encode_int 2 idx)
      else
        Error (msg "Section index not in the range (1,FFF2)")
    end
  end.

Definition check_range32 (z: Z) :=
  (0 <=? z) &&  (z <? two_p 32).

Definition check_range64 (z: Z) :=
  (0 <=? z) &&  (z <? two_p 64).


(** Encode Symbol entry with related strtable index which is the index of symbol entry *)
(** eliminate the strtable checking: add name_index parameter which denote the index in strtb, arbitrary doesn't matter ? *)
Definition encode_symbentry32 (e:symbentry) (name_index: Z) (idxmap: PTree.t Z) : res (list byte) :=
  if check_range32 name_index && check_range32 (symbentry_value e) && check_range32 (symbentry_size e) then
    let st_name_bytes := encode_int32 name_index in 
    let st_value_bytes := encode_int32 (symbentry_value e) in
    let st_size_bytes := encode_int32 (symbentry_size e) in
    let st_info_bytes := 
        encode_int 1 (encode_glob_symb_info (symbentry_bind e) (symbentry_type e)) in
    let st_other_bytes := [Byte.repr 0] in
    do st_shndx_bytes <- encode_secindex (symbentry_secindex e) idxmap;
    OK (st_name_bytes ++ st_value_bytes ++ st_size_bytes ++
                      st_info_bytes ++ st_other_bytes ++ st_shndx_bytes)
  else Error (msg "encode_symbentry32 out of range").

Definition encode_symbentry64 (e:symbentry) (name_index: Z) (idxmap: PTree.t Z) : res (list byte) :=
  if check_range32 name_index && check_range64 (symbentry_value e) && check_range64 (symbentry_size e) then
  let st_name_bytes := encode_int32 name_index in 
  let st_value_bytes := encode_int64 (symbentry_value e) in
  let st_size_bytes := encode_int64 (symbentry_size e) in
  let st_info_bytes :=
      encode_int 1 (encode_glob_symb_info (symbentry_bind e) (symbentry_type e)) in
  let st_other_bytes := [Byte.repr 0] in
  do st_shndx_bytes <- encode_secindex (symbentry_secindex e) idxmap;
  OK (st_name_bytes ++ st_info_bytes ++ st_other_bytes ++ st_shndx_bytes ++ st_value_bytes ++ st_size_bytes)
  else Error (msg "encode_symbentry64 out of range").



Definition encode_dummy_symbentry32 : (list byte) :=
  let e := {| 
              symbentry_bind := bind_local;
              symbentry_type := symb_notype;
              symbentry_value := 0;
              symbentry_secindex := secindex_undef;
              symbentry_size := 0;
           |} in
  let st_name_bytes := encode_int32 0 in 
  let st_value_bytes := encode_int32 (symbentry_value e) in
  let st_size_bytes := encode_int32 (symbentry_size e) in
  let st_info_bytes := 
      encode_int 1 (encode_glob_symb_info (symbentry_bind e) (symbentry_type e)) in
  let st_other_bytes := [Byte.repr 0] in
  let st_shndx_bytes := encode_int 2 0 in
  (st_name_bytes ++ st_value_bytes ++ st_size_bytes ++
                 st_info_bytes ++ st_other_bytes ++ st_shndx_bytes).

Definition encode_dummy_symbentry64 : (list byte) :=
  let e := {| 
              symbentry_bind := bind_local;
              symbentry_type := symb_notype;
              symbentry_value := 0;
              symbentry_secindex := secindex_undef;
              symbentry_size := 0;
           |} in
  let st_name_bytes := encode_int32 0 in 
  let st_value_bytes := encode_int64 (symbentry_value e) in
  let st_size_bytes := encode_int64 (symbentry_size e) in
  let st_info_bytes := 
      encode_int 1 (encode_glob_symb_info (symbentry_bind e) (symbentry_type e)) in
  let st_other_bytes := [Byte.repr 0] in
  let st_shndx_bytes := encode_int 2 0 in
  (st_name_bytes ++ st_info_bytes ++ st_other_bytes ++ st_shndx_bytes ++ st_value_bytes ++ st_size_bytes).


Lemma encode_secindex_len: forall l i m,
    encode_secindex i m = OK l ->
    length l = 2%nat.
Proof.
  unfold encode_secindex.
  intros. destr_in H.
  destr_in H. destr_in H.
  inv H. rewrite encode_int_length. auto.
  inv H. rewrite encode_int_length. auto.
  inv H. rewrite encode_int_length. auto.
Qed.

Lemma encode_symbentry32_len: forall l e idx m,
    encode_symbentry32 e idx m = OK l ->
    length l = 16%nat.
Proof.
  unfold encode_symbentry32.
  intros. destr_in H.
  monadInv H.
  simpl. repeat rewrite app_length.
  unfold encode_int32. repeat rewrite encode_int_length.
  simpl. erewrite encode_secindex_len.
  auto. eauto.
Qed.


Lemma encode_symbentry64_len: forall l e idx m,
    encode_symbentry64 e idx m = OK l ->
    length l = 24%nat.
Proof.
  unfold encode_symbentry64.
  intros. destr_in H.
  monadInv H.
  simpl.
  repeat rewrite app_length. simpl.
  unfold encode_int32, encode_int64.
  repeat rewrite app_length.
  repeat rewrite encode_int_length.
  simpl. erewrite encode_secindex_len.
  auto. eauto.
Qed.


(** Transform the program *)
(* Definition transf_program p : res program := *)
(*   let t := prog_symbtable p in *)
(*   do s <- create_symbtable_section t; *)
(*   let p' := *)
(*       {| prog_defs := prog_defs p; *)
(*         prog_public := prog_public p; *)
(*         prog_main := prog_main p; *)
(*         prog_sectable := (prog_sectable p) ++ [s]; *)
(*         prog_symbtable := prog_symbtable p; *)
(*         prog_reloctables := prog_reloctables p; *)
(*         prog_senv := prog_senv p; *)
(*      |} in *)
(*   let len := (length (prog_sectable p')) in *)
(*   if beq_nat len 5 then *)
(*     OK p' *)
(*   else *)
(*     Error [MSG "In SymtableEncode: Number of sections is incorrect (not 5): "; POS (Pos.of_nat len)]. *)
