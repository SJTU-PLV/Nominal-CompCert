Require Import Coqlib Integers Errors.
Require Import encode.Hex encode.Bits Memdata.
Require Import Encode  VerificationCondition.
Import String Ascii.
Import List.
Import ListNotations.
Import Hex Bits.
Require Import BPProperty.
Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.





Definition write_B (REX:byte)  (B_value:bits) : byte :=
	let REX_bits := bytes_to_bits_opt[REX] in
	bB[(REX_bits~@[7])++B_value].

Definition read_B (REX:byte) : bits :=
	let REX_bits := bytes_to_bits_opt[REX] in
	(REX_bits>@[7]).

Lemma read_write_B: 
forall token field,
length field = 1-> 
read_B (write_B token field) = field.
Proof.
intros token field HL;destr_byte token; destr_list field;unfold read_B;unfold write_B;repeat everything.
Qed.

Definition write_R (REX:byte)  (R_value:bits) : byte :=
	let REX_bits := bytes_to_bits_opt[REX] in
	bB[(REX_bits~@[5])++R_value++(REX_bits>@[6])].

Definition read_R (REX:byte) : bits :=
	let REX_bits := bytes_to_bits_opt[REX] in
	(REX_bits>@[5])~@[1].

Lemma read_write_R: 
forall token field,
length field = 1-> 
read_R (write_R token field) = field.
Proof.
intros token field HL;destr_byte token; destr_list field;unfold read_R;unfold write_R;repeat everything.
Qed.

Definition write_W (REX:byte)  (W_value:bits) : byte :=
	let REX_bits := bytes_to_bits_opt[REX] in
	bB[(REX_bits~@[4])++W_value++(REX_bits>@[5])].

Definition read_W (REX:byte) : bits :=
	let REX_bits := bytes_to_bits_opt[REX] in
	(REX_bits>@[4])~@[1].

Lemma read_write_W: 
forall token field,
length field = 1-> 
read_W (write_W token field) = field.
Proof.
intros token field HL;destr_byte token; destr_list field;unfold read_W;unfold write_W;repeat everything.
Qed.

Definition write_X (REX:byte)  (X_value:bits) : byte :=
	let REX_bits := bytes_to_bits_opt[REX] in
	bB[(REX_bits~@[6])++X_value++(REX_bits>@[7])].

Definition read_X (REX:byte) : bits :=
	let REX_bits := bytes_to_bits_opt[REX] in
	(REX_bits>@[6])~@[1].

Lemma read_write_X: 
forall token field,
length field = 1-> 
read_X (write_X token field) = field.
Proof.
intros token field HL;destr_byte token; destr_list field;unfold read_X;unfold write_X;repeat everything.
Qed.

Definition write_base (SIB:byte)  (base_value:bits) : byte :=
	let SIB_bits := bytes_to_bits_opt[SIB] in
	bB[(SIB_bits~@[5])++base_value].

Definition read_base (SIB:byte) : bits :=
	let SIB_bits := bytes_to_bits_opt[SIB] in
	(SIB_bits>@[5]).

Lemma read_write_base: 
forall token field,
length field = 3-> 
read_base (write_base token field) = field.
Proof.
intros token field HL;destr_byte token; destr_list field;unfold read_base;unfold write_base;repeat everything.
Qed.

Definition write_cccode (condi:byte)  (cccode_value:bits) : byte :=
	let condi_bits := bytes_to_bits_opt[condi] in
	bB[(condi_bits~@[4])++cccode_value].

Definition read_cccode (condi:byte) : bits :=
	let condi_bits := bytes_to_bits_opt[condi] in
	(condi_bits>@[4]).

Lemma read_write_cccode: 
forall token field,
length field = 4-> 
read_cccode (write_cccode token field) = field.
Proof.
intros token field HL;destr_byte token; destr_list field;unfold read_cccode;unfold write_cccode;repeat everything.
Qed.

Definition write_col (Opcode:byte)  (col_value:bits) : byte :=
	let Opcode_bits := bytes_to_bits_opt[Opcode] in
	bB[(Opcode_bits~@[5])++col_value].

Definition read_col (Opcode:byte) : bits :=
	let Opcode_bits := bytes_to_bits_opt[Opcode] in
	(Opcode_bits>@[5]).

Lemma read_write_col: 
forall token field,
length field = 3-> 
read_col (write_col token field) = field.
Proof.
intros token field HL;destr_byte token; destr_list field;unfold read_col;unfold write_col;repeat everything.
Qed.

Definition write_cprefix (condi:byte)  (cprefix_value:bits) : byte :=
	let condi_bits := bytes_to_bits_opt[condi] in
	bB[cprefix_value++(condi_bits>@[4])].

Definition read_cprefix (condi:byte) : bits :=
	let condi_bits := bytes_to_bits_opt[condi] in
	condi_bits~@[4].

Lemma read_write_cprefix: 
forall token field,
length field = 4-> 
read_cprefix (write_cprefix token field) = field.
Proof.
intros token field HL;destr_byte token; destr_list field;unfold read_cprefix;unfold write_cprefix;repeat everything.
Qed.

Definition write_index (SIB:byte)  (index_value:bits) : byte :=
	let SIB_bits := bytes_to_bits_opt[SIB] in
	bB[(SIB_bits~@[2])++index_value++(SIB_bits>@[5])].

Definition read_index (SIB:byte) : bits :=
	let SIB_bits := bytes_to_bits_opt[SIB] in
	(SIB_bits>@[2])~@[3].

Lemma read_write_index: 
forall token field,
length field = 3-> 
read_index (write_index token field) = field.
Proof.
intros token field HL;destr_byte token; destr_list field;unfold read_index;unfold write_index;repeat everything.
Qed.

Definition write_mod (ModRM:byte)  (mod_value:bits) : byte :=
	let ModRM_bits := bytes_to_bits_opt[ModRM] in
	bB[mod_value++(ModRM_bits>@[2])].

Definition read_mod (ModRM:byte) : bits :=
	let ModRM_bits := bytes_to_bits_opt[ModRM] in
	ModRM_bits~@[2].

Lemma read_write_mod: 
forall token field,
length field = 2-> 
read_mod (write_mod token field) = field.
Proof.
intros token field HL;destr_byte token; destr_list field;unfold read_mod;unfold write_mod;repeat everything.
Qed.

Definition write_page (Opcode:byte)  (page_value:bits) : byte :=
	let Opcode_bits := bytes_to_bits_opt[Opcode] in
	bB[(Opcode_bits~@[4])++page_value++(Opcode_bits>@[5])].

Definition read_page (Opcode:byte) : bits :=
	let Opcode_bits := bytes_to_bits_opt[Opcode] in
	(Opcode_bits>@[4])~@[1].

Lemma read_write_page: 
forall token field,
length field = 1-> 
read_page (write_page token field) = field.
Proof.
intros token field HL;destr_byte token; destr_list field;unfold read_page;unfold write_page;repeat everything.
Qed.

Definition write_reg_op (ModRM:byte)  (reg_op_value:bits) : byte :=
	let ModRM_bits := bytes_to_bits_opt[ModRM] in
	bB[(ModRM_bits~@[2])++reg_op_value++(ModRM_bits>@[5])].

Definition read_reg_op (ModRM:byte) : bits :=
	let ModRM_bits := bytes_to_bits_opt[ModRM] in
	(ModRM_bits>@[2])~@[3].

Lemma read_write_reg_op: 
forall token field,
length field = 3-> 
read_reg_op (write_reg_op token field) = field.
Proof.
intros token field HL;destr_byte token; destr_list field;unfold read_reg_op;unfold write_reg_op;repeat everything.
Qed.

Definition write_rm (ModRM:byte)  (rm_value:bits) : byte :=
	let ModRM_bits := bytes_to_bits_opt[ModRM] in
	bB[(ModRM_bits~@[5])++rm_value].

Definition read_rm (ModRM:byte) : bits :=
	let ModRM_bits := bytes_to_bits_opt[ModRM] in
	(ModRM_bits>@[5]).

Lemma read_write_rm: 
forall token field,
length field = 3-> 
read_rm (write_rm token field) = field.
Proof.
intros token field HL;destr_byte token; destr_list field;unfold read_rm;unfold write_rm;repeat everything.
Qed.

Definition write_rmagic (REX:byte)  (rmagic_value:bits) : byte :=
	let REX_bits := bytes_to_bits_opt[REX] in
	bB[rmagic_value++(REX_bits>@[4])].

Definition read_rmagic (REX:byte) : bits :=
	let REX_bits := bytes_to_bits_opt[REX] in
	REX_bits~@[4].

Lemma read_write_rmagic: 
forall token field,
length field = 4-> 
read_rmagic (write_rmagic token field) = field.
Proof.
intros token field HL;destr_byte token; destr_list field;unfold read_rmagic;unfold write_rmagic;repeat everything.
Qed.

Definition write_row (Opcode:byte)  (row_value:bits) : byte :=
	let Opcode_bits := bytes_to_bits_opt[Opcode] in
	bB[row_value++(Opcode_bits>@[4])].

Definition read_row (Opcode:byte) : bits :=
	let Opcode_bits := bytes_to_bits_opt[Opcode] in
	Opcode_bits~@[4].

Lemma read_write_row: 
forall token field,
length field = 4-> 
read_row (write_row token field) = field.
Proof.
intros token field HL;destr_byte token; destr_list field;unfold read_row;unfold write_row;repeat everything.
Qed.

Definition write_scale (SIB:byte)  (scale_value:bits) : byte :=
	let SIB_bits := bytes_to_bits_opt[SIB] in
	bB[scale_value++(SIB_bits>@[2])].

Definition read_scale (SIB:byte) : bits :=
	let SIB_bits := bytes_to_bits_opt[SIB] in
	SIB_bits~@[2].

Lemma read_write_scale: 
forall token field,
length field = 2-> 
read_scale (write_scale token field) = field.
Proof.
intros token field HL;destr_byte token; destr_list field;unfold read_scale;unfold write_scale;repeat everything.
Qed.


Hint Resolve read_write_B read_write_R read_write_W read_write_X read_write_base read_write_cccode read_write_col read_write_cprefix read_write_index read_write_mod read_write_page read_write_reg_op read_write_rm read_write_rmagic read_write_row read_write_scale:bitfields.
Hint Unfold read_B write_B read_R write_R read_W write_W read_X write_X read_base write_base read_cccode write_cccode read_col write_col read_cprefix write_cprefix read_index write_index read_mod write_mod read_page write_page read_reg_op write_reg_op read_rm write_rm read_rmagic write_rmagic read_row write_row read_scale write_scale:bitfields.

Hint Unfold AddrE11_bp AddrE9_bp AddrE5_bp AddrE0_bp :AddrE_bpdb.

Hint Unfold REX_WRXB_bp Override_bp REP_bp REPNZ_bp Psubl_ri_bp Pbsqrtsd_bp Psbbl_rr_bp Prep_movsl_bp Pmovsq_rm_bp Pmovsq_mr_bp Pminsd_bp Pmaxsd_bp Pbswap32_bp Pbsrl_bp Pbsfl_bp Paddl_mi_bp Paddl_GvEv_bp Paddl_EvGv_bp Padcl_rr_bp Padcl_ri_bp Pjcc_rel_bp Pret_iw_bp Pret_bp Pcall_r_bp Pcall_ofs_bp Pnop_bp Pjmp_Ev_bp Pjmp_l_rel_bp Pxorps_d_GvEv_bp Pcomiss_d_ff_bp Pdivss_d_ff_bp Pmuls_d_ff_bp Psubs_d_ff_bp Pandps_d_fm_bp Padds_d_ff_bp Psetcc_bp Pcmov_bp Ptestl_EvGv_bp Ptestl_ri_bp Pcmpl_ri_bp Pcmpl_GvEv_bp Pcmpl_EvGv_bp Prorl_ri_bp Prolw_ri_bp Pshld_ri_bp Psarl_rcl_bp Psarl_ri_bp Pshrl_rcl_bp Pshrl_ri_bp Psall_rcl_bp Psall_ri_bp Pnotl_bp Pxorl_GvEv_bp Pxorl_EvGv_bp Pxorl_ri_bp Porl_GvEv_bp Porl_EvGv_bp Porl_ri_bp Pandl_ri_bp Pandl_GvEv_bp Pandl_EvGv_bp Pidivl_r_bp Pdivl_r_bp Pcltd_bp Pmull_r_bp Pimull_r_bp Pimull_ri_bp Pimull_GvEv_bp Psubl_GvEv_bp Psubl_EvGv_bp Paddl_ri_bp Pnegl_bp Pleal_bp Pcvtsi2ss_d_fr_bp Pcvttss_d_2si_rf_bp Pcvtsd2ss_d_ff_bp Pmovsxd_GvEv_bp Pmovsw_GvEv_bp Pmovzw_GvEv_bp Pmovsb_GvEv_bp Pmovzb_rm_bp Pmovb_rm_bp Pmovb_mr_bp Pxchg_rr_bp Pflds_m_bp Pfstps_m_bp Pfstpl_m_bp Pfldl_m_bp Pmovss_d_fm_bp Pmovss_d_mf_bp Pmovl_rm_bp Pmovl_mr_bp Pmovl_ri_bp :Instruction_bpdb.
Lemma AddrE_bp_in_list0: 
In AddrE11_bp AddrE_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma AddrE_bp_in_list1: 
In AddrE9_bp AddrE_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma AddrE_bp_in_list2: 
In AddrE5_bp AddrE_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma AddrE_bp_in_list3: 
In AddrE0_bp AddrE_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list0: 
In REX_WRXB_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list1: 
In Override_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list2: 
In REP_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list3: 
In REPNZ_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list4: 
In Psubl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list5: 
In Pbsqrtsd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list6: 
In Psbbl_rr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list7: 
In Prep_movsl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list8: 
In Pmovsq_rm_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list9: 
In Pmovsq_mr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list10: 
In Pminsd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list11: 
In Pmaxsd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list12: 
In Pbswap32_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list13: 
In Pbsrl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list14: 
In Pbsfl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list15: 
In Paddl_mi_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list16: 
In Paddl_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list17: 
In Paddl_EvGv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list18: 
In Padcl_rr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list19: 
In Padcl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list20: 
In Pjcc_rel_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list21: 
In Pret_iw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list22: 
In Pret_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list23: 
In Pcall_r_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list24: 
In Pcall_ofs_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list25: 
In Pnop_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list26: 
In Pjmp_Ev_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list27: 
In Pjmp_l_rel_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list28: 
In Pxorps_d_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list29: 
In Pcomiss_d_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list30: 
In Pdivss_d_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list31: 
In Pmuls_d_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list32: 
In Psubs_d_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list33: 
In Pandps_d_fm_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list34: 
In Padds_d_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list35: 
In Psetcc_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list36: 
In Pcmov_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list37: 
In Ptestl_EvGv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list38: 
In Ptestl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list39: 
In Pcmpl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list40: 
In Pcmpl_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list41: 
In Pcmpl_EvGv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list42: 
In Prorl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list43: 
In Prolw_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list44: 
In Pshld_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list45: 
In Psarl_rcl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list46: 
In Psarl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list47: 
In Pshrl_rcl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list48: 
In Pshrl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list49: 
In Psall_rcl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list50: 
In Psall_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list51: 
In Pnotl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list52: 
In Pxorl_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list53: 
In Pxorl_EvGv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list54: 
In Pxorl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list55: 
In Porl_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list56: 
In Porl_EvGv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list57: 
In Porl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list58: 
In Pandl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list59: 
In Pandl_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list60: 
In Pandl_EvGv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list61: 
In Pidivl_r_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list62: 
In Pdivl_r_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list63: 
In Pcltd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list64: 
In Pmull_r_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list65: 
In Pimull_r_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list66: 
In Pimull_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list67: 
In Pimull_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list68: 
In Psubl_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list69: 
In Psubl_EvGv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list70: 
In Paddl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list71: 
In Pnegl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list72: 
In Pleal_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list73: 
In Pcvtsi2ss_d_fr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list74: 
In Pcvttss_d_2si_rf_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list75: 
In Pcvtsd2ss_d_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list76: 
In Pmovsxd_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list77: 
In Pmovsw_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list78: 
In Pmovzw_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list79: 
In Pmovsb_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list80: 
In Pmovzb_rm_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list81: 
In Pmovb_rm_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list82: 
In Pmovb_mr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list83: 
In Pxchg_rr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list84: 
In Pflds_m_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list85: 
In Pfstps_m_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list86: 
In Pfstpl_m_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list87: 
In Pfldl_m_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list88: 
In Pmovss_d_fm_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list89: 
In Pmovss_d_mf_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list90: 
In Pmovl_rm_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list91: 
In Pmovl_mr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list92: 
In Pmovl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Inductive AddrE: Type :=
| AddrE11(uvar32_0:u32)
| AddrE9(uvar2_0:u2)(uvar3_1:u3)(uvar32_2:u32)
| AddrE5(uvar2_0:u2)(uvar3_1:u3)(uvar3_2:u3)(uvar32_3:u32)
| AddrE0(uvar3_0:u3).
Inductive AddrE_op: Type :=
| AddrE11_op
| AddrE9_op
| AddrE5_op
| AddrE0_op.
Definition AddrE_to_op element  :=
	match element with
| AddrE11 _ => AddrE11_op
| AddrE9 _ _ _ => AddrE9_op
| AddrE5 _ _ _ _ => AddrE5_op
| AddrE0 _ => AddrE0_op
end.
Definition AddrE_op_to_bp element  :=
	match element with
| AddrE11_op => AddrE11_bp
| AddrE9_op => AddrE9_bp
| AddrE5_op => AddrE5_bp
| AddrE0_op => AddrE0_bp
end.
Definition encode_AddrE element  inByte  :=
	match element with
| AddrE11 uvar32_0 => let byte00 := inByte in
let byte01 := write_mod byte00 b["00"] in
let byte02 := write_rm byte01 b["101"] in
let result0 := [byte02] in
do byte11 <- bits_to_bytes (proj1_sig uvar32_0);
let result1 := byte11 in
OK (result0 ++ result1)
| AddrE9 uvar2_0 uvar3_1 uvar32_2 => let byte00 := inByte in
let byte01 := write_mod byte00 b["00"] in
let byte02 := write_rm byte01 b["100"] in
let result0 := [byte02] in
let byte10 := HB["00"] in
let byte11 := write_base byte10 b["101"] in
let byte12 := write_scale byte11 (proj1_sig uvar2_0) in
let byte13 := write_index byte12 (proj1_sig uvar3_1) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar32_2);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| AddrE5 uvar2_0 uvar3_1 uvar3_2 uvar32_3 => let byte00 := inByte in
let byte01 := write_mod byte00 b["10"] in
let byte02 := write_rm byte01 b["100"] in
let result0 := [byte02] in
let byte10 := HB["00"] in
let byte11 := write_scale byte10 (proj1_sig uvar2_0) in
let byte12 := write_index byte11 (proj1_sig uvar3_1) in
let byte13 := write_base byte12 (proj1_sig uvar3_2) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar32_3);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| AddrE0 uvar3_0 => let byte00 := inByte in
let byte01 := write_mod byte00 b["11"] in
let byte02 := write_rm byte01 (proj1_sig uvar3_0) in
let result0 := [byte02] in
OK (result0)
end.

Program Definition decode_AddrE code : res (AddrE*nat) :=
	let bin := bytes_to_bits_opt code in
	if AddrE11_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte_seq0 <- try_first_n bytes1 4;
let uvar32_0 := bytes_to_bits_opt byte_seq0 in
if assertLength uvar32_0 32 then
do bytes2 <- try_skip_n bytes1 4;
OK ((AddrE11 (uvar32_0)), 5)
else Error(msg"impossible")
else

	if AddrE9_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar2_0 := read_scale byte0 in
if assertLength uvar2_0 2 then
let uvar3_1 := read_index byte0 in
if assertLength uvar3_1 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 4;
let uvar32_2 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_2 32 then
do bytes3 <- try_skip_n bytes2 4;
OK ((AddrE9 (uvar2_0) (uvar3_1) (uvar32_2)), 6)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if AddrE5_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar2_0 := read_scale byte0 in
if assertLength uvar2_0 2 then
let uvar3_1 := read_index byte0 in
if assertLength uvar3_1 3 then
let uvar3_2 := read_base byte0 in
if assertLength uvar3_2 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 4;
let uvar32_3 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_3 32 then
do bytes3 <- try_skip_n bytes2 4;
OK ((AddrE5 (uvar2_0) (uvar3_1) (uvar3_2) (uvar32_3)), 6)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if AddrE0_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes1 <- try_skip_n bytes0 1;
OK ((AddrE0 (uvar3_0)), 1)
else Error(msg"impossible")
else

	Error(msg"Unsupported AddrE").

Inductive Instruction: Type :=
| REX_WRXB(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar1_3:u1)
| Override
| REP
| REPNZ
| Psubl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pbsqrtsd(uvar3_0:u3)(uvar3_1:u3)
| Psbbl_rr(uvar3_0:u3)(uvar3_1:u3)
| Prep_movsl
| Pmovsq_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovsq_mr(AddrE:AddrE)(uvar3_0:u3)
| Pminsd(uvar3_0:u3)(uvar3_1:u3)
| Pmaxsd(uvar3_0:u3)(uvar3_1:u3)
| Pbswap32(uvar3_0:u3)
| Pbsrl(uvar3_0:u3)(uvar3_1:u3)
| Pbsfl(uvar3_0:u3)(uvar3_1:u3)
| Paddl_mi(AddrE:AddrE)(uvar32_1:u32)
| Paddl_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Paddl_EvGv(AddrE:AddrE)(uvar3_0:u3)
| Padcl_rr(uvar3_0:u3)(uvar3_1:u3)
| Padcl_ri(uvar3_0:u3)(uvar8_1:u8)
| Pjcc_rel(uvar4_0:u4)(uvar32_1:u32)
| Pret_iw(uvar16_0:u16)
| Pret
| Pcall_r(uvar3_0:u3)
| Pcall_ofs(uvar32_0:u32)
| Pnop
| Pjmp_Ev(AddrE:AddrE)
| Pjmp_l_rel(uvar32_0:u32)
| Pxorps_d_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pcomiss_d_ff(uvar3_0:u3)(uvar3_1:u3)
| Pdivss_d_ff(uvar3_0:u3)(uvar3_1:u3)
| Pmuls_d_ff(uvar3_0:u3)(uvar3_1:u3)
| Psubs_d_ff(uvar3_0:u3)(uvar3_1:u3)
| Pandps_d_fm(AddrE:AddrE)(uvar3_0:u3)
| Padds_d_ff(uvar3_0:u3)(uvar3_1:u3)
| Psetcc(uvar4_0:u4)(uvar3_1:u3)
| Pcmov(uvar4_0:u4)(uvar3_1:u3)(uvar3_2:u3)
| Ptestl_EvGv(AddrE:AddrE)(uvar3_0:u3)
| Ptestl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pcmpl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pcmpl_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pcmpl_EvGv(AddrE:AddrE)(uvar3_0:u3)
| Prorl_ri(uvar3_0:u3)(uvar8_1:u8)
| Prolw_ri(uvar3_0:u3)(uvar8_1:u8)
| Pshld_ri(uvar3_0:u3)(uvar3_1:u3)(uvar8_2:u8)
| Psarl_rcl(uvar3_0:u3)
| Psarl_ri(uvar3_0:u3)(uvar8_1:u8)
| Pshrl_rcl(uvar3_0:u3)
| Pshrl_ri(uvar3_0:u3)(uvar8_1:u8)
| Psall_rcl(uvar3_0:u3)
| Psall_ri(uvar3_0:u3)(uvar8_1:u8)
| Pnotl(uvar3_0:u3)
| Pxorl_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pxorl_EvGv(AddrE:AddrE)(uvar3_0:u3)
| Pxorl_ri(uvar3_0:u3)(uvar32_1:u32)
| Porl_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Porl_EvGv(AddrE:AddrE)(uvar3_0:u3)
| Porl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pandl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pandl_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pandl_EvGv(AddrE:AddrE)(uvar3_0:u3)
| Pidivl_r(uvar3_0:u3)
| Pdivl_r(uvar3_0:u3)
| Pcltd
| Pmull_r(uvar3_0:u3)
| Pimull_r(uvar3_0:u3)
| Pimull_ri(uvar3_0:u3)(uvar3_1:u3)(uvar32_2:u32)
| Pimull_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Psubl_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Psubl_EvGv(AddrE:AddrE)(uvar3_0:u3)
| Paddl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pnegl(uvar3_0:u3)
| Pleal(AddrE:AddrE)(uvar3_0:u3)
| Pcvtsi2ss_d_fr(uvar3_0:u3)(uvar3_1:u3)
| Pcvttss_d_2si_rf(uvar3_0:u3)(uvar3_1:u3)
| Pcvtsd2ss_d_ff(uvar3_0:u3)(uvar3_1:u3)
| Pmovsxd_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pmovsw_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pmovzw_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pmovsb_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pmovzb_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovb_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovb_mr(AddrE:AddrE)(uvar3_0:u3)
| Pxchg_rr(uvar3_0:u3)(uvar3_1:u3)
| Pflds_m(AddrE:AddrE)
| Pfstps_m(AddrE:AddrE)
| Pfstpl_m(AddrE:AddrE)
| Pfldl_m(AddrE:AddrE)
| Pmovss_d_fm(AddrE:AddrE)(uvar3_0:u3)
| Pmovss_d_mf(AddrE:AddrE)(uvar3_0:u3)
| Pmovl_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovl_mr(AddrE:AddrE)(uvar3_0:u3)
| Pmovl_ri(uvar3_0:u3)(uvar32_1:u32).
Inductive Instruction_op: Type :=
| REX_WRXB_op
| Override_op
| REP_op
| REPNZ_op
| Psubl_ri_op
| Pbsqrtsd_op
| Psbbl_rr_op
| Prep_movsl_op
| Pmovsq_rm_op
| Pmovsq_mr_op
| Pminsd_op
| Pmaxsd_op
| Pbswap32_op
| Pbsrl_op
| Pbsfl_op
| Paddl_mi_op
| Paddl_GvEv_op
| Paddl_EvGv_op
| Padcl_rr_op
| Padcl_ri_op
| Pjcc_rel_op
| Pret_iw_op
| Pret_op
| Pcall_r_op
| Pcall_ofs_op
| Pnop_op
| Pjmp_Ev_op
| Pjmp_l_rel_op
| Pxorps_d_GvEv_op
| Pcomiss_d_ff_op
| Pdivss_d_ff_op
| Pmuls_d_ff_op
| Psubs_d_ff_op
| Pandps_d_fm_op
| Padds_d_ff_op
| Psetcc_op
| Pcmov_op
| Ptestl_EvGv_op
| Ptestl_ri_op
| Pcmpl_ri_op
| Pcmpl_GvEv_op
| Pcmpl_EvGv_op
| Prorl_ri_op
| Prolw_ri_op
| Pshld_ri_op
| Psarl_rcl_op
| Psarl_ri_op
| Pshrl_rcl_op
| Pshrl_ri_op
| Psall_rcl_op
| Psall_ri_op
| Pnotl_op
| Pxorl_GvEv_op
| Pxorl_EvGv_op
| Pxorl_ri_op
| Porl_GvEv_op
| Porl_EvGv_op
| Porl_ri_op
| Pandl_ri_op
| Pandl_GvEv_op
| Pandl_EvGv_op
| Pidivl_r_op
| Pdivl_r_op
| Pcltd_op
| Pmull_r_op
| Pimull_r_op
| Pimull_ri_op
| Pimull_GvEv_op
| Psubl_GvEv_op
| Psubl_EvGv_op
| Paddl_ri_op
| Pnegl_op
| Pleal_op
| Pcvtsi2ss_d_fr_op
| Pcvttss_d_2si_rf_op
| Pcvtsd2ss_d_ff_op
| Pmovsxd_GvEv_op
| Pmovsw_GvEv_op
| Pmovzw_GvEv_op
| Pmovsb_GvEv_op
| Pmovzb_rm_op
| Pmovb_rm_op
| Pmovb_mr_op
| Pxchg_rr_op
| Pflds_m_op
| Pfstps_m_op
| Pfstpl_m_op
| Pfldl_m_op
| Pmovss_d_fm_op
| Pmovss_d_mf_op
| Pmovl_rm_op
| Pmovl_mr_op
| Pmovl_ri_op.
Definition Instruction_to_op element  :=
	match element with
| REX_WRXB _ _ _ _ => REX_WRXB_op
| Override => Override_op
| REP => REP_op
| REPNZ => REPNZ_op
| Psubl_ri _ _ => Psubl_ri_op
| Pbsqrtsd _ _ => Pbsqrtsd_op
| Psbbl_rr _ _ => Psbbl_rr_op
| Prep_movsl => Prep_movsl_op
| Pmovsq_rm _ _ => Pmovsq_rm_op
| Pmovsq_mr _ _ => Pmovsq_mr_op
| Pminsd _ _ => Pminsd_op
| Pmaxsd _ _ => Pmaxsd_op
| Pbswap32 _ => Pbswap32_op
| Pbsrl _ _ => Pbsrl_op
| Pbsfl _ _ => Pbsfl_op
| Paddl_mi _ _ => Paddl_mi_op
| Paddl_GvEv _ _ => Paddl_GvEv_op
| Paddl_EvGv _ _ => Paddl_EvGv_op
| Padcl_rr _ _ => Padcl_rr_op
| Padcl_ri _ _ => Padcl_ri_op
| Pjcc_rel _ _ => Pjcc_rel_op
| Pret_iw _ => Pret_iw_op
| Pret => Pret_op
| Pcall_r _ => Pcall_r_op
| Pcall_ofs _ => Pcall_ofs_op
| Pnop => Pnop_op
| Pjmp_Ev _ => Pjmp_Ev_op
| Pjmp_l_rel _ => Pjmp_l_rel_op
| Pxorps_d_GvEv _ _ => Pxorps_d_GvEv_op
| Pcomiss_d_ff _ _ => Pcomiss_d_ff_op
| Pdivss_d_ff _ _ => Pdivss_d_ff_op
| Pmuls_d_ff _ _ => Pmuls_d_ff_op
| Psubs_d_ff _ _ => Psubs_d_ff_op
| Pandps_d_fm _ _ => Pandps_d_fm_op
| Padds_d_ff _ _ => Padds_d_ff_op
| Psetcc _ _ => Psetcc_op
| Pcmov _ _ _ => Pcmov_op
| Ptestl_EvGv _ _ => Ptestl_EvGv_op
| Ptestl_ri _ _ => Ptestl_ri_op
| Pcmpl_ri _ _ => Pcmpl_ri_op
| Pcmpl_GvEv _ _ => Pcmpl_GvEv_op
| Pcmpl_EvGv _ _ => Pcmpl_EvGv_op
| Prorl_ri _ _ => Prorl_ri_op
| Prolw_ri _ _ => Prolw_ri_op
| Pshld_ri _ _ _ => Pshld_ri_op
| Psarl_rcl _ => Psarl_rcl_op
| Psarl_ri _ _ => Psarl_ri_op
| Pshrl_rcl _ => Pshrl_rcl_op
| Pshrl_ri _ _ => Pshrl_ri_op
| Psall_rcl _ => Psall_rcl_op
| Psall_ri _ _ => Psall_ri_op
| Pnotl _ => Pnotl_op
| Pxorl_GvEv _ _ => Pxorl_GvEv_op
| Pxorl_EvGv _ _ => Pxorl_EvGv_op
| Pxorl_ri _ _ => Pxorl_ri_op
| Porl_GvEv _ _ => Porl_GvEv_op
| Porl_EvGv _ _ => Porl_EvGv_op
| Porl_ri _ _ => Porl_ri_op
| Pandl_ri _ _ => Pandl_ri_op
| Pandl_GvEv _ _ => Pandl_GvEv_op
| Pandl_EvGv _ _ => Pandl_EvGv_op
| Pidivl_r _ => Pidivl_r_op
| Pdivl_r _ => Pdivl_r_op
| Pcltd => Pcltd_op
| Pmull_r _ => Pmull_r_op
| Pimull_r _ => Pimull_r_op
| Pimull_ri _ _ _ => Pimull_ri_op
| Pimull_GvEv _ _ => Pimull_GvEv_op
| Psubl_GvEv _ _ => Psubl_GvEv_op
| Psubl_EvGv _ _ => Psubl_EvGv_op
| Paddl_ri _ _ => Paddl_ri_op
| Pnegl _ => Pnegl_op
| Pleal _ _ => Pleal_op
| Pcvtsi2ss_d_fr _ _ => Pcvtsi2ss_d_fr_op
| Pcvttss_d_2si_rf _ _ => Pcvttss_d_2si_rf_op
| Pcvtsd2ss_d_ff _ _ => Pcvtsd2ss_d_ff_op
| Pmovsxd_GvEv _ _ => Pmovsxd_GvEv_op
| Pmovsw_GvEv _ _ => Pmovsw_GvEv_op
| Pmovzw_GvEv _ _ => Pmovzw_GvEv_op
| Pmovsb_GvEv _ _ => Pmovsb_GvEv_op
| Pmovzb_rm _ _ => Pmovzb_rm_op
| Pmovb_rm _ _ => Pmovb_rm_op
| Pmovb_mr _ _ => Pmovb_mr_op
| Pxchg_rr _ _ => Pxchg_rr_op
| Pflds_m _ => Pflds_m_op
| Pfstps_m _ => Pfstps_m_op
| Pfstpl_m _ => Pfstpl_m_op
| Pfldl_m _ => Pfldl_m_op
| Pmovss_d_fm _ _ => Pmovss_d_fm_op
| Pmovss_d_mf _ _ => Pmovss_d_mf_op
| Pmovl_rm _ _ => Pmovl_rm_op
| Pmovl_mr _ _ => Pmovl_mr_op
| Pmovl_ri _ _ => Pmovl_ri_op
end.
Definition Instruction_op_to_bp element  :=
	match element with
| REX_WRXB_op => REX_WRXB_bp
| Override_op => Override_bp
| REP_op => REP_bp
| REPNZ_op => REPNZ_bp
| Psubl_ri_op => Psubl_ri_bp
| Pbsqrtsd_op => Pbsqrtsd_bp
| Psbbl_rr_op => Psbbl_rr_bp
| Prep_movsl_op => Prep_movsl_bp
| Pmovsq_rm_op => Pmovsq_rm_bp
| Pmovsq_mr_op => Pmovsq_mr_bp
| Pminsd_op => Pminsd_bp
| Pmaxsd_op => Pmaxsd_bp
| Pbswap32_op => Pbswap32_bp
| Pbsrl_op => Pbsrl_bp
| Pbsfl_op => Pbsfl_bp
| Paddl_mi_op => Paddl_mi_bp
| Paddl_GvEv_op => Paddl_GvEv_bp
| Paddl_EvGv_op => Paddl_EvGv_bp
| Padcl_rr_op => Padcl_rr_bp
| Padcl_ri_op => Padcl_ri_bp
| Pjcc_rel_op => Pjcc_rel_bp
| Pret_iw_op => Pret_iw_bp
| Pret_op => Pret_bp
| Pcall_r_op => Pcall_r_bp
| Pcall_ofs_op => Pcall_ofs_bp
| Pnop_op => Pnop_bp
| Pjmp_Ev_op => Pjmp_Ev_bp
| Pjmp_l_rel_op => Pjmp_l_rel_bp
| Pxorps_d_GvEv_op => Pxorps_d_GvEv_bp
| Pcomiss_d_ff_op => Pcomiss_d_ff_bp
| Pdivss_d_ff_op => Pdivss_d_ff_bp
| Pmuls_d_ff_op => Pmuls_d_ff_bp
| Psubs_d_ff_op => Psubs_d_ff_bp
| Pandps_d_fm_op => Pandps_d_fm_bp
| Padds_d_ff_op => Padds_d_ff_bp
| Psetcc_op => Psetcc_bp
| Pcmov_op => Pcmov_bp
| Ptestl_EvGv_op => Ptestl_EvGv_bp
| Ptestl_ri_op => Ptestl_ri_bp
| Pcmpl_ri_op => Pcmpl_ri_bp
| Pcmpl_GvEv_op => Pcmpl_GvEv_bp
| Pcmpl_EvGv_op => Pcmpl_EvGv_bp
| Prorl_ri_op => Prorl_ri_bp
| Prolw_ri_op => Prolw_ri_bp
| Pshld_ri_op => Pshld_ri_bp
| Psarl_rcl_op => Psarl_rcl_bp
| Psarl_ri_op => Psarl_ri_bp
| Pshrl_rcl_op => Pshrl_rcl_bp
| Pshrl_ri_op => Pshrl_ri_bp
| Psall_rcl_op => Psall_rcl_bp
| Psall_ri_op => Psall_ri_bp
| Pnotl_op => Pnotl_bp
| Pxorl_GvEv_op => Pxorl_GvEv_bp
| Pxorl_EvGv_op => Pxorl_EvGv_bp
| Pxorl_ri_op => Pxorl_ri_bp
| Porl_GvEv_op => Porl_GvEv_bp
| Porl_EvGv_op => Porl_EvGv_bp
| Porl_ri_op => Porl_ri_bp
| Pandl_ri_op => Pandl_ri_bp
| Pandl_GvEv_op => Pandl_GvEv_bp
| Pandl_EvGv_op => Pandl_EvGv_bp
| Pidivl_r_op => Pidivl_r_bp
| Pdivl_r_op => Pdivl_r_bp
| Pcltd_op => Pcltd_bp
| Pmull_r_op => Pmull_r_bp
| Pimull_r_op => Pimull_r_bp
| Pimull_ri_op => Pimull_ri_bp
| Pimull_GvEv_op => Pimull_GvEv_bp
| Psubl_GvEv_op => Psubl_GvEv_bp
| Psubl_EvGv_op => Psubl_EvGv_bp
| Paddl_ri_op => Paddl_ri_bp
| Pnegl_op => Pnegl_bp
| Pleal_op => Pleal_bp
| Pcvtsi2ss_d_fr_op => Pcvtsi2ss_d_fr_bp
| Pcvttss_d_2si_rf_op => Pcvttss_d_2si_rf_bp
| Pcvtsd2ss_d_ff_op => Pcvtsd2ss_d_ff_bp
| Pmovsxd_GvEv_op => Pmovsxd_GvEv_bp
| Pmovsw_GvEv_op => Pmovsw_GvEv_bp
| Pmovzw_GvEv_op => Pmovzw_GvEv_bp
| Pmovsb_GvEv_op => Pmovsb_GvEv_bp
| Pmovzb_rm_op => Pmovzb_rm_bp
| Pmovb_rm_op => Pmovb_rm_bp
| Pmovb_mr_op => Pmovb_mr_bp
| Pxchg_rr_op => Pxchg_rr_bp
| Pflds_m_op => Pflds_m_bp
| Pfstps_m_op => Pfstps_m_bp
| Pfstpl_m_op => Pfstpl_m_bp
| Pfldl_m_op => Pfldl_m_bp
| Pmovss_d_fm_op => Pmovss_d_fm_bp
| Pmovss_d_mf_op => Pmovss_d_mf_bp
| Pmovl_rm_op => Pmovl_rm_bp
| Pmovl_mr_op => Pmovl_mr_bp
| Pmovl_ri_op => Pmovl_ri_bp
end.
Definition encode_Instruction element  :=
	match element with
| REX_WRXB uvar1_0 uvar1_1 uvar1_2 uvar1_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 (proj1_sig uvar1_0) in
let byte03 := write_R byte02 (proj1_sig uvar1_1) in
let byte04 := write_X byte03 (proj1_sig uvar1_2) in
let byte05 := write_B byte04 (proj1_sig uvar1_3) in
let result0 := [byte05] in
OK (result0)
| Override => let byte01 := HB["66"] in
let result0 := [byte01] in
OK (result0)
| REP => let byte01 := HB["F3"] in
let result0 := [byte01] in
OK (result0)
| REPNZ => let byte01 := HB["F2"] in
let result0 := [byte01] in
OK (result0)
| Psubl_ri uvar3_0 uvar32_1 => let byte01 := HB["81"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["101"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar32_1);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| Pbsqrtsd uvar3_0 uvar3_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["51"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_0) in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Psbbl_rr uvar3_0 uvar3_1 => let byte01 := HB["19"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 (proj1_sig uvar3_0) in
let byte13 := write_rm byte12 (proj1_sig uvar3_1) in
let result1 := [byte13] in
OK (result0 ++ result1)
| Prep_movsl => let byte01 := HB["A5"] in
let result0 := [byte01] in
OK (result0)
| Pmovsq_rm AddrE uvar3_0 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["7E"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_0) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pmovsq_mr AddrE uvar3_0 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["D6"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_0) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pminsd uvar3_0 uvar3_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["5D"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_0) in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Pmaxsd uvar3_0 uvar3_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["5F"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_0) in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Pbswap32 uvar3_0 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["001"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
OK (result0 ++ result1)
| Pbsrl uvar3_0 uvar3_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["BD"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_0) in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Pbsfl uvar3_0 uvar3_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["BC"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_0) in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Paddl_mi AddrE uvar32_1 => let byte01 := HB["80"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 b["000"] in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
do byte21 <- bits_to_bytes (proj1_sig uvar32_1);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| Paddl_GvEv AddrE uvar3_0 => let byte01 := HB["03"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 (proj1_sig uvar3_0) in
do byte13 <- encode_AddrE AddrE byte12;
let result1 := byte13 in
OK (result0 ++ result1)
| Paddl_EvGv AddrE uvar3_0 => let byte01 := HB["01"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 (proj1_sig uvar3_0) in
do byte13 <- encode_AddrE AddrE byte12;
let result1 := byte13 in
OK (result0 ++ result1)
| Padcl_rr uvar3_0 uvar3_1 => let byte01 := HB["11"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 (proj1_sig uvar3_0) in
let byte13 := write_rm byte12 (proj1_sig uvar3_1) in
let result1 := [byte13] in
OK (result0 ++ result1)
| Padcl_ri uvar3_0 uvar8_1 => let byte01 := HB["83"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["010"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar8_1);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| Pjcc_rel uvar4_0 uvar32_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_cprefix byte10 b["1000"] in
let byte12 := write_cccode byte11 (proj1_sig uvar4_0) in
let result1 := [byte12] in
do byte21 <- bits_to_bytes (proj1_sig uvar32_1);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| Pret_iw uvar16_0 => let byte01 := HB["C2"] in
let result0 := [byte01] in
do byte11 <- bits_to_bytes (proj1_sig uvar16_0);
let result1 := byte11 in
OK (result0 ++ result1)
| Pret => let byte01 := HB["C3"] in
let result0 := [byte01] in
OK (result0)
| Pcall_r uvar3_0 => let byte01 := HB["FF"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["010"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
OK (result0 ++ result1)
| Pcall_ofs uvar32_0 => let byte01 := HB["E8"] in
let result0 := [byte01] in
do byte11 <- bits_to_bytes (proj1_sig uvar32_0);
let result1 := byte11 in
OK (result0 ++ result1)
| Pnop => let byte01 := HB["90"] in
let result0 := [byte01] in
OK (result0)
| Pjmp_Ev AddrE => let byte01 := HB["FF"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 b["100"] in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Pjmp_l_rel uvar32_0 => let byte01 := HB["E9"] in
let result0 := [byte01] in
do byte11 <- bits_to_bytes (proj1_sig uvar32_0);
let result1 := byte11 in
OK (result0 ++ result1)
| Pxorps_d_GvEv AddrE uvar3_0 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["57"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_0) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pcomiss_d_ff uvar3_0 uvar3_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["2F"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_0) in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Pdivss_d_ff uvar3_0 uvar3_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["5E"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_0) in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Pmuls_d_ff uvar3_0 uvar3_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["59"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_0) in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Psubs_d_ff uvar3_0 uvar3_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["5C"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_0) in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Pandps_d_fm AddrE uvar3_0 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["54"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_0) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Padds_d_ff uvar3_0 uvar3_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["58"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_0) in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Psetcc uvar4_0 uvar3_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_cprefix byte10 b["1001"] in
let byte12 := write_cccode byte11 (proj1_sig uvar4_0) in
let result1 := [byte12] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 b["000"] in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Pcmov uvar4_0 uvar3_1 uvar3_2 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_cprefix byte10 b["0100"] in
let byte12 := write_cccode byte11 (proj1_sig uvar4_0) in
let result1 := [byte12] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_1) in
let byte23 := write_rm byte22 (proj1_sig uvar3_2) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Ptestl_EvGv AddrE uvar3_0 => let byte01 := HB["85"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Ptestl_ri uvar3_0 uvar32_1 => let byte01 := HB["F7"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["000"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar32_1);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| Pcmpl_ri uvar3_0 uvar32_1 => let byte01 := HB["81"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["111"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar32_1);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| Pcmpl_GvEv AddrE uvar3_0 => let byte01 := HB["3B"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Pcmpl_EvGv AddrE uvar3_0 => let byte01 := HB["39"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Prorl_ri uvar3_0 uvar8_1 => let byte01 := HB["C1"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 b["001"] in
let byte12 := write_mod byte11 b["11"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar8_1);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| Prolw_ri uvar3_0 uvar8_1 => let byte01 := HB["C1"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["000"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar8_1);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| Pshld_ri uvar3_0 uvar3_1 uvar8_2 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["A4"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_0) in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
do byte31 <- bits_to_bytes (proj1_sig uvar8_2);
let result3 := byte31 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Psarl_rcl uvar3_0 => let byte01 := HB["D3"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["111"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
OK (result0 ++ result1)
| Psarl_ri uvar3_0 uvar8_1 => let byte01 := HB["C1"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["111"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar8_1);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| Pshrl_rcl uvar3_0 => let byte01 := HB["D3"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["101"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
OK (result0 ++ result1)
| Pshrl_ri uvar3_0 uvar8_1 => let byte01 := HB["C1"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["101"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar8_1);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| Psall_rcl uvar3_0 => let byte01 := HB["D3"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["100"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
OK (result0 ++ result1)
| Psall_ri uvar3_0 uvar8_1 => let byte01 := HB["C1"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["100"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar8_1);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| Pnotl uvar3_0 => let byte01 := HB["F7"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["010"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
OK (result0 ++ result1)
| Pxorl_GvEv AddrE uvar3_0 => let byte01 := HB["33"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Pxorl_EvGv AddrE uvar3_0 => let byte01 := HB["31"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Pxorl_ri uvar3_0 uvar32_1 => let byte01 := HB["81"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["110"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar32_1);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| Porl_GvEv AddrE uvar3_0 => let byte01 := HB["0B"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Porl_EvGv AddrE uvar3_0 => let byte01 := HB["09"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Porl_ri uvar3_0 uvar32_1 => let byte01 := HB["81"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["001"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar32_1);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| Pandl_ri uvar3_0 uvar32_1 => let byte01 := HB["81"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["100"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar32_1);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| Pandl_GvEv AddrE uvar3_0 => let byte01 := HB["23"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Pandl_EvGv AddrE uvar3_0 => let byte01 := HB["21"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Pidivl_r uvar3_0 => let byte01 := HB["F7"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["111"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
OK (result0 ++ result1)
| Pdivl_r uvar3_0 => let byte01 := HB["F7"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["110"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
OK (result0 ++ result1)
| Pcltd => let byte01 := HB["99"] in
let result0 := [byte01] in
OK (result0)
| Pmull_r uvar3_0 => let byte01 := HB["F7"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["100"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
OK (result0 ++ result1)
| Pimull_r uvar3_0 => let byte01 := HB["F7"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["101"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
OK (result0 ++ result1)
| Pimull_ri uvar3_0 uvar3_1 uvar32_2 => let byte01 := HB["69"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 (proj1_sig uvar3_0) in
let byte13 := write_rm byte12 (proj1_sig uvar3_1) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar32_2);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| Pimull_GvEv AddrE uvar3_0 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["AF"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_0) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Psubl_GvEv AddrE uvar3_0 => let byte01 := HB["2B"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Psubl_EvGv AddrE uvar3_0 => let byte01 := HB["29"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Paddl_ri uvar3_0 uvar32_1 => let byte01 := HB["81"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["000"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar32_1);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| Pnegl uvar3_0 => let byte01 := HB["F7"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 b["011"] in
let byte13 := write_rm byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
OK (result0 ++ result1)
| Pleal AddrE uvar3_0 => let byte01 := HB["8D"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Pcvtsi2ss_d_fr uvar3_0 uvar3_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["2A"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_0) in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Pcvttss_d_2si_rf uvar3_0 uvar3_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["2C"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_0) in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Pcvtsd2ss_d_ff uvar3_0 uvar3_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["5A"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_0) in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Pmovsxd_GvEv AddrE uvar3_0 => let byte01 := HB["63"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Pmovsw_GvEv AddrE uvar3_0 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["BF"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_0) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pmovzw_GvEv AddrE uvar3_0 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["B7"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_0) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pmovsb_GvEv AddrE uvar3_0 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["BE"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_0) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pmovzb_rm AddrE uvar3_0 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["B6"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_0) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pmovb_rm AddrE uvar3_0 => let byte01 := HB["8A"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Pmovb_mr AddrE uvar3_0 => let byte01 := HB["88"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Pxchg_rr uvar3_0 uvar3_1 => let byte01 := HB["87"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 (proj1_sig uvar3_0) in
let byte13 := write_rm byte12 (proj1_sig uvar3_1) in
let result1 := [byte13] in
OK (result0 ++ result1)
| Pflds_m AddrE => let byte01 := HB["D9"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 b["000"] in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Pfstps_m AddrE => let byte01 := HB["D9"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 b["011"] in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Pfstpl_m AddrE => let byte01 := HB["DD"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 b["011"] in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Pfldl_m AddrE => let byte01 := HB["DD"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 b["000"] in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Pmovss_d_fm AddrE uvar3_0 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["10"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_0) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pmovss_d_mf AddrE uvar3_0 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["11"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_0) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pmovl_rm AddrE uvar3_0 => let byte01 := HB["8B"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Pmovl_mr AddrE uvar3_0 => let byte01 := HB["89"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_reg_op byte10 (proj1_sig uvar3_0) in
do byte12 <- encode_AddrE AddrE byte11;
let result1 := byte12 in
OK (result0 ++ result1)
| Pmovl_ri uvar3_0 uvar32_1 => let byte00 := HB["00"] in
let byte01 := write_row byte00 b["1011"] in
let byte02 := write_page byte01 b["1"] in
let byte03 := write_col byte02 (proj1_sig uvar3_0) in
let result0 := [byte03] in
do byte11 <- bits_to_bytes (proj1_sig uvar32_1);
let result1 := byte11 in
OK (result0 ++ result1)
end.

Program Definition decode_Instruction code : res (Instruction*nat) :=
	let bin := bytes_to_bits_opt code in
	if REX_WRXB_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_W byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_R byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_X byte0 in
if assertLength uvar1_2 1 then
let uvar1_3 := read_B byte0 in
if assertLength uvar1_3 1 then
do bytes1 <- try_skip_n bytes0 1;
OK ((REX_WRXB (uvar1_0) (uvar1_1) (uvar1_2) (uvar1_3)), 1)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Override_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
OK ((Override), 1)
else

	if REP_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
OK ((REP), 1)
else

	if REPNZ_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
OK ((REPNZ), 1)
else

	if Psubl_ri_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 4;
let uvar32_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_1 32 then
do bytes3 <- try_skip_n bytes2 4;
OK ((Psubl_ri (uvar3_0) (uvar32_1)), 6)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pbsqrtsd_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pbsqrtsd (uvar3_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Psbbl_rr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Psbbl_rr (uvar3_0) (uvar3_1)), 2)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Prep_movsl_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
OK ((Prep_movsl), 1)
else

	if Pmovsq_rm_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pmovsq_rm AddrE (uvar3_0)), 2 + localLength0)
else Error(msg"impossible")
else

	if Pmovsq_mr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pmovsq_mr AddrE (uvar3_0)), 2 + localLength0)
else Error(msg"impossible")
else

	if Pminsd_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pminsd (uvar3_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pmaxsd_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pmaxsd (uvar3_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pbswap32_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Pbswap32 (uvar3_0)), 2)
else Error(msg"impossible")
else

	if Pbsrl_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pbsrl (uvar3_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pbsfl_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pbsfl (uvar3_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Paddl_mi_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
do byte_seq0 <- try_first_n bytes2 4;
let uvar32_1 := bytes_to_bits_opt byte_seq0 in
if assertLength uvar32_1 32 then
do bytes3 <- try_skip_n bytes2 4;
OK ((Paddl_mi AddrE (uvar32_1)), 5 + localLength0)
else Error(msg"impossible")
else

	if Paddl_GvEv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Paddl_GvEv AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Paddl_EvGv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Paddl_EvGv AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Padcl_rr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Padcl_rr (uvar3_0) (uvar3_1)), 2)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Padcl_ri_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 1;
let uvar8_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar8_1 8 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Padcl_ri (uvar3_0) (uvar8_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pjcc_rel_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar4_0 := read_cccode byte0 in
if assertLength uvar4_0 4 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 4;
let uvar32_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_1 32 then
do bytes3 <- try_skip_n bytes2 4;
OK ((Pjcc_rel (uvar4_0) (uvar32_1)), 6)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pret_iw_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte_seq0 <- try_first_n bytes1 2;
let uvar16_0 := bytes_to_bits_opt byte_seq0 in
if assertLength uvar16_0 16 then
do bytes2 <- try_skip_n bytes1 2;
OK ((Pret_iw (uvar16_0)), 3)
else Error(msg"impossible")
else

	if Pret_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
OK ((Pret), 1)
else

	if Pcall_r_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Pcall_r (uvar3_0)), 2)
else Error(msg"impossible")
else

	if Pcall_ofs_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte_seq0 <- try_first_n bytes1 4;
let uvar32_0 := bytes_to_bits_opt byte_seq0 in
if assertLength uvar32_0 32 then
do bytes2 <- try_skip_n bytes1 4;
OK ((Pcall_ofs (uvar32_0)), 5)
else Error(msg"impossible")
else

	if Pnop_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
OK ((Pnop), 1)
else

	if Pjmp_Ev_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pjmp_Ev AddrE), 1 + localLength0)
else

	if Pjmp_l_rel_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte_seq0 <- try_first_n bytes1 4;
let uvar32_0 := bytes_to_bits_opt byte_seq0 in
if assertLength uvar32_0 32 then
do bytes2 <- try_skip_n bytes1 4;
OK ((Pjmp_l_rel (uvar32_0)), 5)
else Error(msg"impossible")
else

	if Pxorps_d_GvEv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pxorps_d_GvEv AddrE (uvar3_0)), 2 + localLength0)
else Error(msg"impossible")
else

	if Pcomiss_d_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pcomiss_d_ff (uvar3_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pdivss_d_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pdivss_d_ff (uvar3_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pmuls_d_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pmuls_d_ff (uvar3_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Psubs_d_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Psubs_d_ff (uvar3_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pandps_d_fm_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pandps_d_fm AddrE (uvar3_0)), 2 + localLength0)
else Error(msg"impossible")
else

	if Padds_d_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Padds_d_ff (uvar3_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Psetcc_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar4_0 := read_cccode byte0 in
if assertLength uvar4_0 4 then
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_1 := read_rm byte1 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Psetcc (uvar4_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pcmov_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar4_0 := read_cccode byte0 in
if assertLength uvar4_0 4 then
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_1 := read_reg_op byte1 in
if assertLength uvar3_1 3 then
let uvar3_2 := read_rm byte1 in
if assertLength uvar3_2 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pcmov (uvar4_0) (uvar3_1) (uvar3_2)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Ptestl_EvGv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Ptestl_EvGv AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Ptestl_ri_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 4;
let uvar32_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_1 32 then
do bytes3 <- try_skip_n bytes2 4;
OK ((Ptestl_ri (uvar3_0) (uvar32_1)), 6)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pcmpl_ri_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 4;
let uvar32_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_1 32 then
do bytes3 <- try_skip_n bytes2 4;
OK ((Pcmpl_ri (uvar3_0) (uvar32_1)), 6)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pcmpl_GvEv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pcmpl_GvEv AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Pcmpl_EvGv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pcmpl_EvGv AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Prorl_ri_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 1;
let uvar8_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar8_1 8 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Prorl_ri (uvar3_0) (uvar8_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Prolw_ri_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 1;
let uvar8_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar8_1 8 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Prolw_ri (uvar3_0) (uvar8_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pshld_ri_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
do byte_seq1 <- try_first_n bytes3 1;
let uvar8_2 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar8_2 8 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Pshld_ri (uvar3_0) (uvar3_1) (uvar8_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Psarl_rcl_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Psarl_rcl (uvar3_0)), 2)
else Error(msg"impossible")
else

	if Psarl_ri_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 1;
let uvar8_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar8_1 8 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Psarl_ri (uvar3_0) (uvar8_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pshrl_rcl_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Pshrl_rcl (uvar3_0)), 2)
else Error(msg"impossible")
else

	if Pshrl_ri_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 1;
let uvar8_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar8_1 8 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pshrl_ri (uvar3_0) (uvar8_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Psall_rcl_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Psall_rcl (uvar3_0)), 2)
else Error(msg"impossible")
else

	if Psall_ri_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 1;
let uvar8_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar8_1 8 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Psall_ri (uvar3_0) (uvar8_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pnotl_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Pnotl (uvar3_0)), 2)
else Error(msg"impossible")
else

	if Pxorl_GvEv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pxorl_GvEv AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Pxorl_EvGv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pxorl_EvGv AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Pxorl_ri_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 4;
let uvar32_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_1 32 then
do bytes3 <- try_skip_n bytes2 4;
OK ((Pxorl_ri (uvar3_0) (uvar32_1)), 6)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Porl_GvEv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Porl_GvEv AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Porl_EvGv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Porl_EvGv AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Porl_ri_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 4;
let uvar32_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_1 32 then
do bytes3 <- try_skip_n bytes2 4;
OK ((Porl_ri (uvar3_0) (uvar32_1)), 6)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pandl_ri_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 4;
let uvar32_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_1 32 then
do bytes3 <- try_skip_n bytes2 4;
OK ((Pandl_ri (uvar3_0) (uvar32_1)), 6)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pandl_GvEv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pandl_GvEv AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Pandl_EvGv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pandl_EvGv AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Pidivl_r_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Pidivl_r (uvar3_0)), 2)
else Error(msg"impossible")
else

	if Pdivl_r_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Pdivl_r (uvar3_0)), 2)
else Error(msg"impossible")
else

	if Pcltd_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
OK ((Pcltd), 1)
else

	if Pmull_r_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Pmull_r (uvar3_0)), 2)
else Error(msg"impossible")
else

	if Pimull_r_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Pimull_r (uvar3_0)), 2)
else Error(msg"impossible")
else

	if Pimull_ri_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 4;
let uvar32_2 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_2 32 then
do bytes3 <- try_skip_n bytes2 4;
OK ((Pimull_ri (uvar3_0) (uvar3_1) (uvar32_2)), 6)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pimull_GvEv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pimull_GvEv AddrE (uvar3_0)), 2 + localLength0)
else Error(msg"impossible")
else

	if Psubl_GvEv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Psubl_GvEv AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Psubl_EvGv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Psubl_EvGv AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Paddl_ri_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 4;
let uvar32_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_1 32 then
do bytes3 <- try_skip_n bytes2 4;
OK ((Paddl_ri (uvar3_0) (uvar32_1)), 6)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pnegl_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Pnegl (uvar3_0)), 2)
else Error(msg"impossible")
else

	if Pleal_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pleal AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Pcvtsi2ss_d_fr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pcvtsi2ss_d_fr (uvar3_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pcvttss_d_2si_rf_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pcvttss_d_2si_rf (uvar3_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pcvtsd2ss_d_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pcvtsd2ss_d_ff (uvar3_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pmovsxd_GvEv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pmovsxd_GvEv AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Pmovsw_GvEv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pmovsw_GvEv AddrE (uvar3_0)), 2 + localLength0)
else Error(msg"impossible")
else

	if Pmovzw_GvEv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pmovzw_GvEv AddrE (uvar3_0)), 2 + localLength0)
else Error(msg"impossible")
else

	if Pmovsb_GvEv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pmovsb_GvEv AddrE (uvar3_0)), 2 + localLength0)
else Error(msg"impossible")
else

	if Pmovzb_rm_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pmovzb_rm AddrE (uvar3_0)), 2 + localLength0)
else Error(msg"impossible")
else

	if Pmovb_rm_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pmovb_rm AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Pmovb_mr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pmovb_mr AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Pxchg_rr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Pxchg_rr (uvar3_0) (uvar3_1)), 2)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pflds_m_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pflds_m AddrE), 1 + localLength0)
else

	if Pfstps_m_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pfstps_m AddrE), 1 + localLength0)
else

	if Pfstpl_m_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pfstpl_m AddrE), 1 + localLength0)
else

	if Pfldl_m_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pfldl_m AddrE), 1 + localLength0)
else

	if Pmovss_d_fm_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pmovss_d_fm AddrE (uvar3_0)), 2 + localLength0)
else Error(msg"impossible")
else

	if Pmovss_d_mf_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pmovss_d_mf AddrE (uvar3_0)), 2 + localLength0)
else Error(msg"impossible")
else

	if Pmovl_rm_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pmovl_rm AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Pmovl_mr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes1;
do bytes2 <- try_skip_n bytes1 localLength0;
OK ((Pmovl_mr AddrE (uvar3_0)), 1 + localLength0)
else Error(msg"impossible")
else

	if Pmovl_ri_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar3_0 := read_col byte0 in
if assertLength uvar3_0 3 then
do bytes1 <- try_skip_n bytes0 1;
do byte_seq1 <- try_first_n bytes1 4;
let uvar32_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_1 32 then
do bytes2 <- try_skip_n bytes1 4;
OK ((Pmovl_ri (uvar3_0) (uvar32_1)), 5)
else Error(msg"impossible")
else Error(msg"impossible")
else

	Error(msg"Unsupported Instruction").

