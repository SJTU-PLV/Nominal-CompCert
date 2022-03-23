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

Hint Unfold AddrE12_bp AddrE11_bp AddrE10_bp AddrE9_bp AddrE8_bp AddrE7_bp AddrE6_bp AddrE5_bp AddrE4_bp AddrE0_bp :AddrE_bpdb.

Hint Unfold Ptestq_EvGv_bp Ptestq_ri_bp Pcmpq_GvEv_bp Pcmpq_EvGv_bp Pcmpq_ri_bp Prorq_ri_bp Psarq_ri_bp Psarq_rcl_bp Psalq_ri_bp Psalq_rcl_bp Pnotq_bp Pxorq_GvEv_bp Pxorq_EvGv_bp Pxorq_ri_bp Porq_GvEv_bp Porq_EvGv_bp Porq_ri_bp Pandq_GvEv_bp Pandq_EvGv_bp Pandq_ri_bp Pdivq_bp Pidivq_bp Pmulq_r_bp Pimulq_GvEv_bp Pimulq_r_bp Pimulq_ri_bp Psubq_GvEv_bp Psubq_EvGv_bp Psubq_ri_bp Paddq_GvEv_bp Paddq_EvGv_bp Paddq_ri_bp Pnegq_bp Pleaq_bp Pmovq_EvGv_bp Pmovq_GvEv_bp Pmovq_ri_bp Psubl_ri_bp Pbsqrtsd_bp Psbbl_rr_bp Prep_movsl_bp Pmovsq_rm_bp Pmovsq_mr_bp Pminsd_bp Pmaxsd_bp Pbswap32_bp Pbsrl_bp Pbsfl_bp Paddl_mi_bp Paddl_rr_bp Padcl_rr_bp Padcl_ri_bp Pjcc_rel_bp Pret_iw_bp Pret_bp Pcall_r_bp Pcall_ofs_bp Pnop_bp Pjmp_Ev_bp Pjmp_l_rel_bp Pandps_fm_bp Pxorps_GvEv_bp Pxorpd_GvEv_bp Pcomiss_ff_bp Pcomisd_ff_bp Pdivss_ff_bp Pdivsd_ff_bp Pmuls_ff_bp Pmuld_ff_bp Psubs_ff_bp Psubd_ff_bp Padds_ff_bp Paddd_ff_bp Psetcc_bp Pcmov_bp Ptestl_rr_bp Ptestl_ri_bp Pcmpl_ri_bp Pcmpl_rr_bp Prorl_ri_bp Prolw_ri_bp Pshld_ri_bp Psarl_rcl_bp Psarl_ri_bp Pshrl_rcl_bp Pshrl_ri_bp Psall_rcl_bp Psall_ri_bp Pnotl_bp Pxorl_rr_bp Pxorl_ri_bp Porl_rr_bp Porl_ri_bp Pandl_ri_bp Pandl_rr_bp Pidivl_r_bp Pdivl_r_bp Pcltd_bp Pmull_r_bp Pimull_ri_bp Pimull_rr_bp Psubl_rr_bp Paddl_ri_bp Pnegl_bp Pleal_bp Pcvttss2si_rf_bp Pcvtsi2sd_fr_bp Pcvtsi2ss_fr_bp Pcvttsd2si_rf_bp Pcvtss2sd_ff_bp Pcvtsd2ss_ff_bp Pmovsw_GvEv_bp Pmovzw_GvEv_bp Pmovsb_GvEv_bp Pmovzb_rm_bp Pmovw_rm_bp Pmovw_mr_bp Pmovb_rm_bp Pmovb_mr_bp Pxchg_rr_bp Pflds_m_bp Pfstps_m_bp Pfstpl_m_bp Pfldl_m_bp Pmovss_fm_bp Pmovss_mf_bp Pmovsd_fm_bp Pmovsd_mf_bp Pmovl_rm_bp Pmovl_mr_bp Pmovl_ri_bp :Instruction_bpdb.
Lemma AddrE_bp_in_list0: 
In AddrE12_bp AddrE_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma AddrE_bp_in_list1: 
In AddrE11_bp AddrE_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma AddrE_bp_in_list2: 
In AddrE10_bp AddrE_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma AddrE_bp_in_list3: 
In AddrE9_bp AddrE_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma AddrE_bp_in_list4: 
In AddrE8_bp AddrE_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma AddrE_bp_in_list5: 
In AddrE7_bp AddrE_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma AddrE_bp_in_list6: 
In AddrE6_bp AddrE_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma AddrE_bp_in_list7: 
In AddrE5_bp AddrE_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma AddrE_bp_in_list8: 
In AddrE4_bp AddrE_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma AddrE_bp_in_list9: 
In AddrE0_bp AddrE_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list0: 
In Ptestq_EvGv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list1: 
In Ptestq_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list2: 
In Pcmpq_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list3: 
In Pcmpq_EvGv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list4: 
In Pcmpq_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list5: 
In Prorq_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list6: 
In Psarq_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list7: 
In Psarq_rcl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list8: 
In Psalq_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list9: 
In Psalq_rcl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list10: 
In Pnotq_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list11: 
In Pxorq_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list12: 
In Pxorq_EvGv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list13: 
In Pxorq_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list14: 
In Porq_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list15: 
In Porq_EvGv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list16: 
In Porq_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list17: 
In Pandq_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list18: 
In Pandq_EvGv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list19: 
In Pandq_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list20: 
In Pdivq_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list21: 
In Pidivq_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list22: 
In Pmulq_r_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list23: 
In Pimulq_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list24: 
In Pimulq_r_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list25: 
In Pimulq_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list26: 
In Psubq_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list27: 
In Psubq_EvGv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list28: 
In Psubq_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list29: 
In Paddq_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list30: 
In Paddq_EvGv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list31: 
In Paddq_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list32: 
In Pnegq_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list33: 
In Pleaq_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list34: 
In Pmovq_EvGv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list35: 
In Pmovq_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list36: 
In Pmovq_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list37: 
In Psubl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list38: 
In Pbsqrtsd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list39: 
In Psbbl_rr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list40: 
In Prep_movsl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list41: 
In Pmovsq_rm_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list42: 
In Pmovsq_mr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list43: 
In Pminsd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list44: 
In Pmaxsd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list45: 
In Pbswap32_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list46: 
In Pbsrl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list47: 
In Pbsfl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list48: 
In Paddl_mi_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list49: 
In Paddl_rr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list50: 
In Padcl_rr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list51: 
In Padcl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list52: 
In Pjcc_rel_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list53: 
In Pret_iw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list54: 
In Pret_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list55: 
In Pcall_r_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list56: 
In Pcall_ofs_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list57: 
In Pnop_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list58: 
In Pjmp_Ev_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list59: 
In Pjmp_l_rel_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list60: 
In Pandps_fm_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list61: 
In Pxorps_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list62: 
In Pxorpd_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list63: 
In Pcomiss_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list64: 
In Pcomisd_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list65: 
In Pdivss_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list66: 
In Pdivsd_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list67: 
In Pmuls_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list68: 
In Pmuld_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list69: 
In Psubs_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list70: 
In Psubd_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list71: 
In Padds_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list72: 
In Paddd_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list73: 
In Psetcc_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list74: 
In Pcmov_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list75: 
In Ptestl_rr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list76: 
In Ptestl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list77: 
In Pcmpl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list78: 
In Pcmpl_rr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list79: 
In Prorl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list80: 
In Prolw_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list81: 
In Pshld_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list82: 
In Psarl_rcl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list83: 
In Psarl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list84: 
In Pshrl_rcl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list85: 
In Pshrl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list86: 
In Psall_rcl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list87: 
In Psall_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list88: 
In Pnotl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list89: 
In Pxorl_rr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list90: 
In Pxorl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list91: 
In Porl_rr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list92: 
In Porl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list93: 
In Pandl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list94: 
In Pandl_rr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list95: 
In Pidivl_r_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list96: 
In Pdivl_r_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list97: 
In Pcltd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list98: 
In Pmull_r_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list99: 
In Pimull_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list100: 
In Pimull_rr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list101: 
In Psubl_rr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list102: 
In Paddl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list103: 
In Pnegl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list104: 
In Pleal_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list105: 
In Pcvttss2si_rf_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list106: 
In Pcvtsi2sd_fr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list107: 
In Pcvtsi2ss_fr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list108: 
In Pcvttsd2si_rf_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list109: 
In Pcvtss2sd_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list110: 
In Pcvtsd2ss_ff_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list111: 
In Pmovsw_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list112: 
In Pmovzw_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list113: 
In Pmovsb_GvEv_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list114: 
In Pmovzb_rm_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list115: 
In Pmovw_rm_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list116: 
In Pmovw_mr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list117: 
In Pmovb_rm_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list118: 
In Pmovb_mr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list119: 
In Pxchg_rr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list120: 
In Pflds_m_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list121: 
In Pfstps_m_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list122: 
In Pfstpl_m_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list123: 
In Pfldl_m_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list124: 
In Pmovss_fm_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list125: 
In Pmovss_mf_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list126: 
In Pmovsd_fm_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list127: 
In Pmovsd_mf_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list128: 
In Pmovl_rm_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list129: 
In Pmovl_mr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list130: 
In Pmovl_ri_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Inductive AddrE: Type :=
| AddrE12(uvar3_0:u3)
| AddrE11(uvar32_0:u32)
| AddrE10(uvar2_0:u2)(uvar3_1:u3)(uvar3_2:u3)
| AddrE9(uvar2_0:u2)(uvar3_1:u3)(uvar32_2:u32)
| AddrE8(uvar3_0:u3)
| AddrE7(uvar32_0:u32)
| AddrE6(uvar3_0:u3)(uvar32_1:u32)
| AddrE5(uvar2_0:u2)(uvar3_1:u3)(uvar3_2:u3)(uvar32_3:u32)
| AddrE4(uvar3_0:u3)(uvar32_1:u32)
| AddrE0(uvar3_0:u3).
Inductive AddrE_op: Type :=
| AddrE12_op
| AddrE11_op
| AddrE10_op
| AddrE9_op
| AddrE8_op
| AddrE7_op
| AddrE6_op
| AddrE5_op
| AddrE4_op
| AddrE0_op.
Definition AddrE_to_op element  :=
	match element with
| AddrE12 _ => AddrE12_op
| AddrE11 _ => AddrE11_op
| AddrE10 _ _ _ => AddrE10_op
| AddrE9 _ _ _ => AddrE9_op
| AddrE8 _ => AddrE8_op
| AddrE7 _ => AddrE7_op
| AddrE6 _ _ => AddrE6_op
| AddrE5 _ _ _ _ => AddrE5_op
| AddrE4 _ _ => AddrE4_op
| AddrE0 _ => AddrE0_op
end.
Definition AddrE_op_to_bp element  :=
	match element with
| AddrE12_op => AddrE12_bp
| AddrE11_op => AddrE11_bp
| AddrE10_op => AddrE10_bp
| AddrE9_op => AddrE9_bp
| AddrE8_op => AddrE8_bp
| AddrE7_op => AddrE7_bp
| AddrE6_op => AddrE6_bp
| AddrE5_op => AddrE5_bp
| AddrE4_op => AddrE4_bp
| AddrE0_op => AddrE0_bp
end.
Definition encode_AddrE element  inByte  :=
	match element with
| AddrE12 uvar3_0 => if builtin_eq_dec (proj1_sig uvar3_0)b["100"] then
Error(msg"Constraint Failed")
else

if builtin_eq_dec (proj1_sig uvar3_0)b["101"] then
Error(msg"Constraint Failed")
else

let byte00 := inByte in
let byte01 := write_mod byte00 b["00"] in
let byte02 := write_rm byte01 (proj1_sig uvar3_0) in
let result0 := [byte02] in
OK (result0)
| AddrE11 uvar32_0 => let byte00 := inByte in
let byte01 := write_mod byte00 b["00"] in
let byte02 := write_rm byte01 b["101"] in
let result0 := [byte02] in
do byte11 <- bits_to_bytes (proj1_sig uvar32_0);
let result1 := byte11 in
OK (result0 ++ result1)
| AddrE10 uvar2_0 uvar3_1 uvar3_2 => if builtin_eq_dec (proj1_sig uvar3_2)b["101"] then
Error(msg"Constraint Failed")
else

if builtin_eq_dec (proj1_sig uvar3_1)b["100"] then
Error(msg"Constraint Failed")
else

let byte00 := inByte in
let byte01 := write_mod byte00 b["00"] in
let byte02 := write_rm byte01 b["100"] in
let result0 := [byte02] in
let byte10 := HB["00"] in
let byte11 := write_scale byte10 (proj1_sig uvar2_0) in
let byte12 := write_index byte11 (proj1_sig uvar3_1) in
let byte13 := write_base byte12 (proj1_sig uvar3_2) in
let result1 := [byte13] in
OK (result0 ++ result1)
| AddrE9 uvar2_0 uvar3_1 uvar32_2 => if builtin_eq_dec (proj1_sig uvar3_1)b["100"] then
Error(msg"Constraint Failed")
else

let byte00 := inByte in
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
| AddrE8 uvar3_0 => if builtin_eq_dec (proj1_sig uvar3_0)b["101"] then
Error(msg"Constraint Failed")
else

let byte00 := inByte in
let byte01 := write_mod byte00 b["00"] in
let byte02 := write_rm byte01 b["100"] in
let result0 := [byte02] in
let byte10 := HB["00"] in
let byte11 := write_scale byte10 b["00"] in
let byte12 := write_index byte11 b["100"] in
let byte13 := write_base byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
OK (result0 ++ result1)
| AddrE7 uvar32_0 => let byte00 := inByte in
let byte01 := write_mod byte00 b["00"] in
let byte02 := write_rm byte01 b["100"] in
let result0 := [byte02] in
let byte10 := HB["00"] in
let byte11 := write_scale byte10 b["00"] in
let byte12 := write_index byte11 b["100"] in
let byte13 := write_base byte12 b["101"] in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar32_0);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
| AddrE6 uvar3_0 uvar32_1 => if builtin_eq_dec (proj1_sig uvar3_0)b["100"] then
Error(msg"Constraint Failed")
else

let byte00 := inByte in
let byte01 := write_mod byte00 b["10"] in
let byte02 := write_rm byte01 (proj1_sig uvar3_0) in
let result0 := [byte02] in
do byte11 <- bits_to_bytes (proj1_sig uvar32_1);
let result1 := byte11 in
OK (result0 ++ result1)
| AddrE5 uvar2_0 uvar3_1 uvar3_2 uvar32_3 => if builtin_eq_dec (proj1_sig uvar3_1)b["100"] then
Error(msg"Constraint Failed")
else

let byte00 := inByte in
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
| AddrE4 uvar3_0 uvar32_1 => let byte00 := inByte in
let byte01 := write_mod byte00 b["10"] in
let byte02 := write_rm byte01 b["100"] in
let result0 := [byte02] in
let byte10 := HB["00"] in
let byte11 := write_scale byte10 b["00"] in
let byte12 := write_index byte11 b["100"] in
let byte13 := write_base byte12 (proj1_sig uvar3_0) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar32_1);
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
	if AddrE12_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes1 <- try_skip_n bytes0 1;
OK ((AddrE12 (uvar3_0)), 1)
else Error(msg"impossible")
else

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

	if AddrE10_bp bin then
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
OK ((AddrE10 (uvar2_0) (uvar3_1) (uvar3_2)), 2)
else Error(msg"impossible")
else Error(msg"impossible")
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

	if AddrE8_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_base byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((AddrE8 (uvar3_0)), 2)
else Error(msg"impossible")
else

	if AddrE7_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte_seq0 <- try_first_n bytes2 4;
let uvar32_0 := bytes_to_bits_opt byte_seq0 in
if assertLength uvar32_0 32 then
do bytes3 <- try_skip_n bytes2 4;
OK ((AddrE7 (uvar32_0)), 6)
else Error(msg"impossible")
else

	if AddrE6_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes1 <- try_skip_n bytes0 1;
do byte_seq1 <- try_first_n bytes1 4;
let uvar32_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_1 32 then
do bytes2 <- try_skip_n bytes1 4;
OK ((AddrE6 (uvar3_0) (uvar32_1)), 5)
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

	if AddrE4_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_base byte0 in
if assertLength uvar3_0 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq1 <- try_first_n bytes2 4;
let uvar32_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_1 32 then
do bytes3 <- try_skip_n bytes2 4;
OK ((AddrE4 (uvar3_0) (uvar32_1)), 6)
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
| Ptestq_EvGv(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Ptestq_ri(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar32_4:u32)
| Pcmpq_GvEv(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Pcmpq_EvGv(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Pcmpq_ri(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar32_4:u32)
| Prorq_ri(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar8_4:u8)
| Psarq_ri(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar8_4:u8)
| Psarq_rcl(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)
| Psalq_ri(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar8_4:u8)
| Psalq_rcl(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)
| Pnotq(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)
| Pxorq_GvEv(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Pxorq_EvGv(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Pxorq_ri(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar32_4:u32)
| Porq_GvEv(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Porq_EvGv(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Porq_ri(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar32_4:u32)
| Pandq_GvEv(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Pandq_EvGv(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Pandq_ri(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar32_4:u32)
| Pdivq(uvar1_0:u1)(uvar3_1:u3)
| Pidivq(uvar1_0:u1)(uvar3_1:u3)
| Pmulq_r(uvar1_0:u1)(uvar3_1:u3)
| Pimulq_GvEv(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Pimulq_r(uvar1_0:u1)(uvar3_1:u3)
| Pimulq_ri(uvar1_0:u1)(uvar1_1:u1)(uvar3_2:u3)(uvar3_3:u3)(uvar32_4:u32)
| Psubq_GvEv(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Psubq_EvGv(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Psubq_ri(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar32_4:u32)
| Paddq_GvEv(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Paddq_EvGv(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Paddq_ri(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar32_4:u32)
| Pnegq(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)
| Pleaq(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Pmovq_EvGv(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Pmovq_GvEv(AddrE:AddrE)(uvar1_0:u1)(uvar1_1:u1)(uvar1_2:u1)(uvar3_3:u3)
| Pmovq_ri(uvar1_0:u1)(uvar3_1:u3)(uvar64_2:u64)
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
| Paddl_rr(uvar3_0:u3)(uvar3_1:u3)
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
| Pandps_fm(AddrE:AddrE)(uvar3_0:u3)
| Pxorps_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pxorpd_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pcomiss_ff(uvar3_0:u3)(uvar3_1:u3)
| Pcomisd_ff(uvar3_0:u3)(uvar3_1:u3)
| Pdivss_ff(uvar3_0:u3)(uvar3_1:u3)
| Pdivsd_ff(uvar3_0:u3)(uvar3_1:u3)
| Pmuls_ff(uvar3_0:u3)(uvar3_1:u3)
| Pmuld_ff(uvar3_0:u3)(uvar3_1:u3)
| Psubs_ff(uvar3_0:u3)(uvar3_1:u3)
| Psubd_ff(uvar3_0:u3)(uvar3_1:u3)
| Padds_ff(uvar3_0:u3)(uvar3_1:u3)
| Paddd_ff(uvar3_0:u3)(uvar3_1:u3)
| Psetcc(uvar4_0:u4)(uvar3_1:u3)
| Pcmov(uvar4_0:u4)(uvar3_1:u3)(uvar3_2:u3)
| Ptestl_rr(uvar3_0:u3)(uvar3_1:u3)
| Ptestl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pcmpl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pcmpl_rr(uvar3_0:u3)(uvar3_1:u3)
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
| Pxorl_rr(uvar3_0:u3)(uvar3_1:u3)
| Pxorl_ri(uvar3_0:u3)(uvar32_1:u32)
| Porl_rr(uvar3_0:u3)(uvar3_1:u3)
| Porl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pandl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pandl_rr(uvar3_0:u3)(uvar3_1:u3)
| Pidivl_r(uvar3_0:u3)
| Pdivl_r(uvar3_0:u3)
| Pcltd
| Pmull_r(uvar3_0:u3)
| Pimull_ri(uvar3_0:u3)(uvar3_1:u3)(uvar32_2:u32)
| Pimull_rr(uvar3_0:u3)(uvar3_1:u3)
| Psubl_rr(uvar3_0:u3)(uvar3_1:u3)
| Paddl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pnegl(uvar3_0:u3)
| Pleal(AddrE:AddrE)(uvar3_0:u3)
| Pcvttss2si_rf(uvar3_0:u3)(uvar3_1:u3)
| Pcvtsi2sd_fr(uvar3_0:u3)(uvar3_1:u3)
| Pcvtsi2ss_fr(uvar3_0:u3)(uvar3_1:u3)
| Pcvttsd2si_rf(uvar3_0:u3)(uvar3_1:u3)
| Pcvtss2sd_ff(uvar3_0:u3)(uvar3_1:u3)
| Pcvtsd2ss_ff(uvar3_0:u3)(uvar3_1:u3)
| Pmovsw_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pmovzw_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pmovsb_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pmovzb_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovw_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovw_mr(AddrE:AddrE)(uvar3_0:u3)
| Pmovb_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovb_mr(AddrE:AddrE)(uvar3_0:u3)
| Pxchg_rr(uvar3_0:u3)(uvar3_1:u3)
| Pflds_m(AddrE:AddrE)
| Pfstps_m(AddrE:AddrE)
| Pfstpl_m(AddrE:AddrE)
| Pfldl_m(AddrE:AddrE)
| Pmovss_fm(AddrE:AddrE)(uvar3_0:u3)
| Pmovss_mf(AddrE:AddrE)(uvar3_0:u3)
| Pmovsd_fm(AddrE:AddrE)(uvar3_0:u3)
| Pmovsd_mf(AddrE:AddrE)(uvar3_0:u3)
| Pmovl_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovl_mr(AddrE:AddrE)(uvar3_0:u3)
| Pmovl_ri(uvar3_0:u3)(uvar32_1:u32).
Inductive Instruction_op: Type :=
| Ptestq_EvGv_op
| Ptestq_ri_op
| Pcmpq_GvEv_op
| Pcmpq_EvGv_op
| Pcmpq_ri_op
| Prorq_ri_op
| Psarq_ri_op
| Psarq_rcl_op
| Psalq_ri_op
| Psalq_rcl_op
| Pnotq_op
| Pxorq_GvEv_op
| Pxorq_EvGv_op
| Pxorq_ri_op
| Porq_GvEv_op
| Porq_EvGv_op
| Porq_ri_op
| Pandq_GvEv_op
| Pandq_EvGv_op
| Pandq_ri_op
| Pdivq_op
| Pidivq_op
| Pmulq_r_op
| Pimulq_GvEv_op
| Pimulq_r_op
| Pimulq_ri_op
| Psubq_GvEv_op
| Psubq_EvGv_op
| Psubq_ri_op
| Paddq_GvEv_op
| Paddq_EvGv_op
| Paddq_ri_op
| Pnegq_op
| Pleaq_op
| Pmovq_EvGv_op
| Pmovq_GvEv_op
| Pmovq_ri_op
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
| Paddl_rr_op
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
| Pandps_fm_op
| Pxorps_GvEv_op
| Pxorpd_GvEv_op
| Pcomiss_ff_op
| Pcomisd_ff_op
| Pdivss_ff_op
| Pdivsd_ff_op
| Pmuls_ff_op
| Pmuld_ff_op
| Psubs_ff_op
| Psubd_ff_op
| Padds_ff_op
| Paddd_ff_op
| Psetcc_op
| Pcmov_op
| Ptestl_rr_op
| Ptestl_ri_op
| Pcmpl_ri_op
| Pcmpl_rr_op
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
| Pxorl_rr_op
| Pxorl_ri_op
| Porl_rr_op
| Porl_ri_op
| Pandl_ri_op
| Pandl_rr_op
| Pidivl_r_op
| Pdivl_r_op
| Pcltd_op
| Pmull_r_op
| Pimull_ri_op
| Pimull_rr_op
| Psubl_rr_op
| Paddl_ri_op
| Pnegl_op
| Pleal_op
| Pcvttss2si_rf_op
| Pcvtsi2sd_fr_op
| Pcvtsi2ss_fr_op
| Pcvttsd2si_rf_op
| Pcvtss2sd_ff_op
| Pcvtsd2ss_ff_op
| Pmovsw_GvEv_op
| Pmovzw_GvEv_op
| Pmovsb_GvEv_op
| Pmovzb_rm_op
| Pmovw_rm_op
| Pmovw_mr_op
| Pmovb_rm_op
| Pmovb_mr_op
| Pxchg_rr_op
| Pflds_m_op
| Pfstps_m_op
| Pfstpl_m_op
| Pfldl_m_op
| Pmovss_fm_op
| Pmovss_mf_op
| Pmovsd_fm_op
| Pmovsd_mf_op
| Pmovl_rm_op
| Pmovl_mr_op
| Pmovl_ri_op.
Definition Instruction_to_op element  :=
	match element with
| Ptestq_EvGv _ _ _ _ _ => Ptestq_EvGv_op
| Ptestq_ri _ _ _ _ _ => Ptestq_ri_op
| Pcmpq_GvEv _ _ _ _ _ => Pcmpq_GvEv_op
| Pcmpq_EvGv _ _ _ _ _ => Pcmpq_EvGv_op
| Pcmpq_ri _ _ _ _ _ => Pcmpq_ri_op
| Prorq_ri _ _ _ _ _ => Prorq_ri_op
| Psarq_ri _ _ _ _ _ => Psarq_ri_op
| Psarq_rcl _ _ _ _ => Psarq_rcl_op
| Psalq_ri _ _ _ _ _ => Psalq_ri_op
| Psalq_rcl _ _ _ _ => Psalq_rcl_op
| Pnotq _ _ _ _ => Pnotq_op
| Pxorq_GvEv _ _ _ _ _ => Pxorq_GvEv_op
| Pxorq_EvGv _ _ _ _ _ => Pxorq_EvGv_op
| Pxorq_ri _ _ _ _ _ => Pxorq_ri_op
| Porq_GvEv _ _ _ _ _ => Porq_GvEv_op
| Porq_EvGv _ _ _ _ _ => Porq_EvGv_op
| Porq_ri _ _ _ _ _ => Porq_ri_op
| Pandq_GvEv _ _ _ _ _ => Pandq_GvEv_op
| Pandq_EvGv _ _ _ _ _ => Pandq_EvGv_op
| Pandq_ri _ _ _ _ _ => Pandq_ri_op
| Pdivq _ _ => Pdivq_op
| Pidivq _ _ => Pidivq_op
| Pmulq_r _ _ => Pmulq_r_op
| Pimulq_GvEv _ _ _ _ _ => Pimulq_GvEv_op
| Pimulq_r _ _ => Pimulq_r_op
| Pimulq_ri _ _ _ _ _ => Pimulq_ri_op
| Psubq_GvEv _ _ _ _ _ => Psubq_GvEv_op
| Psubq_EvGv _ _ _ _ _ => Psubq_EvGv_op
| Psubq_ri _ _ _ _ _ => Psubq_ri_op
| Paddq_GvEv _ _ _ _ _ => Paddq_GvEv_op
| Paddq_EvGv _ _ _ _ _ => Paddq_EvGv_op
| Paddq_ri _ _ _ _ _ => Paddq_ri_op
| Pnegq _ _ _ _ => Pnegq_op
| Pleaq _ _ _ _ _ => Pleaq_op
| Pmovq_EvGv _ _ _ _ _ => Pmovq_EvGv_op
| Pmovq_GvEv _ _ _ _ _ => Pmovq_GvEv_op
| Pmovq_ri _ _ _ => Pmovq_ri_op
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
| Paddl_rr _ _ => Paddl_rr_op
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
| Pandps_fm _ _ => Pandps_fm_op
| Pxorps_GvEv _ _ => Pxorps_GvEv_op
| Pxorpd_GvEv _ _ => Pxorpd_GvEv_op
| Pcomiss_ff _ _ => Pcomiss_ff_op
| Pcomisd_ff _ _ => Pcomisd_ff_op
| Pdivss_ff _ _ => Pdivss_ff_op
| Pdivsd_ff _ _ => Pdivsd_ff_op
| Pmuls_ff _ _ => Pmuls_ff_op
| Pmuld_ff _ _ => Pmuld_ff_op
| Psubs_ff _ _ => Psubs_ff_op
| Psubd_ff _ _ => Psubd_ff_op
| Padds_ff _ _ => Padds_ff_op
| Paddd_ff _ _ => Paddd_ff_op
| Psetcc _ _ => Psetcc_op
| Pcmov _ _ _ => Pcmov_op
| Ptestl_rr _ _ => Ptestl_rr_op
| Ptestl_ri _ _ => Ptestl_ri_op
| Pcmpl_ri _ _ => Pcmpl_ri_op
| Pcmpl_rr _ _ => Pcmpl_rr_op
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
| Pxorl_rr _ _ => Pxorl_rr_op
| Pxorl_ri _ _ => Pxorl_ri_op
| Porl_rr _ _ => Porl_rr_op
| Porl_ri _ _ => Porl_ri_op
| Pandl_ri _ _ => Pandl_ri_op
| Pandl_rr _ _ => Pandl_rr_op
| Pidivl_r _ => Pidivl_r_op
| Pdivl_r _ => Pdivl_r_op
| Pcltd => Pcltd_op
| Pmull_r _ => Pmull_r_op
| Pimull_ri _ _ _ => Pimull_ri_op
| Pimull_rr _ _ => Pimull_rr_op
| Psubl_rr _ _ => Psubl_rr_op
| Paddl_ri _ _ => Paddl_ri_op
| Pnegl _ => Pnegl_op
| Pleal _ _ => Pleal_op
| Pcvttss2si_rf _ _ => Pcvttss2si_rf_op
| Pcvtsi2sd_fr _ _ => Pcvtsi2sd_fr_op
| Pcvtsi2ss_fr _ _ => Pcvtsi2ss_fr_op
| Pcvttsd2si_rf _ _ => Pcvttsd2si_rf_op
| Pcvtss2sd_ff _ _ => Pcvtss2sd_ff_op
| Pcvtsd2ss_ff _ _ => Pcvtsd2ss_ff_op
| Pmovsw_GvEv _ _ => Pmovsw_GvEv_op
| Pmovzw_GvEv _ _ => Pmovzw_GvEv_op
| Pmovsb_GvEv _ _ => Pmovsb_GvEv_op
| Pmovzb_rm _ _ => Pmovzb_rm_op
| Pmovw_rm _ _ => Pmovw_rm_op
| Pmovw_mr _ _ => Pmovw_mr_op
| Pmovb_rm _ _ => Pmovb_rm_op
| Pmovb_mr _ _ => Pmovb_mr_op
| Pxchg_rr _ _ => Pxchg_rr_op
| Pflds_m _ => Pflds_m_op
| Pfstps_m _ => Pfstps_m_op
| Pfstpl_m _ => Pfstpl_m_op
| Pfldl_m _ => Pfldl_m_op
| Pmovss_fm _ _ => Pmovss_fm_op
| Pmovss_mf _ _ => Pmovss_mf_op
| Pmovsd_fm _ _ => Pmovsd_fm_op
| Pmovsd_mf _ _ => Pmovsd_mf_op
| Pmovl_rm _ _ => Pmovl_rm_op
| Pmovl_mr _ _ => Pmovl_mr_op
| Pmovl_ri _ _ => Pmovl_ri_op
end.
Definition Instruction_op_to_bp element  :=
	match element with
| Ptestq_EvGv_op => Ptestq_EvGv_bp
| Ptestq_ri_op => Ptestq_ri_bp
| Pcmpq_GvEv_op => Pcmpq_GvEv_bp
| Pcmpq_EvGv_op => Pcmpq_EvGv_bp
| Pcmpq_ri_op => Pcmpq_ri_bp
| Prorq_ri_op => Prorq_ri_bp
| Psarq_ri_op => Psarq_ri_bp
| Psarq_rcl_op => Psarq_rcl_bp
| Psalq_ri_op => Psalq_ri_bp
| Psalq_rcl_op => Psalq_rcl_bp
| Pnotq_op => Pnotq_bp
| Pxorq_GvEv_op => Pxorq_GvEv_bp
| Pxorq_EvGv_op => Pxorq_EvGv_bp
| Pxorq_ri_op => Pxorq_ri_bp
| Porq_GvEv_op => Porq_GvEv_bp
| Porq_EvGv_op => Porq_EvGv_bp
| Porq_ri_op => Porq_ri_bp
| Pandq_GvEv_op => Pandq_GvEv_bp
| Pandq_EvGv_op => Pandq_EvGv_bp
| Pandq_ri_op => Pandq_ri_bp
| Pdivq_op => Pdivq_bp
| Pidivq_op => Pidivq_bp
| Pmulq_r_op => Pmulq_r_bp
| Pimulq_GvEv_op => Pimulq_GvEv_bp
| Pimulq_r_op => Pimulq_r_bp
| Pimulq_ri_op => Pimulq_ri_bp
| Psubq_GvEv_op => Psubq_GvEv_bp
| Psubq_EvGv_op => Psubq_EvGv_bp
| Psubq_ri_op => Psubq_ri_bp
| Paddq_GvEv_op => Paddq_GvEv_bp
| Paddq_EvGv_op => Paddq_EvGv_bp
| Paddq_ri_op => Paddq_ri_bp
| Pnegq_op => Pnegq_bp
| Pleaq_op => Pleaq_bp
| Pmovq_EvGv_op => Pmovq_EvGv_bp
| Pmovq_GvEv_op => Pmovq_GvEv_bp
| Pmovq_ri_op => Pmovq_ri_bp
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
| Paddl_rr_op => Paddl_rr_bp
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
| Pandps_fm_op => Pandps_fm_bp
| Pxorps_GvEv_op => Pxorps_GvEv_bp
| Pxorpd_GvEv_op => Pxorpd_GvEv_bp
| Pcomiss_ff_op => Pcomiss_ff_bp
| Pcomisd_ff_op => Pcomisd_ff_bp
| Pdivss_ff_op => Pdivss_ff_bp
| Pdivsd_ff_op => Pdivsd_ff_bp
| Pmuls_ff_op => Pmuls_ff_bp
| Pmuld_ff_op => Pmuld_ff_bp
| Psubs_ff_op => Psubs_ff_bp
| Psubd_ff_op => Psubd_ff_bp
| Padds_ff_op => Padds_ff_bp
| Paddd_ff_op => Paddd_ff_bp
| Psetcc_op => Psetcc_bp
| Pcmov_op => Pcmov_bp
| Ptestl_rr_op => Ptestl_rr_bp
| Ptestl_ri_op => Ptestl_ri_bp
| Pcmpl_ri_op => Pcmpl_ri_bp
| Pcmpl_rr_op => Pcmpl_rr_bp
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
| Pxorl_rr_op => Pxorl_rr_bp
| Pxorl_ri_op => Pxorl_ri_bp
| Porl_rr_op => Porl_rr_bp
| Porl_ri_op => Porl_ri_bp
| Pandl_ri_op => Pandl_ri_bp
| Pandl_rr_op => Pandl_rr_bp
| Pidivl_r_op => Pidivl_r_bp
| Pdivl_r_op => Pdivl_r_bp
| Pcltd_op => Pcltd_bp
| Pmull_r_op => Pmull_r_bp
| Pimull_ri_op => Pimull_ri_bp
| Pimull_rr_op => Pimull_rr_bp
| Psubl_rr_op => Psubl_rr_bp
| Paddl_ri_op => Paddl_ri_bp
| Pnegl_op => Pnegl_bp
| Pleal_op => Pleal_bp
| Pcvttss2si_rf_op => Pcvttss2si_rf_bp
| Pcvtsi2sd_fr_op => Pcvtsi2sd_fr_bp
| Pcvtsi2ss_fr_op => Pcvtsi2ss_fr_bp
| Pcvttsd2si_rf_op => Pcvttsd2si_rf_bp
| Pcvtss2sd_ff_op => Pcvtss2sd_ff_bp
| Pcvtsd2ss_ff_op => Pcvtsd2ss_ff_bp
| Pmovsw_GvEv_op => Pmovsw_GvEv_bp
| Pmovzw_GvEv_op => Pmovzw_GvEv_bp
| Pmovsb_GvEv_op => Pmovsb_GvEv_bp
| Pmovzb_rm_op => Pmovzb_rm_bp
| Pmovw_rm_op => Pmovw_rm_bp
| Pmovw_mr_op => Pmovw_mr_bp
| Pmovb_rm_op => Pmovb_rm_bp
| Pmovb_mr_op => Pmovb_mr_bp
| Pxchg_rr_op => Pxchg_rr_bp
| Pflds_m_op => Pflds_m_bp
| Pfstps_m_op => Pfstps_m_bp
| Pfstpl_m_op => Pfstpl_m_bp
| Pfldl_m_op => Pfldl_m_bp
| Pmovss_fm_op => Pmovss_fm_bp
| Pmovss_mf_op => Pmovss_mf_bp
| Pmovsd_fm_op => Pmovsd_fm_bp
| Pmovsd_mf_op => Pmovsd_mf_bp
| Pmovl_rm_op => Pmovl_rm_bp
| Pmovl_mr_op => Pmovl_mr_bp
| Pmovl_ri_op => Pmovl_ri_bp
end.
Definition encode_Instruction element  :=
	match element with
| Ptestq_EvGv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["85"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_3) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Ptestq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["F7"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 b["000"] in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
do byte31 <- bits_to_bytes (proj1_sig uvar32_4);
let result3 := byte31 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pcmpq_GvEv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["3B"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_3) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pcmpq_EvGv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["39"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_3) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pcmpq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["81"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 b["111"] in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
do byte31 <- bits_to_bytes (proj1_sig uvar32_4);
let result3 := byte31 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Prorq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar8_4 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["C1"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 b["001"] in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
do byte31 <- bits_to_bytes (proj1_sig uvar8_4);
let result3 := byte31 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Psarq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar8_4 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["C1"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 b["111"] in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
do byte31 <- bits_to_bytes (proj1_sig uvar8_4);
let result3 := byte31 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Psarq_rcl AddrE uvar1_0 uvar1_1 uvar1_2 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["D3"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 b["111"] in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Psalq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar8_4 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["C1"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 b["100"] in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
do byte31 <- bits_to_bytes (proj1_sig uvar8_4);
let result3 := byte31 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Psalq_rcl AddrE uvar1_0 uvar1_1 uvar1_2 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["D3"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 b["100"] in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pnotq AddrE uvar1_0 uvar1_1 uvar1_2 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["F7"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 b["010"] in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pxorq_GvEv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["33"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_3) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pxorq_EvGv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["31"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_3) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pxorq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["81"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 b["110"] in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
do byte31 <- bits_to_bytes (proj1_sig uvar32_4);
let result3 := byte31 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Porq_GvEv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["0B"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_3) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Porq_EvGv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["09"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_3) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Porq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["81"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 b["001"] in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
do byte31 <- bits_to_bytes (proj1_sig uvar32_4);
let result3 := byte31 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pandq_GvEv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["23"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_3) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pandq_EvGv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["21"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_3) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pandq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["81"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 b["100"] in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
do byte31 <- bits_to_bytes (proj1_sig uvar32_4);
let result3 := byte31 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pdivq uvar1_0 uvar3_1 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 b["0"] in
let byte04 := write_X byte03 b["0"] in
let byte05 := write_B byte04 (proj1_sig uvar1_0) in
let result0 := [byte05] in
let byte11 := HB["F7"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 b["110"] in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Pidivq uvar1_0 uvar3_1 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 b["0"] in
let byte04 := write_X byte03 b["0"] in
let byte05 := write_B byte04 (proj1_sig uvar1_0) in
let result0 := [byte05] in
let byte11 := HB["F7"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 b["111"] in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Pmulq_r uvar1_0 uvar3_1 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 b["0"] in
let byte04 := write_X byte03 b["0"] in
let byte05 := write_B byte04 (proj1_sig uvar1_0) in
let result0 := [byte05] in
let byte11 := HB["F7"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 b["100"] in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Pimulq_GvEv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["AF"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_reg_op byte30 (proj1_sig uvar3_3) in
do byte32 <- encode_AddrE AddrE byte31;
let result3 := byte32 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pimulq_r uvar1_0 uvar3_1 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 b["0"] in
let byte04 := write_X byte03 b["0"] in
let byte05 := write_B byte04 (proj1_sig uvar1_0) in
let result0 := [byte05] in
let byte11 := HB["F7"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 b["101"] in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Pimulq_ri uvar1_0 uvar1_1 uvar3_2 uvar3_3 uvar32_4 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_X byte02 b["0"] in
let byte04 := write_R byte03 (proj1_sig uvar1_0) in
let byte05 := write_B byte04 (proj1_sig uvar1_1) in
let result0 := [byte05] in
let byte11 := HB["69"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_2) in
let byte23 := write_rm byte22 (proj1_sig uvar3_3) in
let result2 := [byte23] in
do byte31 <- bits_to_bytes (proj1_sig uvar32_4);
let result3 := byte31 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Psubq_GvEv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["2B"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_3) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Psubq_EvGv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["29"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_3) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Psubq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["81"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 b["101"] in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
do byte31 <- bits_to_bytes (proj1_sig uvar32_4);
let result3 := byte31 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Paddq_GvEv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["03"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_3) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Paddq_EvGv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["01"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_3) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Paddq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["81"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 b["000"] in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
do byte31 <- bits_to_bytes (proj1_sig uvar32_4);
let result3 := byte31 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pnegq AddrE uvar1_0 uvar1_1 uvar1_2 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["F7"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 b["011"] in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pleaq AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["8D"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_3) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pmovq_EvGv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["89"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_3) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pmovq_GvEv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 (proj1_sig uvar1_0) in
let byte04 := write_X byte03 (proj1_sig uvar1_1) in
let byte05 := write_B byte04 (proj1_sig uvar1_2) in
let result0 := [byte05] in
let byte11 := HB["8B"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_3) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pmovq_ri uvar1_0 uvar3_1 uvar64_2 => let byte00 := HB["00"] in
let byte01 := write_rmagic byte00 b["0100"] in
let byte02 := write_W byte01 b["1"] in
let byte03 := write_R byte02 b["0"] in
let byte04 := write_X byte03 b["0"] in
let byte05 := write_B byte04 (proj1_sig uvar1_0) in
let result0 := [byte05] in
let byte10 := HB["00"] in
let byte11 := write_page byte10 b["1"] in
let byte12 := write_row byte11 b["0001"] in
let byte13 := write_col byte12 (proj1_sig uvar3_1) in
let result1 := [byte13] in
do byte21 <- bits_to_bytes (proj1_sig uvar64_2);
let result2 := byte21 in
OK (result0 ++ result1 ++ result2)
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
| Pbsqrtsd uvar3_0 uvar3_1 => let byte01 := HB["F2"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["51"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
| Psbbl_rr uvar3_0 uvar3_1 => let byte01 := HB["19"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 (proj1_sig uvar3_0) in
let byte13 := write_rm byte12 (proj1_sig uvar3_1) in
let result1 := [byte13] in
OK (result0 ++ result1)
| Prep_movsl => let byte01 := HB["F3"] in
let result0 := [byte01] in
let byte11 := HB["A5"] in
let result1 := [byte11] in
OK (result0 ++ result1)
| Pmovsq_rm AddrE uvar3_0 => let byte01 := HB["F3"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["7E"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_reg_op byte30 (proj1_sig uvar3_0) in
do byte32 <- encode_AddrE AddrE byte31;
let result3 := byte32 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pmovsq_mr AddrE uvar3_0 => let byte01 := HB["66"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["D6"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_reg_op byte30 (proj1_sig uvar3_0) in
do byte32 <- encode_AddrE AddrE byte31;
let result3 := byte32 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pminsd uvar3_0 uvar3_1 => let byte01 := HB["F2"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["5D"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pmaxsd uvar3_0 uvar3_1 => let byte01 := HB["F2"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["5F"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
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
| Paddl_rr uvar3_0 uvar3_1 => let byte01 := HB["01"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 (proj1_sig uvar3_0) in
let byte13 := write_rm byte12 (proj1_sig uvar3_1) in
let result1 := [byte13] in
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
| Pandps_fm AddrE uvar3_0 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["58"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_0) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pxorps_GvEv AddrE uvar3_0 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["57"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_0) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pxorpd_GvEv AddrE uvar3_0 => let byte01 := HB["66"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["57"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_reg_op byte30 (proj1_sig uvar3_0) in
do byte32 <- encode_AddrE AddrE byte31;
let result3 := byte32 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pcomiss_ff uvar3_0 uvar3_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["2F"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_0) in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Pcomisd_ff uvar3_0 uvar3_1 => let byte01 := HB["66"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["2F"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pdivss_ff uvar3_0 uvar3_1 => let byte01 := HB["F3"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["5E"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pdivsd_ff uvar3_0 uvar3_1 => let byte01 := HB["F2"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["5E"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pmuls_ff uvar3_0 uvar3_1 => let byte01 := HB["F3"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["59"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pmuld_ff uvar3_0 uvar3_1 => let byte01 := HB["F2"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["59"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
| Psubs_ff uvar3_0 uvar3_1 => let byte01 := HB["F3"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["5C"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
| Psubd_ff uvar3_0 uvar3_1 => let byte01 := HB["F2"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["5C"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
| Padds_ff uvar3_0 uvar3_1 => let byte01 := HB["F3"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["58"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
| Paddd_ff uvar3_0 uvar3_1 => let byte01 := HB["F2"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["58"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
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
| Ptestl_rr uvar3_0 uvar3_1 => let byte01 := HB["85"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 (proj1_sig uvar3_0) in
let byte13 := write_rm byte12 (proj1_sig uvar3_1) in
let result1 := [byte13] in
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
| Pcmpl_rr uvar3_0 uvar3_1 => let byte01 := HB["39"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 (proj1_sig uvar3_0) in
let byte13 := write_rm byte12 (proj1_sig uvar3_1) in
let result1 := [byte13] in
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
| Prolw_ri uvar3_0 uvar8_1 => let byte01 := HB["66"] in
let result0 := [byte01] in
let byte11 := HB["C1"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 b["000"] in
let byte23 := write_rm byte22 (proj1_sig uvar3_0) in
let result2 := [byte23] in
do byte31 <- bits_to_bytes (proj1_sig uvar8_1);
let result3 := byte31 in
OK (result0 ++ result1 ++ result2 ++ result3)
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
| Pxorl_rr uvar3_0 uvar3_1 => let byte01 := HB["31"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 (proj1_sig uvar3_0) in
let byte13 := write_rm byte12 (proj1_sig uvar3_1) in
let result1 := [byte13] in
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
| Porl_rr uvar3_0 uvar3_1 => let byte01 := HB["09"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 (proj1_sig uvar3_0) in
let byte13 := write_rm byte12 (proj1_sig uvar3_1) in
let result1 := [byte13] in
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
| Pandl_rr uvar3_0 uvar3_1 => let byte01 := HB["21"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 (proj1_sig uvar3_0) in
let byte13 := write_rm byte12 (proj1_sig uvar3_1) in
let result1 := [byte13] in
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
| Pimull_rr uvar3_0 uvar3_1 => let byte01 := HB["0F"] in
let result0 := [byte01] in
let byte11 := HB["AF"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_mod byte20 b["11"] in
let byte22 := write_reg_op byte21 (proj1_sig uvar3_0) in
let byte23 := write_rm byte22 (proj1_sig uvar3_1) in
let result2 := [byte23] in
OK (result0 ++ result1 ++ result2)
| Psubl_rr uvar3_0 uvar3_1 => let byte01 := HB["2B"] in
let result0 := [byte01] in
let byte10 := HB["00"] in
let byte11 := write_mod byte10 b["11"] in
let byte12 := write_reg_op byte11 (proj1_sig uvar3_0) in
let byte13 := write_rm byte12 (proj1_sig uvar3_1) in
let result1 := [byte13] in
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
| Pcvttss2si_rf uvar3_0 uvar3_1 => let byte01 := HB["F3"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["2C"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pcvtsi2sd_fr uvar3_0 uvar3_1 => let byte01 := HB["F2"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["2A"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pcvtsi2ss_fr uvar3_0 uvar3_1 => let byte01 := HB["F3"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["2A"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pcvttsd2si_rf uvar3_0 uvar3_1 => let byte01 := HB["F2"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["2C"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pcvtss2sd_ff uvar3_0 uvar3_1 => let byte01 := HB["F3"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["5A"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pcvtsd2ss_ff uvar3_0 uvar3_1 => let byte01 := HB["F2"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["5A"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_mod byte30 b["11"] in
let byte32 := write_reg_op byte31 (proj1_sig uvar3_0) in
let byte33 := write_rm byte32 (proj1_sig uvar3_1) in
let result3 := [byte33] in
OK (result0 ++ result1 ++ result2 ++ result3)
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
| Pmovw_rm AddrE uvar3_0 => let byte01 := HB["66"] in
let result0 := [byte01] in
let byte11 := HB["8B"] in
let result1 := [byte11] in
let byte20 := HB["00"] in
let byte21 := write_reg_op byte20 (proj1_sig uvar3_0) in
do byte22 <- encode_AddrE AddrE byte21;
let result2 := byte22 in
OK (result0 ++ result1 ++ result2)
| Pmovw_mr AddrE uvar3_0 => let byte01 := HB["66"] in
let result0 := [byte01] in
let byte11 := HB["89"] in
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
| Pmovss_fm AddrE uvar3_0 => let byte01 := HB["F3"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["10"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_reg_op byte30 (proj1_sig uvar3_0) in
do byte32 <- encode_AddrE AddrE byte31;
let result3 := byte32 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pmovss_mf AddrE uvar3_0 => let byte01 := HB["F3"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["11"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_reg_op byte30 (proj1_sig uvar3_0) in
do byte32 <- encode_AddrE AddrE byte31;
let result3 := byte32 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pmovsd_fm AddrE uvar3_0 => let byte01 := HB["F2"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["10"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_reg_op byte30 (proj1_sig uvar3_0) in
do byte32 <- encode_AddrE AddrE byte31;
let result3 := byte32 in
OK (result0 ++ result1 ++ result2 ++ result3)
| Pmovsd_mf AddrE uvar3_0 => let byte01 := HB["F2"] in
let result0 := [byte01] in
let byte11 := HB["0F"] in
let result1 := [byte11] in
let byte21 := HB["11"] in
let result2 := [byte21] in
let byte30 := HB["00"] in
let byte31 := write_reg_op byte30 (proj1_sig uvar3_0) in
do byte32 <- encode_AddrE AddrE byte31;
let result3 := byte32 in
OK (result0 ++ result1 ++ result2 ++ result3)
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
	if Ptestq_EvGv_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Ptestq_EvGv AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Ptestq_ri_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
do byte_seq1 <- try_first_n bytes3 4;
let uvar32_4 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_4 32 then
do bytes4 <- try_skip_n bytes3 4;
OK ((Ptestq_ri AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar32_4)), 6 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pcmpq_GvEv_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pcmpq_GvEv AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pcmpq_EvGv_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pcmpq_EvGv AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pcmpq_ri_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
do byte_seq1 <- try_first_n bytes3 4;
let uvar32_4 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_4 32 then
do bytes4 <- try_skip_n bytes3 4;
OK ((Pcmpq_ri AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar32_4)), 6 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Prorq_ri_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
do byte_seq1 <- try_first_n bytes3 1;
let uvar8_4 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar8_4 8 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Prorq_ri AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar8_4)), 3 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Psarq_ri_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
do byte_seq1 <- try_first_n bytes3 1;
let uvar8_4 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar8_4 8 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Psarq_ri AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar8_4)), 3 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Psarq_rcl_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Psarq_rcl AddrE (uvar1_0) (uvar1_1) (uvar1_2)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Psalq_ri_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
do byte_seq1 <- try_first_n bytes3 1;
let uvar8_4 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar8_4 8 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Psalq_ri AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar8_4)), 3 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Psalq_rcl_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Psalq_rcl AddrE (uvar1_0) (uvar1_1) (uvar1_2)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pnotq_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pnotq AddrE (uvar1_0) (uvar1_1) (uvar1_2)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pxorq_GvEv_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pxorq_GvEv AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pxorq_EvGv_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pxorq_EvGv AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pxorq_ri_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
do byte_seq1 <- try_first_n bytes3 4;
let uvar32_4 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_4 32 then
do bytes4 <- try_skip_n bytes3 4;
OK ((Pxorq_ri AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar32_4)), 6 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Porq_GvEv_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Porq_GvEv AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Porq_EvGv_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Porq_EvGv AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Porq_ri_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
do byte_seq1 <- try_first_n bytes3 4;
let uvar32_4 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_4 32 then
do bytes4 <- try_skip_n bytes3 4;
OK ((Porq_ri AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar32_4)), 6 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pandq_GvEv_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pandq_GvEv AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pandq_EvGv_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pandq_EvGv AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pandq_ri_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
do byte_seq1 <- try_first_n bytes3 4;
let uvar32_4 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_4 32 then
do bytes4 <- try_skip_n bytes3 4;
OK ((Pandq_ri AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar32_4)), 6 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pdivq_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_B byte0 in
if assertLength uvar1_0 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_1 := read_rm byte1 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pdivq (uvar1_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pidivq_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_B byte0 in
if assertLength uvar1_0 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_1 := read_rm byte1 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pidivq (uvar1_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pmulq_r_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_B byte0 in
if assertLength uvar1_0 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_1 := read_rm byte1 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pmulq_r (uvar1_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pimulq_GvEv_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte1 <- try_get_n bytes3 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes3;
do bytes4 <- try_skip_n bytes3 localLength0;
OK ((Pimulq_GvEv AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 3 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pimulq_r_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_B byte0 in
if assertLength uvar1_0 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_1 := read_rm byte1 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pimulq_r (uvar1_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pimulq_ri_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_B byte0 in
if assertLength uvar1_1 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_2 := read_reg_op byte1 in
if assertLength uvar3_2 3 then
let uvar3_3 := read_rm byte1 in
if assertLength uvar3_3 3 then
do bytes3 <- try_skip_n bytes2 1;
do byte_seq2 <- try_first_n bytes3 4;
let uvar32_4 := bytes_to_bits_opt byte_seq2 in
if assertLength uvar32_4 32 then
do bytes4 <- try_skip_n bytes3 4;
OK ((Pimulq_ri (uvar1_0) (uvar1_1) (uvar3_2) (uvar3_3) (uvar32_4)), 7)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Psubq_GvEv_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Psubq_GvEv AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Psubq_EvGv_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Psubq_EvGv AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Psubq_ri_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
do byte_seq1 <- try_first_n bytes3 4;
let uvar32_4 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_4 32 then
do bytes4 <- try_skip_n bytes3 4;
OK ((Psubq_ri AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar32_4)), 6 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Paddq_GvEv_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Paddq_GvEv AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Paddq_EvGv_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Paddq_EvGv AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Paddq_ri_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
do byte_seq1 <- try_first_n bytes3 4;
let uvar32_4 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar32_4 32 then
do bytes4 <- try_skip_n bytes3 4;
OK ((Paddq_ri AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar32_4)), 6 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pnegq_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pnegq AddrE (uvar1_0) (uvar1_1) (uvar1_2)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pleaq_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pleaq AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pmovq_EvGv_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pmovq_EvGv AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pmovq_GvEv_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_R byte0 in
if assertLength uvar1_0 1 then
let uvar1_1 := read_X byte0 in
if assertLength uvar1_1 1 then
let uvar1_2 := read_B byte0 in
if assertLength uvar1_2 1 then
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte1 <- try_get_n bytes2 0;
let uvar3_3 := read_reg_op byte1 in
if assertLength uvar3_3 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pmovq_GvEv AddrE (uvar1_0) (uvar1_1) (uvar1_2) (uvar3_3)), 2 + localLength0)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pmovq_ri_bp bin then
let bytes0 := code in
do byte0 <- try_get_n bytes0 0;
let uvar1_0 := read_B byte0 in
if assertLength uvar1_0 1 then
do bytes1 <- try_skip_n bytes0 1;
do byte1 <- try_get_n bytes1 0;
let uvar3_1 := read_col byte1 in
if assertLength uvar3_1 3 then
do bytes2 <- try_skip_n bytes1 1;
do byte_seq2 <- try_first_n bytes2 8;
let uvar64_2 := bytes_to_bits_opt byte_seq2 in
if assertLength uvar64_2 64 then
do bytes3 <- try_skip_n bytes2 8;
OK ((Pmovq_ri (uvar1_0) (uvar3_1) (uvar64_2)), 10)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
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
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Pbsqrtsd (uvar3_0) (uvar3_1)), 4)
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
do bytes2 <- try_skip_n bytes1 1;
OK ((Prep_movsl), 2)
else

	if Pmovsq_rm_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes3;
do bytes4 <- try_skip_n bytes3 localLength0;
OK ((Pmovsq_rm AddrE (uvar3_0)), 3 + localLength0)
else Error(msg"impossible")
else

	if Pmovsq_mr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes3;
do bytes4 <- try_skip_n bytes3 localLength0;
OK ((Pmovsq_mr AddrE (uvar3_0)), 3 + localLength0)
else Error(msg"impossible")
else

	if Pminsd_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Pminsd (uvar3_0) (uvar3_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pmaxsd_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Pmaxsd (uvar3_0) (uvar3_1)), 4)
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

	if Paddl_rr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Paddl_rr (uvar3_0) (uvar3_1)), 2)
else Error(msg"impossible")
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

	if Pandps_fm_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pandps_fm AddrE (uvar3_0)), 2 + localLength0)
else Error(msg"impossible")
else

	if Pxorps_GvEv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pxorps_GvEv AddrE (uvar3_0)), 2 + localLength0)
else Error(msg"impossible")
else

	if Pxorpd_GvEv_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes3;
do bytes4 <- try_skip_n bytes3 localLength0;
OK ((Pxorpd_GvEv AddrE (uvar3_0)), 3 + localLength0)
else Error(msg"impossible")
else

	if Pcomiss_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pcomiss_ff (uvar3_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pcomisd_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Pcomisd_ff (uvar3_0) (uvar3_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pdivss_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Pdivss_ff (uvar3_0) (uvar3_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pdivsd_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Pdivsd_ff (uvar3_0) (uvar3_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pmuls_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Pmuls_ff (uvar3_0) (uvar3_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pmuld_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Pmuld_ff (uvar3_0) (uvar3_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Psubs_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Psubs_ff (uvar3_0) (uvar3_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Psubd_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Psubd_ff (uvar3_0) (uvar3_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Padds_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Padds_ff (uvar3_0) (uvar3_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Paddd_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Paddd_ff (uvar3_0) (uvar3_1)), 4)
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

	if Ptestl_rr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Ptestl_rr (uvar3_0) (uvar3_1)), 2)
else Error(msg"impossible")
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

	if Pcmpl_rr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Pcmpl_rr (uvar3_0) (uvar3_1)), 2)
else Error(msg"impossible")
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
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_rm byte0 in
if assertLength uvar3_0 3 then
do bytes3 <- try_skip_n bytes2 1;
do byte_seq1 <- try_first_n bytes3 1;
let uvar8_1 := bytes_to_bits_opt byte_seq1 in
if assertLength uvar8_1 8 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Prolw_ri (uvar3_0) (uvar8_1)), 4)
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

	if Pxorl_rr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Pxorl_rr (uvar3_0) (uvar3_1)), 2)
else Error(msg"impossible")
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

	if Porl_rr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Porl_rr (uvar3_0) (uvar3_1)), 2)
else Error(msg"impossible")
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

	if Pandl_rr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Pandl_rr (uvar3_0) (uvar3_1)), 2)
else Error(msg"impossible")
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

	if Pimull_rr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes3 <- try_skip_n bytes2 1;
OK ((Pimull_rr (uvar3_0) (uvar3_1)), 3)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Psubl_rr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do byte0 <- try_get_n bytes1 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes2 <- try_skip_n bytes1 1;
OK ((Psubl_rr (uvar3_0) (uvar3_1)), 2)
else Error(msg"impossible")
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

	if Pcvttss2si_rf_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Pcvttss2si_rf (uvar3_0) (uvar3_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pcvtsi2sd_fr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Pcvtsi2sd_fr (uvar3_0) (uvar3_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pcvtsi2ss_fr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Pcvtsi2ss_fr (uvar3_0) (uvar3_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pcvttsd2si_rf_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Pcvttsd2si_rf (uvar3_0) (uvar3_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pcvtss2sd_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Pcvtss2sd_ff (uvar3_0) (uvar3_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if Pcvtsd2ss_ff_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
let uvar3_1 := read_rm byte0 in
if assertLength uvar3_1 3 then
do bytes4 <- try_skip_n bytes3 1;
OK ((Pcvtsd2ss_ff (uvar3_0) (uvar3_1)), 4)
else Error(msg"impossible")
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

	if Pmovw_rm_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pmovw_rm AddrE (uvar3_0)), 2 + localLength0)
else Error(msg"impossible")
else

	if Pmovw_mr_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do byte0 <- try_get_n bytes2 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes2;
do bytes3 <- try_skip_n bytes2 localLength0;
OK ((Pmovw_mr AddrE (uvar3_0)), 2 + localLength0)
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

	if Pmovss_fm_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes3;
do bytes4 <- try_skip_n bytes3 localLength0;
OK ((Pmovss_fm AddrE (uvar3_0)), 3 + localLength0)
else Error(msg"impossible")
else

	if Pmovss_mf_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes3;
do bytes4 <- try_skip_n bytes3 localLength0;
OK ((Pmovss_mf AddrE (uvar3_0)), 3 + localLength0)
else Error(msg"impossible")
else

	if Pmovsd_fm_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes3;
do bytes4 <- try_skip_n bytes3 localLength0;
OK ((Pmovsd_fm AddrE (uvar3_0)), 3 + localLength0)
else Error(msg"impossible")
else

	if Pmovsd_mf_bp bin then
let bytes0 := code in
do bytes1 <- try_skip_n bytes0 1;
do bytes2 <- try_skip_n bytes1 1;
do bytes3 <- try_skip_n bytes2 1;
do byte0 <- try_get_n bytes3 0;
let uvar3_0 := read_reg_op byte0 in
if assertLength uvar3_0 3 then
do (AddrE, localLength0) <- decode_AddrE bytes3;
do bytes4 <- try_skip_n bytes3 localLength0;
OK ((Pmovsd_mf AddrE (uvar3_0)), 3 + localLength0)
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

