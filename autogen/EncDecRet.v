Require Import Coqlib Integers Errors.
Require Import encode.Hex encode.Bits Memdata.
Require Import Encode  VerificationCondition.
Import String Ascii.
Import List.
Import ListNotations.
Import Hex Bits.
Require Import BPProperty.

(* use a simple tactic to solve obligation *)
Obligation Tactic := auto.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.





Definition write_fm (Instr:bits)  (fm_value:bits) : bits :=
	fm_value++(Instr>@[4]).

Definition read_fm (Instr:bits) : bits :=
	Instr~@[4].

Definition write_funct2 (Instr:bits)  (funct2_value:bits) : bits :=
	(Instr~@[5])++funct2_value++(Instr>@[7]).

Definition read_funct2 (Instr:bits) : bits :=
	(Instr>@[5])~@[2].

Definition write_funct3 (Instr:bits)  (funct3_value:bits) : bits :=
	(Instr~@[17])++funct3_value++(Instr>@[20]).

Definition read_funct3 (Instr:bits) : bits :=
	(Instr>@[17])~@[3].

Definition write_funct7 (Instr:bits)  (funct7_value:bits) : bits :=
	funct7_value++(Instr>@[7]).

Definition read_funct7 (Instr:bits) : bits :=
	Instr~@[7].

Definition write_immB1 (Instr:bits)  (immB1_value:bits) : bits :=
	(Instr~@[24])++immB1_value++(Instr>@[25]).

Definition read_immB1 (Instr:bits) : bits :=
	(Instr>@[24])~@[1].

Definition write_immB2 (Instr:bits)  (immB2_value:bits) : bits :=
	(Instr~@[20])++immB2_value++(Instr>@[24]).

Definition read_immB2 (Instr:bits) : bits :=
	(Instr>@[20])~@[4].

Definition write_immB3 (Instr:bits)  (immB3_value:bits) : bits :=
	(Instr~@[1])++immB3_value++(Instr>@[7]).

Definition read_immB3 (Instr:bits) : bits :=
	(Instr>@[1])~@[6].

Definition write_immB4 (Instr:bits)  (immB4_value:bits) : bits :=
	immB4_value++(Instr>@[1]).

Definition read_immB4 (Instr:bits) : bits :=
	Instr~@[1].

Definition write_immI (Instr:bits)  (immI_value:bits) : bits :=
	immI_value++(Instr>@[12]).

Definition read_immI (Instr:bits) : bits :=
	Instr~@[12].

Definition write_immISp32 (Instr:bits)  (immISp32_value:bits) : bits :=
	immISp32_value++(Instr>@[7]).

Definition read_immISp32 (Instr:bits) : bits :=
	Instr~@[7].

Definition write_immISp64 (Instr:bits)  (immISp64_value:bits) : bits :=
	immISp64_value++(Instr>@[8]).

Definition read_immISp64 (Instr:bits) : bits :=
	Instr~@[8].

Definition write_immJ1 (Instr:bits)  (immJ1_value:bits) : bits :=
	(Instr~@[12])++immJ1_value++(Instr>@[20]).

Definition read_immJ1 (Instr:bits) : bits :=
	(Instr>@[12])~@[8].

Definition write_immJ2 (Instr:bits)  (immJ2_value:bits) : bits :=
	(Instr~@[11])++immJ2_value++(Instr>@[12]).

Definition read_immJ2 (Instr:bits) : bits :=
	(Instr>@[11])~@[1].

Definition write_immJ3 (Instr:bits)  (immJ3_value:bits) : bits :=
	(Instr~@[1])++immJ3_value++(Instr>@[11]).

Definition read_immJ3 (Instr:bits) : bits :=
	(Instr>@[1])~@[10].

Definition write_immJ4 (Instr:bits)  (immJ4_value:bits) : bits :=
	immJ4_value++(Instr>@[1]).

Definition read_immJ4 (Instr:bits) : bits :=
	Instr~@[1].

Definition write_immS1 (Instr:bits)  (immS1_value:bits) : bits :=
	(Instr~@[20])++immS1_value++(Instr>@[25]).

Definition read_immS1 (Instr:bits) : bits :=
	(Instr>@[20])~@[5].

Definition write_immS2 (Instr:bits)  (immS2_value:bits) : bits :=
	immS2_value++(Instr>@[7]).

Definition read_immS2 (Instr:bits) : bits :=
	Instr~@[7].

Definition write_immU (Instr:bits)  (immU_value:bits) : bits :=
	immU_value++(Instr>@[20]).

Definition read_immU (Instr:bits) : bits :=
	Instr~@[20].

Definition write_opcode (Instr:bits)  (opcode_value:bits) : bits :=
	(Instr~@[25])++opcode_value.

Definition read_opcode (Instr:bits) : bits :=
	(Instr>@[25]).

Definition write_pred (Instr:bits)  (pred_value:bits) : bits :=
	(Instr~@[4])++pred_value++(Instr>@[8]).

Definition read_pred (Instr:bits) : bits :=
	(Instr>@[4])~@[4].

Definition write_rd (Instr:bits)  (rd_value:bits) : bits :=
	(Instr~@[20])++rd_value++(Instr>@[25]).

Definition read_rd (Instr:bits) : bits :=
	(Instr>@[20])~@[5].

Definition write_rm (Instr:bits)  (rm_value:bits) : bits :=
	(Instr~@[17])++rm_value++(Instr>@[20]).

Definition read_rm (Instr:bits) : bits :=
	(Instr>@[17])~@[3].

Definition write_rs1 (Instr:bits)  (rs1_value:bits) : bits :=
	(Instr~@[12])++rs1_value++(Instr>@[17]).

Definition read_rs1 (Instr:bits) : bits :=
	(Instr>@[12])~@[5].

Definition write_rs2 (Instr:bits)  (rs2_value:bits) : bits :=
	(Instr~@[7])++rs2_value++(Instr>@[12]).

Definition read_rs2 (Instr:bits) : bits :=
	(Instr>@[7])~@[5].

Definition write_rs3 (Instr:bits)  (rs3_value:bits) : bits :=
	rs3_value++(Instr>@[5]).

Definition read_rs3 (Instr:bits) : bits :=
	Instr~@[5].

Definition write_shamt32 (Instr:bits)  (shamt32_value:bits) : bits :=
	(Instr~@[7])++shamt32_value++(Instr>@[12]).

Definition read_shamt32 (Instr:bits) : bits :=
	(Instr>@[7])~@[5].

Definition write_shamt64 (Instr:bits)  (shamt64_value:bits) : bits :=
	(Instr~@[6])++shamt64_value++(Instr>@[12]).

Definition read_shamt64 (Instr:bits) : bits :=
	(Instr>@[6])~@[6].

Definition write_succ (Instr:bits)  (succ_value:bits) : bits :=
	(Instr~@[8])++succ_value++(Instr>@[12]).

Definition read_succ (Instr:bits) : bits :=
	(Instr>@[8])~@[4].


Hint Unfold read_fm write_fm read_funct2 write_funct2 read_funct3 write_funct3 read_funct7 write_funct7 read_immB1 write_immB1 read_immB2 write_immB2 read_immB3 write_immB3 read_immB4 write_immB4 read_immI write_immI read_immISp32 write_immISp32 read_immISp64 write_immISp64 read_immJ1 write_immJ1 read_immJ2 write_immJ2 read_immJ3 write_immJ3 read_immJ4 write_immJ4 read_immS1 write_immS1 read_immS2 write_immS2 read_immU write_immU read_opcode write_opcode read_pred write_pred read_rd write_rd read_rm write_rm read_rs1 write_rs1 read_rs2 write_rs2 read_rs3 write_rs3 read_shamt32 write_shamt32 read_shamt64 write_shamt64 read_succ write_succ:bitfields.

Hint Unfold fcvtsd_bp fcvtds_bp fcvtdlu_bp fcvtdl_bp fcvtlud_bp fcvtld_bp fcvtdwu_bp fcvtdw_bp fcvtwud_bp fcvtwd_bp fnmsubd_bp fnmaddd_bp fmsubd_bp fmaddd_bp fsqrtd_bp fled_bp fltd_bp feqd_bp fmaxd_bp fmind_bp fdivd_bp fmuld_bp fsubd_bp faddd_bp fsgnjxd_bp fsgnjnd_bp fsd_bp fload_bp fcvtslu_bp fcvtsl_bp fcvtlus_bp fcvtls_bp fcvtswu_bp fcvtsw_bp fcvtwus_bp fcvtws_bp fnmsubs_bp fnmadds_bp fmsubs_bp fmadds_bp fsqrts_bp fles_bp flts_bp feqs_bp fmaxs_bp fmins_bp fdivs_bp fmuls_bp fsubs_bp fadds_bp fsgnjxs_bp fsgnjns_bp fsw_bp flw_bp fmvdx_bp fmvxd_bp fmvwx_bp fmvxw_bp fsgnjd_bp fence_bp sd_bp sw_bp sh_bp sb_bp ld_bp lw_bp lhu_bp lh_bp lbu_bp lb_bp bgeu_bp bge_bp bltu_bp blt_bp bne_bp beq_bp auipc_bp jalr_bp jal_bp sraw_bp srlw_bp sllw_bp remuw_bp remw_bp divuw_bp divw_bp mulw_bp subw_bp addw_bp sraiw_bp srliw_bp slliw_bp srai_bp srli_bp slli_bp addiw_bp sra_bp srl_bp sll_bp xor_bp or_bp and_bp sltu_bp slt_bp remu_bp rem_bp divu_bp div_bp mulhu_bp mulh_bp mul_bp sub_bp add_bp lui_bp xori_bp ori_bp andi_bp sltiu_bp slti_bp addi_bp :Instruction_bpdb.
Lemma Instruction_bp_in_list0: 
In fcvtsd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list1: 
In fcvtds_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list2: 
In fcvtdlu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list3: 
In fcvtdl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list4: 
In fcvtlud_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list5: 
In fcvtld_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list6: 
In fcvtdwu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list7: 
In fcvtdw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list8: 
In fcvtwud_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list9: 
In fcvtwd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list10: 
In fnmsubd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list11: 
In fnmaddd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list12: 
In fmsubd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list13: 
In fmaddd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list14: 
In fsqrtd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list15: 
In fled_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list16: 
In fltd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list17: 
In feqd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list18: 
In fmaxd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list19: 
In fmind_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list20: 
In fdivd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list21: 
In fmuld_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list22: 
In fsubd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list23: 
In faddd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list24: 
In fsgnjxd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list25: 
In fsgnjnd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list26: 
In fsd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list27: 
In fload_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list28: 
In fcvtslu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list29: 
In fcvtsl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list30: 
In fcvtlus_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list31: 
In fcvtls_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list32: 
In fcvtswu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list33: 
In fcvtsw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list34: 
In fcvtwus_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list35: 
In fcvtws_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list36: 
In fnmsubs_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list37: 
In fnmadds_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list38: 
In fmsubs_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list39: 
In fmadds_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list40: 
In fsqrts_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list41: 
In fles_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list42: 
In flts_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list43: 
In feqs_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list44: 
In fmaxs_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list45: 
In fmins_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list46: 
In fdivs_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list47: 
In fmuls_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list48: 
In fsubs_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list49: 
In fadds_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list50: 
In fsgnjxs_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list51: 
In fsgnjns_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list52: 
In fsw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list53: 
In flw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list54: 
In fmvdx_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list55: 
In fmvxd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list56: 
In fmvwx_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list57: 
In fmvxw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list58: 
In fsgnjd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list59: 
In fence_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list60: 
In sd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list61: 
In sw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list62: 
In sh_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list63: 
In sb_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list64: 
In ld_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list65: 
In lw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list66: 
In lhu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list67: 
In lh_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list68: 
In lbu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list69: 
In lb_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list70: 
In bgeu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list71: 
In bge_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list72: 
In bltu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list73: 
In blt_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list74: 
In bne_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list75: 
In beq_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list76: 
In auipc_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list77: 
In jalr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list78: 
In jal_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list79: 
In sraw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list80: 
In srlw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list81: 
In sllw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list82: 
In remuw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list83: 
In remw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list84: 
In divuw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list85: 
In divw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list86: 
In mulw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list87: 
In subw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list88: 
In addw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list89: 
In sraiw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list90: 
In srliw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list91: 
In slliw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list92: 
In srai_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list93: 
In srli_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list94: 
In slli_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list95: 
In addiw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list96: 
In sra_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list97: 
In srl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list98: 
In sll_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list99: 
In xor_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list100: 
In or_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list101: 
In and_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list102: 
In sltu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list103: 
In slt_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list104: 
In remu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list105: 
In rem_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list106: 
In divu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list107: 
In div_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list108: 
In mulhu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list109: 
In mulh_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list110: 
In mul_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list111: 
In sub_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list112: 
In add_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list113: 
In lui_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list114: 
In xori_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list115: 
In ori_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list116: 
In andi_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list117: 
In sltiu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list118: 
In slti_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list119: 
In addi_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Inductive Instruction: Type :=
| fcvtsd(uvar5_0:u5)(uvar5_1:u5)
| fcvtds(uvar5_0:u5)(uvar5_1:u5)
| fcvtdlu(uvar5_0:u5)(uvar5_1:u5)
| fcvtdl(uvar5_0:u5)(uvar5_1:u5)
| fcvtlud(uvar5_0:u5)(uvar5_1:u5)
| fcvtld(uvar5_0:u5)(uvar5_1:u5)
| fcvtdwu(uvar5_0:u5)(uvar5_1:u5)
| fcvtdw(uvar5_0:u5)(uvar5_1:u5)
| fcvtwud(uvar5_0:u5)(uvar5_1:u5)
| fcvtwd(uvar5_0:u5)(uvar5_1:u5)
| fnmsubd(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar5_3:u5)
| fnmaddd(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar5_3:u5)
| fmsubd(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar5_3:u5)
| fmaddd(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar5_3:u5)
| fsqrtd(uvar5_0:u5)(uvar5_1:u5)
| fled(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fltd(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| feqd(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fmaxd(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fmind(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fdivd(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fmuld(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fsubd(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| faddd(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fsgnjxd(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fsgnjnd(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fsd(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar7_3:u7)
| fload(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| fcvtslu(uvar5_0:u5)(uvar5_1:u5)
| fcvtsl(uvar5_0:u5)(uvar5_1:u5)
| fcvtlus(uvar5_0:u5)(uvar5_1:u5)
| fcvtls(uvar5_0:u5)(uvar5_1:u5)
| fcvtswu(uvar5_0:u5)(uvar5_1:u5)
| fcvtsw(uvar5_0:u5)(uvar5_1:u5)
| fcvtwus(uvar5_0:u5)(uvar5_1:u5)
| fcvtws(uvar5_0:u5)(uvar5_1:u5)
| fnmsubs(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar5_3:u5)
| fnmadds(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar5_3:u5)
| fmsubs(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar5_3:u5)
| fmadds(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar5_3:u5)
| fsqrts(uvar5_0:u5)(uvar5_1:u5)
| fles(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| flts(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| feqs(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fmaxs(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fmins(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fdivs(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fmuls(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fsubs(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fadds(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fsgnjxs(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fsgnjns(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fsw(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar7_3:u7)
| flw(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| fmvdx(uvar5_0:u5)(uvar5_1:u5)
| fmvxd(uvar5_0:u5)(uvar5_1:u5)
| fmvwx(uvar5_0:u5)(uvar5_1:u5)
| fmvxw(uvar5_0:u5)(uvar5_1:u5)
| fsgnjd(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fence(uvar5_0:u5)(uvar5_1:u5)(uvar4_2:u4)(uvar4_3:u4)(uvar4_4:u4)
| sd(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar7_3:u7)
| sw(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar7_3:u7)
| sh(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar7_3:u7)
| sb(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar7_3:u7)
| ld(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| lw(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| lhu(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| lh(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| lbu(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| lb(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| bgeu(uvar1_0:u1)(uvar4_1:u4)(uvar5_2:u5)(uvar5_3:u5)(uvar6_4:u6)(uvar1_5:u1)
| bge(uvar1_0:u1)(uvar4_1:u4)(uvar5_2:u5)(uvar5_3:u5)(uvar6_4:u6)(uvar1_5:u1)
| bltu(uvar1_0:u1)(uvar4_1:u4)(uvar5_2:u5)(uvar5_3:u5)(uvar6_4:u6)(uvar1_5:u1)
| blt(uvar1_0:u1)(uvar4_1:u4)(uvar5_2:u5)(uvar5_3:u5)(uvar6_4:u6)(uvar1_5:u1)
| bne(uvar1_0:u1)(uvar4_1:u4)(uvar5_2:u5)(uvar5_3:u5)(uvar6_4:u6)(uvar1_5:u1)
| beq(uvar1_0:u1)(uvar4_1:u4)(uvar5_2:u5)(uvar5_3:u5)(uvar6_4:u6)(uvar1_5:u1)
| auipc(uvar5_0:u5)(uvar20_1:u20)
| jalr(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| jal(uvar5_0:u5)(uvar8_1:u8)(uvar1_2:u1)(uvar10_3:u10)(uvar1_4:u1)
| sraw(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| srlw(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| sllw(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| remuw(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| remw(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| divuw(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| divw(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| mulw(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| subw(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| addw(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| sraiw(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| srliw(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| slliw(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| srai(uvar5_0:u5)(uvar5_1:u5)(uvar6_2:u6)
| srli(uvar5_0:u5)(uvar5_1:u5)(uvar6_2:u6)
| slli(uvar5_0:u5)(uvar5_1:u5)(uvar6_2:u6)
| addiw(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| sra(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| srl(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| sll(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| xor(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| or(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| and(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| sltu(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| slt(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| remu(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| rem(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| divu(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| div(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| mulhu(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| mulh(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| mul(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| sub(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| add(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| lui(uvar5_0:u5)(uvar20_1:u20)
| xori(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| ori(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| andi(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| sltiu(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| slti(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| addi(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12).
Inductive Instruction_op: Type :=
| fcvtsd_op
| fcvtds_op
| fcvtdlu_op
| fcvtdl_op
| fcvtlud_op
| fcvtld_op
| fcvtdwu_op
| fcvtdw_op
| fcvtwud_op
| fcvtwd_op
| fnmsubd_op
| fnmaddd_op
| fmsubd_op
| fmaddd_op
| fsqrtd_op
| fled_op
| fltd_op
| feqd_op
| fmaxd_op
| fmind_op
| fdivd_op
| fmuld_op
| fsubd_op
| faddd_op
| fsgnjxd_op
| fsgnjnd_op
| fsd_op
| fload_op
| fcvtslu_op
| fcvtsl_op
| fcvtlus_op
| fcvtls_op
| fcvtswu_op
| fcvtsw_op
| fcvtwus_op
| fcvtws_op
| fnmsubs_op
| fnmadds_op
| fmsubs_op
| fmadds_op
| fsqrts_op
| fles_op
| flts_op
| feqs_op
| fmaxs_op
| fmins_op
| fdivs_op
| fmuls_op
| fsubs_op
| fadds_op
| fsgnjxs_op
| fsgnjns_op
| fsw_op
| flw_op
| fmvdx_op
| fmvxd_op
| fmvwx_op
| fmvxw_op
| fsgnjd_op
| fence_op
| sd_op
| sw_op
| sh_op
| sb_op
| ld_op
| lw_op
| lhu_op
| lh_op
| lbu_op
| lb_op
| bgeu_op
| bge_op
| bltu_op
| blt_op
| bne_op
| beq_op
| auipc_op
| jalr_op
| jal_op
| sraw_op
| srlw_op
| sllw_op
| remuw_op
| remw_op
| divuw_op
| divw_op
| mulw_op
| subw_op
| addw_op
| sraiw_op
| srliw_op
| slliw_op
| srai_op
| srli_op
| slli_op
| addiw_op
| sra_op
| srl_op
| sll_op
| xor_op
| or_op
| and_op
| sltu_op
| slt_op
| remu_op
| rem_op
| divu_op
| div_op
| mulhu_op
| mulh_op
| mul_op
| sub_op
| add_op
| lui_op
| xori_op
| ori_op
| andi_op
| sltiu_op
| slti_op
| addi_op.
Definition Instruction_to_op element  :=
	match element with
| fcvtsd _ _ => fcvtsd_op
| fcvtds _ _ => fcvtds_op
| fcvtdlu _ _ => fcvtdlu_op
| fcvtdl _ _ => fcvtdl_op
| fcvtlud _ _ => fcvtlud_op
| fcvtld _ _ => fcvtld_op
| fcvtdwu _ _ => fcvtdwu_op
| fcvtdw _ _ => fcvtdw_op
| fcvtwud _ _ => fcvtwud_op
| fcvtwd _ _ => fcvtwd_op
| fnmsubd _ _ _ _ => fnmsubd_op
| fnmaddd _ _ _ _ => fnmaddd_op
| fmsubd _ _ _ _ => fmsubd_op
| fmaddd _ _ _ _ => fmaddd_op
| fsqrtd _ _ => fsqrtd_op
| fled _ _ _ => fled_op
| fltd _ _ _ => fltd_op
| feqd _ _ _ => feqd_op
| fmaxd _ _ _ => fmaxd_op
| fmind _ _ _ => fmind_op
| fdivd _ _ _ => fdivd_op
| fmuld _ _ _ => fmuld_op
| fsubd _ _ _ => fsubd_op
| faddd _ _ _ => faddd_op
| fsgnjxd _ _ _ => fsgnjxd_op
| fsgnjnd _ _ _ => fsgnjnd_op
| fsd _ _ _ _ => fsd_op
| fload _ _ _ => fload_op
| fcvtslu _ _ => fcvtslu_op
| fcvtsl _ _ => fcvtsl_op
| fcvtlus _ _ => fcvtlus_op
| fcvtls _ _ => fcvtls_op
| fcvtswu _ _ => fcvtswu_op
| fcvtsw _ _ => fcvtsw_op
| fcvtwus _ _ => fcvtwus_op
| fcvtws _ _ => fcvtws_op
| fnmsubs _ _ _ _ => fnmsubs_op
| fnmadds _ _ _ _ => fnmadds_op
| fmsubs _ _ _ _ => fmsubs_op
| fmadds _ _ _ _ => fmadds_op
| fsqrts _ _ => fsqrts_op
| fles _ _ _ => fles_op
| flts _ _ _ => flts_op
| feqs _ _ _ => feqs_op
| fmaxs _ _ _ => fmaxs_op
| fmins _ _ _ => fmins_op
| fdivs _ _ _ => fdivs_op
| fmuls _ _ _ => fmuls_op
| fsubs _ _ _ => fsubs_op
| fadds _ _ _ => fadds_op
| fsgnjxs _ _ _ => fsgnjxs_op
| fsgnjns _ _ _ => fsgnjns_op
| fsw _ _ _ _ => fsw_op
| flw _ _ _ => flw_op
| fmvdx _ _ => fmvdx_op
| fmvxd _ _ => fmvxd_op
| fmvwx _ _ => fmvwx_op
| fmvxw _ _ => fmvxw_op
| fsgnjd _ _ _ => fsgnjd_op
| fence _ _ _ _ _ => fence_op
| sd _ _ _ _ => sd_op
| sw _ _ _ _ => sw_op
| sh _ _ _ _ => sh_op
| sb _ _ _ _ => sb_op
| ld _ _ _ => ld_op
| lw _ _ _ => lw_op
| lhu _ _ _ => lhu_op
| lh _ _ _ => lh_op
| lbu _ _ _ => lbu_op
| lb _ _ _ => lb_op
| bgeu _ _ _ _ _ _ => bgeu_op
| bge _ _ _ _ _ _ => bge_op
| bltu _ _ _ _ _ _ => bltu_op
| blt _ _ _ _ _ _ => blt_op
| bne _ _ _ _ _ _ => bne_op
| beq _ _ _ _ _ _ => beq_op
| auipc _ _ => auipc_op
| jalr _ _ _ => jalr_op
| jal _ _ _ _ _ => jal_op
| sraw _ _ _ => sraw_op
| srlw _ _ _ => srlw_op
| sllw _ _ _ => sllw_op
| remuw _ _ _ => remuw_op
| remw _ _ _ => remw_op
| divuw _ _ _ => divuw_op
| divw _ _ _ => divw_op
| mulw _ _ _ => mulw_op
| subw _ _ _ => subw_op
| addw _ _ _ => addw_op
| sraiw _ _ _ => sraiw_op
| srliw _ _ _ => srliw_op
| slliw _ _ _ => slliw_op
| srai _ _ _ => srai_op
| srli _ _ _ => srli_op
| slli _ _ _ => slli_op
| addiw _ _ _ => addiw_op
| sra _ _ _ => sra_op
| srl _ _ _ => srl_op
| sll _ _ _ => sll_op
| xor _ _ _ => xor_op
| or _ _ _ => or_op
| and _ _ _ => and_op
| sltu _ _ _ => sltu_op
| slt _ _ _ => slt_op
| remu _ _ _ => remu_op
| rem _ _ _ => rem_op
| divu _ _ _ => divu_op
| div _ _ _ => div_op
| mulhu _ _ _ => mulhu_op
| mulh _ _ _ => mulh_op
| mul _ _ _ => mul_op
| sub _ _ _ => sub_op
| add _ _ _ => add_op
| lui _ _ => lui_op
| xori _ _ _ => xori_op
| ori _ _ _ => ori_op
| andi _ _ _ => andi_op
| sltiu _ _ _ => sltiu_op
| slti _ _ _ => slti_op
| addi _ _ _ => addi_op
end.
Definition Instruction_op_to_bp element  :=
	match element with
| fcvtsd_op => fcvtsd_bp
| fcvtds_op => fcvtds_bp
| fcvtdlu_op => fcvtdlu_bp
| fcvtdl_op => fcvtdl_bp
| fcvtlud_op => fcvtlud_bp
| fcvtld_op => fcvtld_bp
| fcvtdwu_op => fcvtdwu_bp
| fcvtdw_op => fcvtdw_bp
| fcvtwud_op => fcvtwud_bp
| fcvtwd_op => fcvtwd_bp
| fnmsubd_op => fnmsubd_bp
| fnmaddd_op => fnmaddd_bp
| fmsubd_op => fmsubd_bp
| fmaddd_op => fmaddd_bp
| fsqrtd_op => fsqrtd_bp
| fled_op => fled_bp
| fltd_op => fltd_bp
| feqd_op => feqd_bp
| fmaxd_op => fmaxd_bp
| fmind_op => fmind_bp
| fdivd_op => fdivd_bp
| fmuld_op => fmuld_bp
| fsubd_op => fsubd_bp
| faddd_op => faddd_bp
| fsgnjxd_op => fsgnjxd_bp
| fsgnjnd_op => fsgnjnd_bp
| fsd_op => fsd_bp
| fload_op => fload_bp
| fcvtslu_op => fcvtslu_bp
| fcvtsl_op => fcvtsl_bp
| fcvtlus_op => fcvtlus_bp
| fcvtls_op => fcvtls_bp
| fcvtswu_op => fcvtswu_bp
| fcvtsw_op => fcvtsw_bp
| fcvtwus_op => fcvtwus_bp
| fcvtws_op => fcvtws_bp
| fnmsubs_op => fnmsubs_bp
| fnmadds_op => fnmadds_bp
| fmsubs_op => fmsubs_bp
| fmadds_op => fmadds_bp
| fsqrts_op => fsqrts_bp
| fles_op => fles_bp
| flts_op => flts_bp
| feqs_op => feqs_bp
| fmaxs_op => fmaxs_bp
| fmins_op => fmins_bp
| fdivs_op => fdivs_bp
| fmuls_op => fmuls_bp
| fsubs_op => fsubs_bp
| fadds_op => fadds_bp
| fsgnjxs_op => fsgnjxs_bp
| fsgnjns_op => fsgnjns_bp
| fsw_op => fsw_bp
| flw_op => flw_bp
| fmvdx_op => fmvdx_bp
| fmvxd_op => fmvxd_bp
| fmvwx_op => fmvwx_bp
| fmvxw_op => fmvxw_bp
| fsgnjd_op => fsgnjd_bp
| fence_op => fence_bp
| sd_op => sd_bp
| sw_op => sw_bp
| sh_op => sh_bp
| sb_op => sb_bp
| ld_op => ld_bp
| lw_op => lw_bp
| lhu_op => lhu_bp
| lh_op => lh_bp
| lbu_op => lbu_bp
| lb_op => lb_bp
| bgeu_op => bgeu_bp
| bge_op => bge_bp
| bltu_op => bltu_bp
| blt_op => blt_bp
| bne_op => bne_bp
| beq_op => beq_bp
| auipc_op => auipc_bp
| jalr_op => jalr_bp
| jal_op => jal_bp
| sraw_op => sraw_bp
| srlw_op => srlw_bp
| sllw_op => sllw_bp
| remuw_op => remuw_bp
| remw_op => remw_bp
| divuw_op => divuw_bp
| divw_op => divw_bp
| mulw_op => mulw_bp
| subw_op => subw_bp
| addw_op => addw_bp
| sraiw_op => sraiw_bp
| srliw_op => srliw_bp
| slliw_op => slliw_bp
| srai_op => srai_bp
| srli_op => srli_bp
| slli_op => slli_bp
| addiw_op => addiw_bp
| sra_op => sra_bp
| srl_op => srl_bp
| sll_op => sll_bp
| xor_op => xor_bp
| or_op => or_bp
| and_op => and_bp
| sltu_op => sltu_bp
| slt_op => slt_bp
| remu_op => remu_bp
| rem_op => rem_bp
| divu_op => divu_bp
| div_op => div_bp
| mulhu_op => mulhu_bp
| mulh_op => mulh_bp
| mul_op => mul_bp
| sub_op => sub_bp
| add_op => add_bp
| lui_op => lui_bp
| xori_op => xori_bp
| ori_op => ori_bp
| andi_op => andi_bp
| sltiu_op => sltiu_bp
| slti_op => slti_bp
| addi_op => addi_bp
end.
Definition encode_Instruction element  :=
	match element with
| fcvtsd uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_rs2 bits02 b["00001"] in
let bits04 := write_funct7 bits03 b["0100000"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtds uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_rs2 bits02 b["00000"] in
let bits04 := write_funct7 bits03 b["0100001"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtdlu uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_rs2 bits02 b["00011"] in
let bits04 := write_funct7 bits03 b["1101001"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtdl uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_rs2 bits02 b["00010"] in
let bits04 := write_funct7 bits03 b["1101001"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtlud uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_rs2 bits02 b["00011"] in
let bits04 := write_funct7 bits03 b["1100001"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtld uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_rs2 bits02 b["00010"] in
let bits04 := write_funct7 bits03 b["1100001"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtdwu uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_rs2 bits02 b["00001"] in
let bits04 := write_funct7 bits03 b["1101001"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtdw uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_rs2 bits02 b["00000"] in
let bits04 := write_funct7 bits03 b["1101001"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtwud uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_rs2 bits02 b["00001"] in
let bits04 := write_funct7 bits03 b["1100001"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtwd uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_rs2 bits02 b["00000"] in
let bits04 := write_funct7 bits03 b["1100001"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fnmsubd uvar5_0 uvar5_1 uvar5_2 uvar5_3 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1001011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct2 bits02 b["01"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let bits07 := write_rs3 bits06 (proj1_sig uvar5_3) in
let result0 := bits07 in
OK (result0)
| fnmaddd uvar5_0 uvar5_1 uvar5_2 uvar5_3 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1001111"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct2 bits02 b["01"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let bits07 := write_rs3 bits06 (proj1_sig uvar5_3) in
let result0 := bits07 in
OK (result0)
| fmsubd uvar5_0 uvar5_1 uvar5_2 uvar5_3 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1000111"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct2 bits02 b["01"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let bits07 := write_rs3 bits06 (proj1_sig uvar5_3) in
let result0 := bits07 in
OK (result0)
| fmaddd uvar5_0 uvar5_1 uvar5_2 uvar5_3 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1000011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct2 bits02 b["01"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let bits07 := write_rs3 bits06 (proj1_sig uvar5_3) in
let result0 := bits07 in
OK (result0)
| fsqrtd uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_rs2 bits02 b["00000"] in
let bits04 := write_funct7 bits03 b["0101101"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fled uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_funct7 bits02 b["1010001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fltd uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_funct7 bits02 b["1010001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| feqd uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["010"] in
let bits03 := write_funct7 bits02 b["1010001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fmaxd uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_funct7 bits02 b["0010101"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fmind uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_funct7 bits02 b["0010101"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fdivd uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct7 bits02 b["0001101"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fmuld uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct7 bits02 b["0001001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fsubd uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct7 bits02 b["0000101"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| faddd uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct7 bits02 b["0000001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fsgnjxd uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["010"] in
let bits03 := write_funct7 bits02 b["0010001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fsgnjnd uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_funct7 bits02 b["0010001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fsd uvar5_0 uvar5_1 uvar5_2 uvar7_3 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0100111"] in
let bits02 := write_funct3 bits01 b["011"] in
let bits03 := write_immS1 bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_rs2 bits04 (proj1_sig uvar5_2) in
let bits06 := write_immS2 bits05 (proj1_sig uvar7_3) in
let result0 := bits06 in
OK (result0)
| fload uvar5_0 uvar5_1 uvar12_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0000111"] in
let bits02 := write_funct3 bits01 b["011"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_immI bits04 (proj1_sig uvar12_2) in
let result0 := bits05 in
OK (result0)
| fcvtslu uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_rs2 bits02 b["00011"] in
let bits04 := write_funct7 bits03 b["1101000"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtsl uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_rs2 bits02 b["00010"] in
let bits04 := write_funct7 bits03 b["1101000"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtlus uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_rs2 bits02 b["00011"] in
let bits04 := write_funct7 bits03 b["1100000"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtls uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_rs2 bits02 b["00010"] in
let bits04 := write_funct7 bits03 b["1100000"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtswu uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_rs2 bits02 b["00001"] in
let bits04 := write_funct7 bits03 b["1101000"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtsw uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_rs2 bits02 b["00000"] in
let bits04 := write_funct7 bits03 b["1101000"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtwus uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_rs2 bits02 b["00001"] in
let bits04 := write_funct7 bits03 b["1100000"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtws uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_rs2 bits02 b["00000"] in
let bits04 := write_funct7 bits03 b["1100000"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fnmsubs uvar5_0 uvar5_1 uvar5_2 uvar5_3 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1001011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct2 bits02 b["00"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let bits07 := write_rs3 bits06 (proj1_sig uvar5_3) in
let result0 := bits07 in
OK (result0)
| fnmadds uvar5_0 uvar5_1 uvar5_2 uvar5_3 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1001111"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct2 bits02 b["00"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let bits07 := write_rs3 bits06 (proj1_sig uvar5_3) in
let result0 := bits07 in
OK (result0)
| fmsubs uvar5_0 uvar5_1 uvar5_2 uvar5_3 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1000111"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct2 bits02 b["00"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let bits07 := write_rs3 bits06 (proj1_sig uvar5_3) in
let result0 := bits07 in
OK (result0)
| fmadds uvar5_0 uvar5_1 uvar5_2 uvar5_3 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1000011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct2 bits02 b["00"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let bits07 := write_rs3 bits06 (proj1_sig uvar5_3) in
let result0 := bits07 in
OK (result0)
| fsqrts uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_rs2 bits02 b["00000"] in
let bits04 := write_funct7 bits03 b["0101100"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fles uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_funct7 bits02 b["1010000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| flts uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_funct7 bits02 b["1010000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| feqs uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["010"] in
let bits03 := write_funct7 bits02 b["1010000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fmaxs uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_funct7 bits02 b["0010100"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fmins uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_funct7 bits02 b["0010100"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fdivs uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct7 bits02 b["0001100"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fmuls uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct7 bits02 b["0001000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fsubs uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct7 bits02 b["0000100"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fadds uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct7 bits02 b["0000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fsgnjxs uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["010"] in
let bits03 := write_funct7 bits02 b["0010000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fsgnjns uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_funct7 bits02 b["0010000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fsw uvar5_0 uvar5_1 uvar5_2 uvar7_3 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0100111"] in
let bits02 := write_funct3 bits01 b["010"] in
let bits03 := write_immS1 bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_rs2 bits04 (proj1_sig uvar5_2) in
let bits06 := write_immS2 bits05 (proj1_sig uvar7_3) in
let result0 := bits06 in
OK (result0)
| flw uvar5_0 uvar5_1 uvar12_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0000111"] in
let bits02 := write_funct3 bits01 b["010"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_immI bits04 (proj1_sig uvar12_2) in
let result0 := bits05 in
OK (result0)
| fmvdx uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_rs2 bits02 b["00000"] in
let bits04 := write_funct7 bits03 b["1111001"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fmvxd uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_rs2 bits02 b["00000"] in
let bits04 := write_funct7 bits03 b["1110001"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fmvwx uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_rs2 bits02 b["00000"] in
let bits04 := write_funct7 bits03 b["1111000"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fmvxw uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_rs2 bits02 b["00000"] in
let bits04 := write_funct7 bits03 b["1110000"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fsgnjd uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["100"] in
let bits03 := write_funct7 bits02 b["0010001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| fence uvar5_0 uvar5_1 uvar4_2 uvar4_3 uvar4_4 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0001111"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_succ bits04 (proj1_sig uvar4_2) in
let bits06 := write_pred bits05 (proj1_sig uvar4_3) in
let bits07 := write_fm bits06 (proj1_sig uvar4_4) in
let result0 := bits07 in
OK (result0)
| sd uvar5_0 uvar5_1 uvar5_2 uvar7_3 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0100011"] in
let bits02 := write_funct3 bits01 b["011"] in
let bits03 := write_immS1 bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_rs2 bits04 (proj1_sig uvar5_2) in
let bits06 := write_immS2 bits05 (proj1_sig uvar7_3) in
let result0 := bits06 in
OK (result0)
| sw uvar5_0 uvar5_1 uvar5_2 uvar7_3 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0100011"] in
let bits02 := write_funct3 bits01 b["010"] in
let bits03 := write_immS1 bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_rs2 bits04 (proj1_sig uvar5_2) in
let bits06 := write_immS2 bits05 (proj1_sig uvar7_3) in
let result0 := bits06 in
OK (result0)
| sh uvar5_0 uvar5_1 uvar5_2 uvar7_3 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0100011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_immS1 bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_rs2 bits04 (proj1_sig uvar5_2) in
let bits06 := write_immS2 bits05 (proj1_sig uvar7_3) in
let result0 := bits06 in
OK (result0)
| sb uvar5_0 uvar5_1 uvar5_2 uvar7_3 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0100011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_immS1 bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_rs2 bits04 (proj1_sig uvar5_2) in
let bits06 := write_immS2 bits05 (proj1_sig uvar7_3) in
let result0 := bits06 in
OK (result0)
| ld uvar5_0 uvar5_1 uvar12_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0000011"] in
let bits02 := write_funct3 bits01 b["011"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_immI bits04 (proj1_sig uvar12_2) in
let result0 := bits05 in
OK (result0)
| lw uvar5_0 uvar5_1 uvar12_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0000011"] in
let bits02 := write_funct3 bits01 b["010"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_immI bits04 (proj1_sig uvar12_2) in
let result0 := bits05 in
OK (result0)
| lhu uvar5_0 uvar5_1 uvar12_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0000011"] in
let bits02 := write_funct3 bits01 b["101"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_immI bits04 (proj1_sig uvar12_2) in
let result0 := bits05 in
OK (result0)
| lh uvar5_0 uvar5_1 uvar12_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0000011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_immI bits04 (proj1_sig uvar12_2) in
let result0 := bits05 in
OK (result0)
| lbu uvar5_0 uvar5_1 uvar12_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0000011"] in
let bits02 := write_funct3 bits01 b["100"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_immI bits04 (proj1_sig uvar12_2) in
let result0 := bits05 in
OK (result0)
| lb uvar5_0 uvar5_1 uvar12_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0000011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_immI bits04 (proj1_sig uvar12_2) in
let result0 := bits05 in
OK (result0)
| bgeu uvar1_0 uvar4_1 uvar5_2 uvar5_3 uvar6_4 uvar1_5 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1100011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_immB1 bits02 (proj1_sig uvar1_0) in
let bits04 := write_immB2 bits03 (proj1_sig uvar4_1) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_2) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_3) in
let bits07 := write_immB3 bits06 (proj1_sig uvar6_4) in
let bits08 := write_immB4 bits07 (proj1_sig uvar1_5) in
let result0 := bits08 in
OK (result0)
| bge uvar1_0 uvar4_1 uvar5_2 uvar5_3 uvar6_4 uvar1_5 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1100011"] in
let bits02 := write_funct3 bits01 b["101"] in
let bits03 := write_immB1 bits02 (proj1_sig uvar1_0) in
let bits04 := write_immB2 bits03 (proj1_sig uvar4_1) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_2) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_3) in
let bits07 := write_immB3 bits06 (proj1_sig uvar6_4) in
let bits08 := write_immB4 bits07 (proj1_sig uvar1_5) in
let result0 := bits08 in
OK (result0)
| bltu uvar1_0 uvar4_1 uvar5_2 uvar5_3 uvar6_4 uvar1_5 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1100011"] in
let bits02 := write_funct3 bits01 b["110"] in
let bits03 := write_immB1 bits02 (proj1_sig uvar1_0) in
let bits04 := write_immB2 bits03 (proj1_sig uvar4_1) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_2) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_3) in
let bits07 := write_immB3 bits06 (proj1_sig uvar6_4) in
let bits08 := write_immB4 bits07 (proj1_sig uvar1_5) in
let result0 := bits08 in
OK (result0)
| blt uvar1_0 uvar4_1 uvar5_2 uvar5_3 uvar6_4 uvar1_5 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1100011"] in
let bits02 := write_funct3 bits01 b["100"] in
let bits03 := write_immB1 bits02 (proj1_sig uvar1_0) in
let bits04 := write_immB2 bits03 (proj1_sig uvar4_1) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_2) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_3) in
let bits07 := write_immB3 bits06 (proj1_sig uvar6_4) in
let bits08 := write_immB4 bits07 (proj1_sig uvar1_5) in
let result0 := bits08 in
OK (result0)
| bne uvar1_0 uvar4_1 uvar5_2 uvar5_3 uvar6_4 uvar1_5 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1100011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_immB1 bits02 (proj1_sig uvar1_0) in
let bits04 := write_immB2 bits03 (proj1_sig uvar4_1) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_2) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_3) in
let bits07 := write_immB3 bits06 (proj1_sig uvar6_4) in
let bits08 := write_immB4 bits07 (proj1_sig uvar1_5) in
let result0 := bits08 in
OK (result0)
| beq uvar1_0 uvar4_1 uvar5_2 uvar5_3 uvar6_4 uvar1_5 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1100011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_immB1 bits02 (proj1_sig uvar1_0) in
let bits04 := write_immB2 bits03 (proj1_sig uvar4_1) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_2) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_3) in
let bits07 := write_immB3 bits06 (proj1_sig uvar6_4) in
let bits08 := write_immB4 bits07 (proj1_sig uvar1_5) in
let result0 := bits08 in
OK (result0)
| auipc uvar5_0 uvar20_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0010111"] in
let bits02 := write_rd bits01 (proj1_sig uvar5_0) in
let bits03 := write_immU bits02 (proj1_sig uvar20_1) in
let result0 := bits03 in
OK (result0)
| jalr uvar5_0 uvar5_1 uvar12_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1100111"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_immI bits04 (proj1_sig uvar12_2) in
let result0 := bits05 in
OK (result0)
| jal uvar5_0 uvar8_1 uvar1_2 uvar10_3 uvar1_4 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1101111"] in
let bits02 := write_rd bits01 (proj1_sig uvar5_0) in
let bits03 := write_immJ1 bits02 (proj1_sig uvar8_1) in
let bits04 := write_immJ2 bits03 (proj1_sig uvar1_2) in
let bits05 := write_immJ3 bits04 (proj1_sig uvar10_3) in
let bits06 := write_immJ4 bits05 (proj1_sig uvar1_4) in
let result0 := bits06 in
OK (result0)
| sraw uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0111011"] in
let bits02 := write_funct3 bits01 b["101"] in
let bits03 := write_funct7 bits02 b["0100000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| srlw uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0111011"] in
let bits02 := write_funct3 bits01 b["101"] in
let bits03 := write_funct7 bits02 b["0000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| sllw uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0111011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_funct7 bits02 b["0000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| remuw uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0111011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct7 bits02 b["0000001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| remw uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0111011"] in
let bits02 := write_funct3 bits01 b["110"] in
let bits03 := write_funct7 bits02 b["0000001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| divuw uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0111011"] in
let bits02 := write_funct3 bits01 b["101"] in
let bits03 := write_funct7 bits02 b["0000001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| divw uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0111011"] in
let bits02 := write_funct3 bits01 b["100"] in
let bits03 := write_funct7 bits02 b["0000001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| mulw uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0111011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_funct7 bits02 b["0000001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| subw uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0111011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_funct7 bits02 b["0100000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| addw uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0111011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_funct7 bits02 b["0000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| sraiw uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0011011"] in
let bits02 := write_funct3 bits01 b["101"] in
let bits03 := write_immISp32 bits02 b["0100000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_shamt32 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| srliw uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0011011"] in
let bits02 := write_funct3 bits01 b["101"] in
let bits03 := write_immISp32 bits02 b["0000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_shamt32 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| slliw uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0011011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_immISp32 bits02 b["0000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_shamt32 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| srai uvar5_0 uvar5_1 uvar6_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0010011"] in
let bits02 := write_funct3 bits01 b["101"] in
let bits03 := write_immISp64 bits02 b["00100000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_shamt64 bits05 (proj1_sig uvar6_2) in
let result0 := bits06 in
OK (result0)
| srli uvar5_0 uvar5_1 uvar6_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0010011"] in
let bits02 := write_funct3 bits01 b["101"] in
let bits03 := write_immISp64 bits02 b["00000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_shamt64 bits05 (proj1_sig uvar6_2) in
let result0 := bits06 in
OK (result0)
| slli uvar5_0 uvar5_1 uvar6_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0010011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_immISp64 bits02 b["00000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_shamt64 bits05 (proj1_sig uvar6_2) in
let result0 := bits06 in
OK (result0)
| addiw uvar5_0 uvar5_1 uvar12_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0011011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_immI bits04 (proj1_sig uvar12_2) in
let result0 := bits05 in
OK (result0)
| sra uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["101"] in
let bits03 := write_funct7 bits02 b["0100000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| srl uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["101"] in
let bits03 := write_funct7 bits02 b["0000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| sll uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_funct7 bits02 b["0000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| xor uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["100"] in
let bits03 := write_funct7 bits02 b["0000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| or uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["110"] in
let bits03 := write_funct7 bits02 b["0000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| and uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct7 bits02 b["0000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| sltu uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["011"] in
let bits03 := write_funct7 bits02 b["0000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| slt uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["010"] in
let bits03 := write_funct7 bits02 b["0000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| remu uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_funct7 bits02 b["0000001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| rem uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["110"] in
let bits03 := write_funct7 bits02 b["0000001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| divu uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["101"] in
let bits03 := write_funct7 bits02 b["0000001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| div uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["100"] in
let bits03 := write_funct7 bits02 b["0000001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| mulhu uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["011"] in
let bits03 := write_funct7 bits02 b["0000001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| mulh uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_funct7 bits02 b["0000001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| mul uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_funct7 bits02 b["0000001"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| sub uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_funct7 bits02 b["0100000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| add uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_funct7 bits02 b["0000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_rs2 bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| lui uvar5_0 uvar20_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0110111"] in
let bits02 := write_rd bits01 (proj1_sig uvar5_0) in
let bits03 := write_immU bits02 (proj1_sig uvar20_1) in
let result0 := bits03 in
OK (result0)
| xori uvar5_0 uvar5_1 uvar12_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0010011"] in
let bits02 := write_funct3 bits01 b["100"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_immI bits04 (proj1_sig uvar12_2) in
let result0 := bits05 in
OK (result0)
| ori uvar5_0 uvar5_1 uvar12_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0010011"] in
let bits02 := write_funct3 bits01 b["110"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_immI bits04 (proj1_sig uvar12_2) in
let result0 := bits05 in
OK (result0)
| andi uvar5_0 uvar5_1 uvar12_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0010011"] in
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_immI bits04 (proj1_sig uvar12_2) in
let result0 := bits05 in
OK (result0)
| sltiu uvar5_0 uvar5_1 uvar12_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0010011"] in
let bits02 := write_funct3 bits01 b["011"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_immI bits04 (proj1_sig uvar12_2) in
let result0 := bits05 in
OK (result0)
| slti uvar5_0 uvar5_1 uvar12_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0010011"] in
let bits02 := write_funct3 bits01 b["010"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_immI bits04 (proj1_sig uvar12_2) in
let result0 := bits05 in
OK (result0)
| addi uvar5_0 uvar5_1 uvar12_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0010011"] in
let bits02 := write_funct3 bits01 b["000"] in
let bits03 := write_rd bits02 (proj1_sig uvar5_0) in
let bits04 := write_rs1 bits03 (proj1_sig uvar5_1) in
let bits05 := write_immI bits04 (proj1_sig uvar12_2) in
let result0 := bits05 in
OK (result0)
end.

Program Definition decode_Instruction bin : res (Instruction*nat) :=
	if fcvtsd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtsd (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtds_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtds (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtdlu_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtdlu (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtdl_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtdl (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtlud_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtlud (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtld_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtld (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtdwu_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtdwu (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtdw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtdw (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtwud_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtwud (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtwd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtwd (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fnmsubd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
let uvar5_3 := read_rs3 token0 in
if assertLength uvar5_3 5 then
do code1 <- try_skip_n code0 32;
OK ((fnmsubd (uvar5_0) (uvar5_1) (uvar5_2) (uvar5_3)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fnmaddd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
let uvar5_3 := read_rs3 token0 in
if assertLength uvar5_3 5 then
do code1 <- try_skip_n code0 32;
OK ((fnmaddd (uvar5_0) (uvar5_1) (uvar5_2) (uvar5_3)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fmsubd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
let uvar5_3 := read_rs3 token0 in
if assertLength uvar5_3 5 then
do code1 <- try_skip_n code0 32;
OK ((fmsubd (uvar5_0) (uvar5_1) (uvar5_2) (uvar5_3)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fmaddd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
let uvar5_3 := read_rs3 token0 in
if assertLength uvar5_3 5 then
do code1 <- try_skip_n code0 32;
OK ((fmaddd (uvar5_0) (uvar5_1) (uvar5_2) (uvar5_3)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fsqrtd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fsqrtd (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fled_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fled (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fltd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fltd (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if feqd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((feqd (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fmaxd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fmaxd (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fmind_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fmind (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fdivd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fdivd (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fmuld_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fmuld (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fsubd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fsubd (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if faddd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((faddd (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fsgnjxd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fsgnjxd (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fsgnjnd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fsgnjnd (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fsd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_immS1 token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
let uvar7_3 := read_immS2 token0 in
if assertLength uvar7_3 7 then
do code1 <- try_skip_n code0 32;
OK ((fsd (uvar5_0) (uvar5_1) (uvar5_2) (uvar7_3)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fload_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar12_2 := read_immI token0 in
if assertLength uvar12_2 12 then
do code1 <- try_skip_n code0 32;
OK ((fload (uvar5_0) (uvar5_1) (uvar12_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtslu_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtslu (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtsl_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtsl (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtlus_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtlus (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtls_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtls (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtswu_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtswu (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtsw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtsw (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtwus_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtwus (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fcvtws_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fcvtws (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fnmsubs_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
let uvar5_3 := read_rs3 token0 in
if assertLength uvar5_3 5 then
do code1 <- try_skip_n code0 32;
OK ((fnmsubs (uvar5_0) (uvar5_1) (uvar5_2) (uvar5_3)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fnmadds_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
let uvar5_3 := read_rs3 token0 in
if assertLength uvar5_3 5 then
do code1 <- try_skip_n code0 32;
OK ((fnmadds (uvar5_0) (uvar5_1) (uvar5_2) (uvar5_3)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fmsubs_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
let uvar5_3 := read_rs3 token0 in
if assertLength uvar5_3 5 then
do code1 <- try_skip_n code0 32;
OK ((fmsubs (uvar5_0) (uvar5_1) (uvar5_2) (uvar5_3)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fmadds_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
let uvar5_3 := read_rs3 token0 in
if assertLength uvar5_3 5 then
do code1 <- try_skip_n code0 32;
OK ((fmadds (uvar5_0) (uvar5_1) (uvar5_2) (uvar5_3)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fsqrts_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fsqrts (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fles_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fles (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if flts_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((flts (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if feqs_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((feqs (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fmaxs_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fmaxs (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fmins_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fmins (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fdivs_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fdivs (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fmuls_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fmuls (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fsubs_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fsubs (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fadds_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fadds (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fsgnjxs_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fsgnjxs (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fsgnjns_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fsgnjns (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fsw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_immS1 token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
let uvar7_3 := read_immS2 token0 in
if assertLength uvar7_3 7 then
do code1 <- try_skip_n code0 32;
OK ((fsw (uvar5_0) (uvar5_1) (uvar5_2) (uvar7_3)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if flw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar12_2 := read_immI token0 in
if assertLength uvar12_2 12 then
do code1 <- try_skip_n code0 32;
OK ((flw (uvar5_0) (uvar5_1) (uvar12_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fmvdx_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fmvdx (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fmvxd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fmvxd (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fmvwx_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fmvwx (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fmvxw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
do code1 <- try_skip_n code0 32;
OK ((fmvxw (uvar5_0) (uvar5_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fsgnjd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((fsgnjd (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if fence_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar4_2 := read_succ token0 in
if assertLength uvar4_2 4 then
let uvar4_3 := read_pred token0 in
if assertLength uvar4_3 4 then
let uvar4_4 := read_fm token0 in
if assertLength uvar4_4 4 then
do code1 <- try_skip_n code0 32;
OK ((fence (uvar5_0) (uvar5_1) (uvar4_2) (uvar4_3) (uvar4_4)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if sd_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_immS1 token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
let uvar7_3 := read_immS2 token0 in
if assertLength uvar7_3 7 then
do code1 <- try_skip_n code0 32;
OK ((sd (uvar5_0) (uvar5_1) (uvar5_2) (uvar7_3)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if sw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_immS1 token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
let uvar7_3 := read_immS2 token0 in
if assertLength uvar7_3 7 then
do code1 <- try_skip_n code0 32;
OK ((sw (uvar5_0) (uvar5_1) (uvar5_2) (uvar7_3)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if sh_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_immS1 token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
let uvar7_3 := read_immS2 token0 in
if assertLength uvar7_3 7 then
do code1 <- try_skip_n code0 32;
OK ((sh (uvar5_0) (uvar5_1) (uvar5_2) (uvar7_3)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if sb_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_immS1 token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
let uvar7_3 := read_immS2 token0 in
if assertLength uvar7_3 7 then
do code1 <- try_skip_n code0 32;
OK ((sb (uvar5_0) (uvar5_1) (uvar5_2) (uvar7_3)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if ld_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar12_2 := read_immI token0 in
if assertLength uvar12_2 12 then
do code1 <- try_skip_n code0 32;
OK ((ld (uvar5_0) (uvar5_1) (uvar12_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if lw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar12_2 := read_immI token0 in
if assertLength uvar12_2 12 then
do code1 <- try_skip_n code0 32;
OK ((lw (uvar5_0) (uvar5_1) (uvar12_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if lhu_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar12_2 := read_immI token0 in
if assertLength uvar12_2 12 then
do code1 <- try_skip_n code0 32;
OK ((lhu (uvar5_0) (uvar5_1) (uvar12_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if lh_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar12_2 := read_immI token0 in
if assertLength uvar12_2 12 then
do code1 <- try_skip_n code0 32;
OK ((lh (uvar5_0) (uvar5_1) (uvar12_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if lbu_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar12_2 := read_immI token0 in
if assertLength uvar12_2 12 then
do code1 <- try_skip_n code0 32;
OK ((lbu (uvar5_0) (uvar5_1) (uvar12_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if lb_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar12_2 := read_immI token0 in
if assertLength uvar12_2 12 then
do code1 <- try_skip_n code0 32;
OK ((lb (uvar5_0) (uvar5_1) (uvar12_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if bgeu_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar1_0 := read_immB1 token0 in
if assertLength uvar1_0 1 then
let uvar4_1 := read_immB2 token0 in
if assertLength uvar4_1 4 then
let uvar5_2 := read_rs1 token0 in
if assertLength uvar5_2 5 then
let uvar5_3 := read_rs2 token0 in
if assertLength uvar5_3 5 then
let uvar6_4 := read_immB3 token0 in
if assertLength uvar6_4 6 then
let uvar1_5 := read_immB4 token0 in
if assertLength uvar1_5 1 then
do code1 <- try_skip_n code0 32;
OK ((bgeu (uvar1_0) (uvar4_1) (uvar5_2) (uvar5_3) (uvar6_4) (uvar1_5)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if bge_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar1_0 := read_immB1 token0 in
if assertLength uvar1_0 1 then
let uvar4_1 := read_immB2 token0 in
if assertLength uvar4_1 4 then
let uvar5_2 := read_rs1 token0 in
if assertLength uvar5_2 5 then
let uvar5_3 := read_rs2 token0 in
if assertLength uvar5_3 5 then
let uvar6_4 := read_immB3 token0 in
if assertLength uvar6_4 6 then
let uvar1_5 := read_immB4 token0 in
if assertLength uvar1_5 1 then
do code1 <- try_skip_n code0 32;
OK ((bge (uvar1_0) (uvar4_1) (uvar5_2) (uvar5_3) (uvar6_4) (uvar1_5)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if bltu_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar1_0 := read_immB1 token0 in
if assertLength uvar1_0 1 then
let uvar4_1 := read_immB2 token0 in
if assertLength uvar4_1 4 then
let uvar5_2 := read_rs1 token0 in
if assertLength uvar5_2 5 then
let uvar5_3 := read_rs2 token0 in
if assertLength uvar5_3 5 then
let uvar6_4 := read_immB3 token0 in
if assertLength uvar6_4 6 then
let uvar1_5 := read_immB4 token0 in
if assertLength uvar1_5 1 then
do code1 <- try_skip_n code0 32;
OK ((bltu (uvar1_0) (uvar4_1) (uvar5_2) (uvar5_3) (uvar6_4) (uvar1_5)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if blt_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar1_0 := read_immB1 token0 in
if assertLength uvar1_0 1 then
let uvar4_1 := read_immB2 token0 in
if assertLength uvar4_1 4 then
let uvar5_2 := read_rs1 token0 in
if assertLength uvar5_2 5 then
let uvar5_3 := read_rs2 token0 in
if assertLength uvar5_3 5 then
let uvar6_4 := read_immB3 token0 in
if assertLength uvar6_4 6 then
let uvar1_5 := read_immB4 token0 in
if assertLength uvar1_5 1 then
do code1 <- try_skip_n code0 32;
OK ((blt (uvar1_0) (uvar4_1) (uvar5_2) (uvar5_3) (uvar6_4) (uvar1_5)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if bne_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar1_0 := read_immB1 token0 in
if assertLength uvar1_0 1 then
let uvar4_1 := read_immB2 token0 in
if assertLength uvar4_1 4 then
let uvar5_2 := read_rs1 token0 in
if assertLength uvar5_2 5 then
let uvar5_3 := read_rs2 token0 in
if assertLength uvar5_3 5 then
let uvar6_4 := read_immB3 token0 in
if assertLength uvar6_4 6 then
let uvar1_5 := read_immB4 token0 in
if assertLength uvar1_5 1 then
do code1 <- try_skip_n code0 32;
OK ((bne (uvar1_0) (uvar4_1) (uvar5_2) (uvar5_3) (uvar6_4) (uvar1_5)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if beq_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar1_0 := read_immB1 token0 in
if assertLength uvar1_0 1 then
let uvar4_1 := read_immB2 token0 in
if assertLength uvar4_1 4 then
let uvar5_2 := read_rs1 token0 in
if assertLength uvar5_2 5 then
let uvar5_3 := read_rs2 token0 in
if assertLength uvar5_3 5 then
let uvar6_4 := read_immB3 token0 in
if assertLength uvar6_4 6 then
let uvar1_5 := read_immB4 token0 in
if assertLength uvar1_5 1 then
do code1 <- try_skip_n code0 32;
OK ((beq (uvar1_0) (uvar4_1) (uvar5_2) (uvar5_3) (uvar6_4) (uvar1_5)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if auipc_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar20_1 := read_immU token0 in
if assertLength uvar20_1 20 then
do code1 <- try_skip_n code0 32;
OK ((auipc (uvar5_0) (uvar20_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if jalr_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar12_2 := read_immI token0 in
if assertLength uvar12_2 12 then
do code1 <- try_skip_n code0 32;
OK ((jalr (uvar5_0) (uvar5_1) (uvar12_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if jal_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar8_1 := read_immJ1 token0 in
if assertLength uvar8_1 8 then
let uvar1_2 := read_immJ2 token0 in
if assertLength uvar1_2 1 then
let uvar10_3 := read_immJ3 token0 in
if assertLength uvar10_3 10 then
let uvar1_4 := read_immJ4 token0 in
if assertLength uvar1_4 1 then
do code1 <- try_skip_n code0 32;
OK ((jal (uvar5_0) (uvar8_1) (uvar1_2) (uvar10_3) (uvar1_4)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if sraw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((sraw (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if srlw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((srlw (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if sllw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((sllw (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if remuw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((remuw (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if remw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((remw (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if divuw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((divuw (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if divw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((divw (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if mulw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((mulw (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if subw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((subw (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if addw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((addw (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if sraiw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_shamt32 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((sraiw (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if srliw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_shamt32 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((srliw (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if slliw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_shamt32 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((slliw (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if srai_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar6_2 := read_shamt64 token0 in
if assertLength uvar6_2 6 then
do code1 <- try_skip_n code0 32;
OK ((srai (uvar5_0) (uvar5_1) (uvar6_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if srli_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar6_2 := read_shamt64 token0 in
if assertLength uvar6_2 6 then
do code1 <- try_skip_n code0 32;
OK ((srli (uvar5_0) (uvar5_1) (uvar6_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if slli_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar6_2 := read_shamt64 token0 in
if assertLength uvar6_2 6 then
do code1 <- try_skip_n code0 32;
OK ((slli (uvar5_0) (uvar5_1) (uvar6_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if addiw_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar12_2 := read_immI token0 in
if assertLength uvar12_2 12 then
do code1 <- try_skip_n code0 32;
OK ((addiw (uvar5_0) (uvar5_1) (uvar12_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if sra_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((sra (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if srl_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((srl (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if sll_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((sll (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if xor_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((xor (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if or_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((or (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if and_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((and (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if sltu_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((sltu (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if slt_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((slt (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if remu_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((remu (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if rem_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((rem (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if divu_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((divu (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if div_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((div (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if mulhu_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((mulhu (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if mulh_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((mulh (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if mul_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((mul (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if sub_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((sub (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if add_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_rs2 token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((add (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if lui_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar20_1 := read_immU token0 in
if assertLength uvar20_1 20 then
do code1 <- try_skip_n code0 32;
OK ((lui (uvar5_0) (uvar20_1)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else

	if xori_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar12_2 := read_immI token0 in
if assertLength uvar12_2 12 then
do code1 <- try_skip_n code0 32;
OK ((xori (uvar5_0) (uvar5_1) (uvar12_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if ori_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar12_2 := read_immI token0 in
if assertLength uvar12_2 12 then
do code1 <- try_skip_n code0 32;
OK ((ori (uvar5_0) (uvar5_1) (uvar12_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if andi_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar12_2 := read_immI token0 in
if assertLength uvar12_2 12 then
do code1 <- try_skip_n code0 32;
OK ((andi (uvar5_0) (uvar5_1) (uvar12_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if sltiu_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar12_2 := read_immI token0 in
if assertLength uvar12_2 12 then
do code1 <- try_skip_n code0 32;
OK ((sltiu (uvar5_0) (uvar5_1) (uvar12_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if slti_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar12_2 := read_immI token0 in
if assertLength uvar12_2 12 then
do code1 <- try_skip_n code0 32;
OK ((slti (uvar5_0) (uvar5_1) (uvar12_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	if addi_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar12_2 := read_immI token0 in
if assertLength uvar12_2 12 then
do code1 <- try_skip_n code0 32;
OK ((addi (uvar5_0) (uvar5_1) (uvar12_2)), 4)
else Error(msg"impossible")
else Error(msg"impossible")
else Error(msg"impossible")
else

	Error(msg"Unsupported Instruction").

