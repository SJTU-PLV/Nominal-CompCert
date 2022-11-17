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

Definition write_immISp (Instr:bits)  (immISp_value:bits) : bits :=
	immISp_value++(Instr>@[7]).

Definition read_immISp (Instr:bits) : bits :=
	Instr~@[7].

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

Definition write_shamt (Instr:bits)  (shamt_value:bits) : bits :=
	(Instr~@[7])++shamt_value++(Instr>@[12]).

Definition read_shamt (Instr:bits) : bits :=
	(Instr>@[7])~@[5].

Definition write_succ (Instr:bits)  (succ_value:bits) : bits :=
	(Instr~@[8])++succ_value++(Instr>@[12]).

Definition read_succ (Instr:bits) : bits :=
	(Instr>@[8])~@[4].


Hint Unfold read_fm write_fm read_funct2 write_funct2 read_funct3 write_funct3 read_funct7 write_funct7 read_immB1 write_immB1 read_immB2 write_immB2 read_immB3 write_immB3 read_immB4 write_immB4 read_immI write_immI read_immISp write_immISp read_immJ1 write_immJ1 read_immJ2 write_immJ2 read_immJ3 write_immJ3 read_immJ4 write_immJ4 read_immS1 write_immS1 read_immS2 write_immS2 read_immU write_immU read_opcode write_opcode read_pred write_pred read_rd write_rd read_rm write_rm read_rs1 write_rs1 read_rs2 write_rs2 read_rs3 write_rs3 read_shamt write_shamt read_succ write_succ:bitfields.

Hint Unfold fcvtswu_bp fcvtsw_bp fcvtwus_bp fcvtws_bp fnmsubs_bp fnmadds_bp fmsubs_bp fmadds_bp fsqrts_bp fles_bp flts_bp feqs_bp fmaxs_bp fmins_bp fdivs_bp fmuls_bp fsubs_bp fadds_bp fsgnjxs_bp fsgnjns_bp fsw_bp flw_bp fmvwx_bp fmvxw_bp fsgnjd_bp fence_bp sw_bp sh_bp sb_bp lw_bp lhu_bp lh_bp lbu_bp lb_bp bgeu_bp bge_bp bltu_bp blt_bp bne_bp beq_bp auipc_bp jalr_bp jal_bp sra_bp srl_bp sll_bp xor_bp or_bp and_bp sltu_bp slt_bp remu_bp rem_bp divu_bp div_bp mulhu_bp mulh_bp mul_bp sub_bp add_bp lui_bp srai_bp srli_bp slli_bp xori_bp ori_bp andi_bp sltiu_bp slti_bp addi_bp :Instruction_bpdb.
Lemma Instruction_bp_in_list0: 
In fcvtswu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list1: 
In fcvtsw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list2: 
In fcvtwus_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list3: 
In fcvtws_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list4: 
In fnmsubs_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list5: 
In fnmadds_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list6: 
In fmsubs_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list7: 
In fmadds_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list8: 
In fsqrts_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list9: 
In fles_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list10: 
In flts_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list11: 
In feqs_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list12: 
In fmaxs_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list13: 
In fmins_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list14: 
In fdivs_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list15: 
In fmuls_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list16: 
In fsubs_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list17: 
In fadds_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list18: 
In fsgnjxs_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list19: 
In fsgnjns_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list20: 
In fsw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list21: 
In flw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list22: 
In fmvwx_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list23: 
In fmvxw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list24: 
In fsgnjd_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list25: 
In fence_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list26: 
In sw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list27: 
In sh_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list28: 
In sb_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list29: 
In lw_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list30: 
In lhu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list31: 
In lh_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list32: 
In lbu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list33: 
In lb_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list34: 
In bgeu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list35: 
In bge_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list36: 
In bltu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list37: 
In blt_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list38: 
In bne_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list39: 
In beq_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list40: 
In auipc_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list41: 
In jalr_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list42: 
In jal_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list43: 
In sra_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list44: 
In srl_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list45: 
In sll_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list46: 
In xor_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list47: 
In or_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list48: 
In and_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list49: 
In sltu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list50: 
In slt_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list51: 
In remu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list52: 
In rem_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list53: 
In divu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list54: 
In div_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list55: 
In mulhu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list56: 
In mulh_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list57: 
In mul_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list58: 
In sub_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list59: 
In add_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list60: 
In lui_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list61: 
In srai_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list62: 
In srli_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list63: 
In slli_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list64: 
In xori_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list65: 
In ori_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list66: 
In andi_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list67: 
In sltiu_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list68: 
In slti_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Lemma Instruction_bp_in_list69: 
In addi_bp Instruction_bp_list.
Proof.
simpl; goOver; auto. Qed.

Inductive Instruction: Type :=
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
| fmvwx(uvar5_0:u5)(uvar5_1:u5)
| fmvxw(uvar5_0:u5)(uvar5_1:u5)
| fsgnjd(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| fence(uvar5_0:u5)(uvar5_1:u5)(uvar4_2:u4)(uvar4_3:u4)(uvar4_4:u4)
| sw(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar7_3:u7)
| sh(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar7_3:u7)
| sb(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)(uvar7_3:u7)
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
| srai(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| srli(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| slli(uvar5_0:u5)(uvar5_1:u5)(uvar5_2:u5)
| xori(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| ori(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| andi(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| sltiu(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| slti(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12)
| addi(uvar5_0:u5)(uvar5_1:u5)(uvar12_2:u12).
Inductive Instruction_op: Type :=
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
| fmvwx_op
| fmvxw_op
| fsgnjd_op
| fence_op
| sw_op
| sh_op
| sb_op
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
| srai_op
| srli_op
| slli_op
| xori_op
| ori_op
| andi_op
| sltiu_op
| slti_op
| addi_op.
Definition Instruction_to_op element  :=
	match element with
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
| fmvwx _ _ => fmvwx_op
| fmvxw _ _ => fmvxw_op
| fsgnjd _ _ _ => fsgnjd_op
| fence _ _ _ _ _ => fence_op
| sw _ _ _ _ => sw_op
| sh _ _ _ _ => sh_op
| sb _ _ _ _ => sb_op
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
| srai _ _ _ => srai_op
| srli _ _ _ => srli_op
| slli _ _ _ => slli_op
| xori _ _ _ => xori_op
| ori _ _ _ => ori_op
| andi _ _ _ => andi_op
| sltiu _ _ _ => sltiu_op
| slti _ _ _ => slti_op
| addi _ _ _ => addi_op
end.
Definition Instruction_op_to_bp element  :=
	match element with
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
| fmvwx_op => fmvwx_bp
| fmvxw_op => fmvxw_bp
| fsgnjd_op => fsgnjd_bp
| fence_op => fence_bp
| sw_op => sw_bp
| sh_op => sh_bp
| sb_op => sb_bp
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
| srai_op => srai_bp
| srli_op => srli_bp
| slli_op => slli_bp
| xori_op => xori_bp
| ori_op => ori_bp
| andi_op => andi_bp
| sltiu_op => sltiu_bp
| slti_op => slti_bp
| addi_op => addi_bp
end.
Definition encode_Instruction element  :=
	match element with
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
let bits02 := write_funct3 bits01 b["111"] in
let bits03 := write_rs2 bits02 b["00001"] in
let bits04 := write_funct7 bits03 b["1100000"] in
let bits05 := write_rd bits04 (proj1_sig uvar5_0) in
let bits06 := write_rs1 bits05 (proj1_sig uvar5_1) in
let result0 := bits06 in
OK (result0)
| fcvtws uvar5_0 uvar5_1 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["1010011"] in
let bits02 := write_funct3 bits01 b["111"] in
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
| srai uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0010011"] in
let bits02 := write_funct3 bits01 b["101"] in
let bits03 := write_immISp bits02 b["0100000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_shamt bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| srli uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0010011"] in
let bits02 := write_funct3 bits01 b["101"] in
let bits03 := write_immISp bits02 b["0000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_shamt bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
OK (result0)
| slli uvar5_0 uvar5_1 uvar5_2 => let bits00 := (repeat false 32) in
let bits01 := write_opcode bits00 b["0010011"] in
let bits02 := write_funct3 bits01 b["001"] in
let bits03 := write_immISp bits02 b["0000000"] in
let bits04 := write_rd bits03 (proj1_sig uvar5_0) in
let bits05 := write_rs1 bits04 (proj1_sig uvar5_1) in
let bits06 := write_shamt bits05 (proj1_sig uvar5_2) in
let result0 := bits06 in
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

	if srai_bp bin then
let code0 := bin in
do token0 <- try_first_n code0 32;
let uvar5_0 := read_rd token0 in
if assertLength uvar5_0 5 then
let uvar5_1 := read_rs1 token0 in
if assertLength uvar5_1 5 then
let uvar5_2 := read_shamt token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((srai (uvar5_0) (uvar5_1) (uvar5_2)), 4)
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
let uvar5_2 := read_shamt token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((srli (uvar5_0) (uvar5_1) (uvar5_2)), 4)
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
let uvar5_2 := read_shamt token0 in
if assertLength uvar5_2 5 then
do code1 <- try_skip_n code0 32;
OK ((slli (uvar5_0) (uvar5_1) (uvar5_2)), 4)
else Error(msg"impossible")
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

