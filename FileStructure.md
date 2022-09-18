
**Program Definitions**
* `assembler/RelocProg.v`: the definition of relocatable programs `reloc_prog` in Sec.3 of our paper.
* `assembler/RelocProgram.v`: an instantiation of `reloc_prog` as the result of generation of relocation programs, i.e., `reloc_prog instruction init_data`.
* `assembler/RelocProgramBytes.v`: an instantiation of `reloc_prog` as the result of instruction and data encoding, i.e., `reloc_prog byte byte`.
* `elf/RelocElf.v`: the definition of elf object files `elf_file`.

**Program Semantics**
* `assembler/RelocProgGlobalenvs.v`: the redefined global environment `genv` introduced in Sec.3.
* `assembler/RelocProgSemantics.v`, `x86/RelocProgSemanticsArchi.v`: the semantics of `reloc_prog` which is divided into architecture-independent and -dependent parts.
* `assembler/RelocProgSemantics1.v`, `x86/RelocProgSemanticsArchi1.v`: the semantics of `reloc_prog` after generation of relocation tables introduced in Sec.5.
* `assembler/RelocProgSemantics2.v`, `x86/RelocProgSemanticsArchi2.v`: the semantics of `reloc_prog` after instruction and data encoding introduced in Sec.6.3
* `elf/RelocElfSemantics.v`: the semantics of `elf_file`.

**Generation of Relocatable Programs (Sec.4)**
* `assembler/Symbtablegen.v`: generation of symbol tables and sections.
* `assembler/Symbtablegenproof.v`: verification of this pass.

**Generation of Relocation Tables (Sec.5)**
* `x86/ReloctablesgenArchi.v`: provides the functions of generating a relocation entry from an instruction and eliminating the symbol in an instruction.
* `assembler/Reloctablesgen.v`: generation of relocation tables and elimination of symbols with the functions provided by `x86/ReloctablesgenArchi.v`.
* `assembler/Reloctablesgenproof.v`, `x86/ReloctablesgenproofArchi.v`: verification of this pass.

**Instruction and Data Encoding (Sec.6)**
* `autogen/EncDecRet.v`: the generated encoders and decoders from CSLED.
* `?`: consistency theorem for generated encoders and decoders.
* `x86/TranslateInstr.v`: translates CompCert instructions to CSLED instructions.
* `assembler/RelocBingen.v`: encoding of instructions and data into bytes with the functions provided by `autogen/EncDecRet.v` and `x86/TranslateInstr.v`.
* `assembler/RelocBingenproof.v`, `x86/RelocBingenproofArchi.v`: verification of this pass.

**Generation of Relocatable ELF (Sec.7)**
* `elf/RelocElfgen.v`: generation of `elf_file` from `reloc_prog byte byte`.
* `elf/RelocElfgenproof.v`: verification of this pass.
