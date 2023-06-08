# Towards a Framework for Developing Verified Assemblers for the ELF Format (Supplementary Material)

This material contains the implmentation and applications of the
framework presented in our paper. The framework is a template of
verified assemblers that implements the architecture-independent
components. Its code mainly resides in [assembler](assembler) directory. Beside
that, we utilize CSLED to simplify the implementation and verification
of the instruction encoding, whose code resides in [csled](csled) directory.
As discussed in Section 4 and Section 5 of the paper, we apply our
framework to X86 and RISC-V to generate verified assemblers and
connect them to the backend of Stack-Aware CompCert (based on CompCert
v3.8). These code respectively reside in [x86](x86) and [riscV](riscV) directorys.

## Prerequisites

We assume that your machine is based on X86. To compile CompCert v3.8
and our framework (including CSLED), the following software components
are required:
* Ocaml 4.09.0
* Coq 8.12.1
* Bison 3.6 (required by CSLED)
* Flex 2.6.4 (required by CSLED)
* riscv-gnu-toolchain (required by RISC-V)
* qemu-7.0.0 (required by RISC-V)

### Install Ocaml and Coq

We recommend using the `opam` package manager to set up a build
environment with the following commands:

    # Initialize opam (if you haven't used it before)
    opam init --bare

    # Create an "opam switch" dedicated to building the framework
    opam switch create aplas23-assembler ocaml-base-compiler.4.09.0

    # Install the Coq and parser
    opam install coq.8.12.1 menhir.20211012

    # Update the environment
    eval $(opam env)
    
### Install Bison and Flex

    # Install flex
    sudo apt install flex

    # Install Bison v3.6 from source
    cd ~ && wget https://ftp.gnu.org/gnu/bison/bison-3.6.1.tar.xz
    tar -xf bison-3.6.1.tar.xz
    cd bison-3.6
    ./configure && make -j$(nproc)
    sudo make install

### Install GNU RISC-V Toolchain and Qemu (Optional)

If you want to build RISC-V assemblers and evaluate it on RISC-V test
cases, you need to install riscv-gnu-toolchain to generate executable
ELF files from the output of the assembler and qemu to simulate the
execution of these files on your machine.

    # Install 64-bit riscv-gnu-toolchain
    sudo apt install gcc-riscv64-linux-gnu
    riscv64-linux-gnu-gcc -v

    # Install 32-bit riscv-gnu-toolchain (required if you want to build 32-bit RISC-V assemblers)
    # Download built package from https://github.com/riscv-collab/riscv-gnu-toolchain/releases (roughly 600MB)
    cd ~ & wget https://github.com/riscv-collab/riscv-gnu-toolchain/releases/download/2022.09.30/riscv32-glibc-ubuntu-20.04-nightly-2022.09.30-nightly.tar.gz -O riscv32-gnu-toolchain.tar.gz
    tar -xf riscv32-gnu-toolchain.tar.gz
    ~/riscv32-gnu-toolchain/bin/riscv32-unknown-linux-gnu-gcc -v

    # Install Qemu
    cd ~ && wget https://download.qemu.org/qemu-7.0.0.tar.xz
    tar xf qemu-7.0.0.tar.xz
    cd qemu-7.0.0

    # Build Qemu that simulates 64-bit RISC-V
    ./configure --target-list=riscv64-softmmu,riscv64-linux-user
    make -j$(nproc)
    sudo make install
    qemu-riscv64 --version

    # Build Qemu that simulates 32-bit RISC-V
    ./configure --target-list=riscv32-softmmu,riscv32-linux-user
    make -j$(nproc)
    sudo make install
    qemu-riscv32 --version

## Build CompCert and The framework

### Target X86-64

    # Configure to X86-64
    ./configure x86_64-linux
    # Build CSLED and generate encoder, decoder and their proofs
    make csled
    make -j$(nproc) all

### Target X86-32

    ./configure x86_32-linux
    make csled
    make -j$(nproc) all

### Target RV32

    # Toolprefix is the prefix of the name of the external C compiler
    # Simulator is set to qemu simulator
    # 'simu-ld' denotes the path to the linker, which is provided by riscv-gnu-toolchain
    ./configure rv32-linux -toolprefix ~/riscv-gnu-toolchain/riscv32-unknown-linux-gnu- -simulator qemu-riscv32 -simu-ld ~/riscv-gnu-toolchain/sysroot
    make csled
    make -j$(nproc) all

### Target RV64
    # As we use apt to install 64-bit riscv-gnu-toolchain, their paths are in the environment
    ./configure rv64-linux -toolprefix riscv64-linux-gnu- -simulator qemu-riscv64 -simu-ld /usr/riscv64-linux-gnu/
    make csled
    make -j$(nproc) all

## Structure

We show the structure following Table 1 in our paper.

| Components            | Framework       | Application of X86 |Application of RISCV       |
|----------------------|-----------------|---------------------|-------------------------|
| $P_{\mathcal{A}}$: Realistic Assembly   | [assembler/RealAsm.v](assembler/RealAsm.v) | [x86/RealAsmArchi.v](x86/RealAsmArchi.v)<br>[x86/Asm.v](x86/Asm.v)  | [riscV/RealAsmArchi.v](riscV/RealAsmArchi.v)<br>[riscV/Asm.v](riscV/Asm.v)|
| $P_{\mathcal{R}}$: Relocatable Programs | [assembler/RelocProg.v](assembler/RelocProg.v)<br>[assembler/RelocProgSemantics.v](assembler/RelocProgSemantics.v)($[\![P_1]\!]$)<br>[assembler/RelocProgSemantics1.v](assembler/RelocProgSemantics1.v)($[\![P_2]\!]$)<br>[assembler/RelocProgSemantics2.v](assembler/RelocProgSemantics2.v)($[\![P_3]\!]$) | [x86/RelocProgSemanticsArchi.v](x86/RelocProgSemanticsArchi.v)<br>[x86/RelocProgSemanticsArchi1.v](x86/RelocProgSemanticsArchi1.v)<br>[x86/RelocBinDecode.v](x86/RelocBinDecode.v) | [riscV/RelocProgSemanticsArchi.v](riscV/RelocProgSemanticsArchi.v)<br>[riscV/RelocProgSemanticsArchi1.v](riscV/RelocProgSemanticsArchi1.v)<br>[riscV/RelocBinDecode.v](riscV/RelocBinDecode.v) | 
| $P_{\mathcal{E}}$: Relocatable ELF | [elf/RelocElf.v](elf/RelocElf.v)<br>[elf/RelocElfSemantics.v](elf/RelocElfSemantics.v)($[\![P_4]\!]$) | [x86/RelocElfArchi.v](x86/RelocElfArchi.v) | [riscV/RelocElfArchi.v](x86/RelocElfArchi.v) |
$\mathbb{C}_1$: Generation of Relocatable Programs | [assembler/Symbtablegen.v](assembler/Symbtablegen.v)<br>[assembler/Symbtablegenproof.v](assembler/Symbtablegenproof.v) | [x86/SymbtablegenproofArchi.v](x86/SymbtablegenproofArchi.v) | [riscV/SymbtablegenproofArchi.v](riscV/SymbtablegenproofArchi.v) |
$\mathbb{C}_2$: Generation of Relocation Table | [assembler/Reloctablesgen.v](assembler/Reloctablesgen.v)<br>[assembler/Reloctablesgenproof.v](assembler/Reloctablesgenproof.v) | [x86/ReloctablesgenArchi.v](x86/ReloctablesgenArchi.v)<br>[x86/ReloctablesgenproofArchi.v](x86/ReloctablesgenproofArchi.v) | [riscV/ReloctablesgenArchi.v](x86/ReloctablesgenArchi.v)<br>[riscV/ReloctablesgenproofArchi.v](x86/ReloctablesgenproofArchi.v) |
$\mathbb{C}_3$: Instruction and Data Encoding | [assembler/RelocBingen.v](assembler/RelocBingen.v)<br>[assembler/RelocBingenproof.v](assembler/RelocBingenproof.v) | Translator: [x86/TranslateInstr.v](x86/TranslateInstr.v)<br>CSLED Spec: [x86.csled](csled/x86/x86.csled)| Translator: [riscV/TranslateInstr.v](riscV/TranslateInstr.v)<br>CSLED Spec: [riscv.csled](csled/riscv/riscv.csled) |
$\mathbb{C}_4$: Generation of Relocatable ELF | [elf/RelocElfgen.v](elf/RelocElfgen.v)<br>[elf/RelocElfgenproof.v](elf/RelocElfgenproof.v) | [x86/RelocElfgenproofArchi.v](x86/RelocElfgenproofArchi.v) | [riscV/RelocElfgenproofArchi.v](riscV/RelocElfgenproofArchi.v) |

By the way, the top-level definitions of the target printers are defined
in [x86/CompilerAux.v](x86/CompilerAux.v) and [riscV/CompilerAux.v](riscV/CompilerAux.v).

### Interfaces

We summarize the interfaces provided by our framework in Section 3.2
of the paper. For simpliciy, we do not choose to use `Variable` and
`Hypothesis` to declare the interfaces. Instead, in our
implementation, we directly instantiate these interfaces by importing
the modules containing their implementation.

For example, `translate_instr` is the interface for translating the
instructions to CSLED specifications. Its implmentation is in
[x86/TranslateInstr.v](x86/TranslateInstr.v) and
[riscV/TranslateInstr.v](riscV/TranslateInstr.v). It is invoked in
[assembler/translate_instr](assembler/translate_instr) by importing
the `TranslateInstr.v` module. It works because both implementation in
x86 and riscV has the same name.

In the following table, we show the interfaces, the names and the
locations of their implementation.

| Interfaces | Names in Coq | X86 instantiation | RISC-V instantiation
|--------|----|---------|-----------|
$gen\_reloc$ | transl_instr<br>id_eliminate | [x86/ReloctablesgenArchi.v](x86/ReloctablesgenArchi.v) | [riscV/ReloctablesgenArchi.v](riscV/ReloctablesgenArchi.v) |
$translate\_instr$ | translate_instr | [x86/TranslateInstr](x86/TranslateInstr.v) | [riscV/TranslateInstr](riscV/TranslateInstr.v) |
$csled\_encode$ | encode_Instruction | [autogen/EncDecRet.v](autogen/EncDecRet.v) | [autogen/EncDecRet.v](autogen/EncDecRet.v) |
$restore\_symb$ | rev_id_eliminate | [x86/RelocProgSemanticsArchi1.v](x86/RelocProgSemanticsArchi1.v) | [riscV/RelocProgSemanticsArchi1.v](riscV/RelocProgSemanticsArchi1.v) |
$revert\_translate$ | decode_instr | [x86/RelocBinDecode.v](x86/RelocBinDecode.v) | [riscV/RelocBinDecode.v](riscV/RelocBinDecode.v) |
$csled\_decode$ | decode_Instruction | [autogen/EncDecRet.v](autogen/EncDecRet.v) | [autogen/EncDecRet.v](autogen/EncDecRet.v) |
$step_{\mathcal{A}}$ | step | [x86/RealAsmArchi.v](x86/RealAsmArchi.v) | [riscV/RealAsmArchi.v](riscV/RealAsmArchi.v) |
$step_{\mathcal{R}}$ | step | [x86/RelocProgSemanticsArchi.v](x86/RelocProgSemanticsArchi.v) | [riscV/RelocProgSemanticsArchi.v](riscV/RelocProgSemanticsArchi.v) |
$restore\_symb\_correct$ | transl_instr_consistency | [x86/ReloctablesgenproofArchi.v](x86/ReloctablesgenproofArchi.v) | [riscV/ReloctablesgenproofArchi.v](riscV/ReloctablesgenproofArchi.v) |
$translate\_intsr\_correct$ | translate_instr_consistency | [x86/RelocBinDecode.v](x86/RelocBinDecode.v) | [riscV/RelocBinDecode.v](riscV/RelocBinDecode.v) |
$csled\_encode\_correct$ | encode_Instruction_consistency | [autogen/EncConsistency.v](autogen/EncConsistency.v) | [autogen/EncConsistency.v](autogen/EncConsistency.v) |
$step\_simulation_{{\mathcal{A}},{\mathcal{R}}}$ | step_simulation | [x86/SymbtablegenproofArchi.v](x86/SymbtablegenproofArchi.v) | [riscV/SymbtablegenproofArchi.v](riscV/SymbtablegenproofArchi.v) |
$step\_simulation_{{\mathcal{R}},{\mathcal{R}}}$ | step_simulation | [assembler/Reloctablesgenproof.v](assembler/Reloctablesgenproof.v)<br>[x86/RelocBingenproofArchi.v](x86/RelocBingenproofArchi.v)<br>[x86/RelocElfgenproofArchi.v](x86/RelocElfgenproofArchi.v) | [assembler/Reloctablesgenproof.v](assembler/Reloctablesgenproof.v)<br>[riscV/RelocBingenproofArchi.v](riscV/RelocBingenproofArchi.v)<br>[riscV/RelocElfgenproofArchi.v](riscV/RelocElfgenproofArchi.v)

## Evaluation

### Run The Test Cases

As described in Section 5 of the paper, we evaluate the generated
assemblers with the test cases provided by CompCert. They reside in
[test](test) folder.

If you configure the assembler to X86-32/64, you can simply run the
following code to evaluate the test：

    cd test
    # Compile the test cases
    make all
    # Start the test
    make test

If you configure to RV-32/64, you need to ensure that the RISC-V GNU
Toolchain and Qemu have been installed and configured in your machine.
The installation and configuration are introduced above. If they are
all done, you can type the same commands to run the test.

    cd test
    # Compile the test cases
    make all
    # Start the test
    make test

### Performance Evaluation

