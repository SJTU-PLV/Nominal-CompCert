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

> The following guide of installation assumes that the architecture of
your machine is X86-64. 

To compile CompCert v3.8 and our framework
(including CSLED), the following software components are required:
* GCC
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
execution of these files on your machine. Since `apt` does not provide
the toolchain of rv32, we need to download its built package from the
github.

    # Install 64-bit riscv-gnu-toolchain
    sudo apt install gcc-riscv64-linux-gnu
    riscv64-linux-gnu-gcc -v

    # Install 32-bit riscv-gnu-toolchain (required if you want to build 32-bit RISC-V assemblers)
    # Download built package (roughly 600MB)
    cd ~ & wget https://github.com/riscv-collab/riscv-gnu-toolchain/releases/download/2022.09.30/riscv32-glibc-ubuntu-20.04-nightly-2022.09.30-nightly.tar.gz -O riscv32-gnu-toolchain.tar.gz
    tar -xf riscv32-gnu-toolchain.tar.gz
    ~/riscv32-gnu-toolchain/bin/riscv32-unknown-linux-gnu-gcc -v

    # Install Qemu
    cd ~ && wget https://download.qemu.org/qemu-7.0.0.tar.xz
    tar -xf qemu-7.0.0.tar.xz
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

**Note**: It is time consuming to build the whole compiler due to the
  huge amount of proofs generated by CSLED. CSLED generates $O(n^2)$
  lemmas to verifiy the consistency between encoders and decoders
  where $n$ is the number of instructions. So it is impractical for
  the readers to run the proofs. We provide three options (O0, O1 and
  O2) to speed up the proofs by replacing the enormous proof scripts
  with `Admitted` so that it can save lots of time. Note that we have
  already checked the complete proofs in our machines. We also
  evaluate the consumption of time which is listed below.

| Options | Time Consumption |
|---------|:----------------:|
| O0      | ~1h30min         |
| O1      | ~40min           |
| O2      | ~5min            |

In the following configuration, we all set `-csled-opt` to `O2` to
reduce the consumption of time. The generated proofs are in
[autogen/EncConsistency.v](autogen/EncConsistency.v) and you can check
them after `make csled`.

### X86-64

    # Configure to X86-64
    ./configure x86_64-linux -csled-opt O2
    # Use CSLED to generate encoder, decoder and their proofs
    make csled
    make -j$(nproc) all

### X86-32

    ./configure x86_32-linux -csled-opt O2
    make csled
    make -j$(nproc) all

### RISC-V 32

    # Toolprefix is the prefix of the name of the external C compiler
    # Simulator is set to qemu simulator
    # 'simu-ld' denotes the path to the dynamic loader, which is provided by riscv-gnu-toolchain
    ./configure rv32-linux -toolprefix ~/riscv-gnu-toolchain/riscv32-unknown-linux-gnu- -simulator qemu-riscv32 -simu-ld ~/riscv-gnu-toolchain/sysroot -csled-opt O2
    make csled
    make -j$(nproc) all

### RISC-V RV64
    # As we use apt to install 64-bit riscv-gnu-toolchain, their paths are already in the environment
    ./configure rv64-linux -toolprefix riscv64-linux-gnu- -simulator qemu-riscv64 -simu-ld /usr/riscv64-linux-gnu/ -csled-opt O2
    make csled
    make -j$(nproc) all

## Structure

We show the structure following Table 1 in our paper.

| Components            | Framework       | Application of X86 |Application of RISCV       |
|----------------------|-----------------|---------------------|-------------------------|
| $P_{\mathcal{A}}$: Realistic Assembly   | [assembler/RealAsm.v](assembler/RealAsm.v) | [x86/RealAsmArchi.v](x86/RealAsmArchi.v)<br>[x86/Asm.v](x86/Asm.v)  | [riscV/RealAsmArchi.v](riscV/RealAsmArchi.v)<br>[riscV/Asm.v](riscV/Asm.v)|
| $P_{\mathcal{R}}$: Relocatable Programs | [assembler/RelocProg.v](assembler/RelocProg.v)<br>[assembler/RelocProgSemantics.v](assembler/RelocProgSemantics.v)($[\![P_1]\!]$)<br>[assembler/RelocProgSemantics1.v](assembler/RelocProgSemantics1.v)($[\![P_2]\!]$)<br>[assembler/RelocProgSemantics2.v](assembler/RelocProgSemantics2.v)($[\![P_3]\!]$) | [x86/RelocProgSemanticsArchi.v](x86/RelocProgSemanticsArchi.v)<br>[x86/RelocProgSemanticsArchi1.v](x86/RelocProgSemanticsArchi1.v) | [riscV/RelocProgSemanticsArchi.v](riscV/RelocProgSemanticsArchi.v)<br>[riscV/RelocProgSemanticsArchi1.v](riscV/RelocProgSemanticsArchi1.v) | 
| $P_{\mathcal{E}}$: Relocatable ELF | [elf/RelocElf.v](elf/RelocElf.v)<br>[elf/RelocElfSemantics.v](elf/RelocElfSemantics.v)($[\![P_4]\!]$) | [x86/RelocElfArchi.v](x86/RelocElfArchi.v) | [riscV/RelocElfArchi.v](x86/RelocElfArchi.v) |
$\mathbb{C}_1$: Generation of Relocatable Programs | [assembler/Symbtablegen.v](assembler/Symbtablegen.v)<br>[assembler/Symbtablegenproof.v](assembler/Symbtablegenproof.v) | [x86/SymbtablegenproofArchi.v](x86/SymbtablegenproofArchi.v) | [riscV/SymbtablegenproofArchi.v](riscV/SymbtablegenproofArchi.v) |
$\mathbb{C}_2$: Generation of Relocation Table | [assembler/Reloctablesgen.v](assembler/Reloctablesgen.v)<br>[assembler/Reloctablesgenproof.v](assembler/Reloctablesgenproof.v) | [x86/ReloctablesgenArchi.v](x86/ReloctablesgenArchi.v)<br>[x86/ReloctablesgenproofArchi.v](x86/ReloctablesgenproofArchi.v) | [riscV/ReloctablesgenArchi.v](x86/ReloctablesgenArchi.v)<br>[riscV/ReloctablesgenproofArchi.v](x86/ReloctablesgenproofArchi.v) |
$\mathbb{C}_3$: Instruction and Data Encoding | [assembler/RelocBingen.v](assembler/RelocBingen.v)<br>[assembler/RelocBingenproof.v](assembler/RelocBingenproof.v) | Translators: [x86/TranslateInstr.v](x86/TranslateInstr.v)<br>[x86/RelocBinDecode.v](x86/RelocBinDecode.v)<br>CSLED Spec: [x86.csled](csled/x86/x86.csled) | Translators: [riscV/TranslateInstr.v](riscV/TranslateInstr.v)<br>[riscV/RelocBinDecode.v](riscV/RelocBinDecode.v)<br>CSLED Spec: [riscv.csled](csled/riscv/riscv.csled) |
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

Before you run the code on your machine, make sure that `gcc` has been installed. Beside that, we need to install `gcc-muitilib` to get the standard library for X86-32.

    sudo apt install gcc-multilib

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

We evaluate the performance of the generated code with the scripts
provided by CompCert in [test/c/Makefile](test/c/Makefile). This code
is compiled by CompCert and assembled by our assemblers or by the GNU
assembler (GAS). The scripts measure the time by running the code
multiple times. and calculating their average value. 

    # Evaluate the code generated by our assemblers
    cd test/c
    make all
    make bench

    # Evaluate the code generated by GCC
    cd test/c
    make all_gcc
    make bench_gcc

 We run the above scripts in WSL2 Ubuntu20.04 on a machine with
 Intel(R) Core(TM) i9-12900H CPU. The result of the evaluation is
 shown in the following tables.

 | Test cases | Our work in X86-32  | GCC in in X86-32 | Our work in X86-64  | GCC in in X86-64 |
|--|:--:|:--:|:--:|:--:|
| fib            | 0.044 | 0.044 | 0.042 | 0.033 |
| integr         | 0.022 | 0.065 | 0.023 | 0.023 |
| qsort          | 0.071 | 0.075 | 0.069 | 0.062 |
| fft            | 0.057 | 0.060 | 0.053 | 0.050 |
| fftsp          | 0.030 | 0.031 | 0.020 | 0.013 |
| fftw           | 0.035 | 0.053 | 0.081 | 0.023 |
| sha1           | 0.037 | 0.027 | 0.030 | 0.025 |
| sha3           | 0.039 | 0.032 | 0.020 | 0.012 |
| aes            | 0.044 | 0.039 | 0.045 | 0.037 |
| almabench      | 0.250 | 0.228 | 0.123 | 0.110 |
| lists          | 0.047 | 0.046 | 0.046 | 0.046 |
| binarytrees    | 0.018 | 0.018 | 0.015 | 0.016 |
| fannkuch       | 0.143 | 0.129 | 0.133 | 0.121 |
| knucleotide    | 0.061 | 0.077 | 0.072 | 0.071 |
| mandelbrot     | 0.086 | 0.073 | 0.086 | 0.051 |
| nbody          | 0.078 | 0.091 | 0.055 | 0.045 |
| nsieve         | 0.070 | 0.067 | 0.064 | 0.062 |
| nsievebits     | 0.065 | 0.056 | 0.060 | 0.054 |
| spectral       | 0.072 | 0.093 | 0.072 | 0.072 |
| vmach          | 0.038 | 0.025 | 0.040 | 0.027 |
| bisect         | 0.050 | 0.058 | 0.049 | 0.052 |
| chomp          | 0.095 | 0.097 | 0.101 | 0.100 |
| perlin         | 0.410 | 0.157 | 0.031 | 0.019 |
| siphash24      | 0.122 | 0.109 | 0.047 | 0.043 |

 | Test cases | Our work in RV-32  | GCC in in RV-32 | Our work in RV-64  | GCC in in RV-64 |
|--|:--:|:--:|:--:|:--:|
| fib            | 0.433 | 0.235 | 0.442 | 0.246 |
| integr         | 0.212 | 0.180 | 0.216 | 0.160 |
| qsort          | 0.183 | 0.164 | 0.189 | 0.175 |
| fft            | 0.372 | 0.310 | 0.376 | 0.297 |
| fftsp          | 0.839 | 0.729 | 0.784 | 0.680 |
| fftw           | 0.721 | 0.726 | 0.742 | 0.705 |
| sha1           | 0.130 | 0.082 | 0.162 | 0.088 |
| sha3           | 0.173 | 0.099 | 0.114 | 0.047 |
| aes            | 0.130 | 0.117 | 0.143 | 0.164 |
| almabench      | 3.684 | 2.896 | 3.686 | 2.771 |
| lists          | 0.090 | 0.115 | 0.056 | 0.057 |
| binarytrees    | 0.188 | 0.155 | 0.171 | 0.143 |
| fannkuch       | 0.259 | 0.226 | 0.275 | 0.219 |
| knucleotide    | 0.314 | 0.239 | 0.298 | 0.236 |
| mandelbrot     | 0.744 | 0.687 | 0.648 | 0.624 |
| nbody          | 1.606 | 1.322 | 1.527 | 1.290 |
| nsieve         | 0.128 | 0.124 | 0.138 | 0.125 |
| nsievebits     | 0.151 | 0.111 | 0.185 | 0.111 |
| spectral       | 0.686 | 0.487 | 0.474 | 0.464 |
| vmach          | 0.237 | 0.172 | 0.317 | 0.177 |
| bisect         | 0.220 | 0.152 | 0.224 | 0.158 |
| chomp          | 0.481 | 0.277 | 0.451 | 0.320 |
| perlin         | 0.488 | 0.274 | 0.885 | 0.282 |
| siphash24      | 0.168 | 0.159 | 0.128 | 0.103 |

We notice that the performance of the generated code of our assemblers
is slower than that generated by GCC. We conjecture that it is because
the GNU assembler performs optimization in the generated object files,
e.g., by merging the sections, using compressed instructions, or using
peephole optimization. 

### Comparison of development with CompCertELF

We show a comparison with CompCert in terms of the work of
implementaion and proof in Section 5.2 of the paper. Here we give
detailed explanation.

The effort for supporting verified instruction encoding for X86 is
summarized in the following table.

```text
+--------------------------------------------------------------+
|                                | CompCertELF  | Our Approach |
|    Statistics for X86          -------------------------------
|                                | Spec | Proof | Spec | Proof |
+--------------------------------------------------------------+
|  Supported Instructions        | 89   | 24    | 146  |  146  |
+--------------------------------------------------------------+
|  Instruction Encoding (Coq)    | 966  | 1356  | 2249 |  478  |
|  Instruction Encoding (CSLED)  | 0    | 0     | 150  |  0    |
+--------------------------------------------------------------+
```

CompCertELF supports a subset of x86-32. To compile the test cases
presented in the CompCertELF paper, an encoding algorithm for 89
X86-32 instructions is implemented. As a proof-of-concept, 24 out of
the 89 instructions are fully verified (manually proved in Coq that
their decoding is the inverse of encoding), which are sufficient to
support the paper's main example. 966 lines of Coq are written for
specifying 89 instructions (of which 374 lines are for the 24 verified
instructions) and 1356 lines of proofs (in Coq) are written to verify
the encoding of the 24 instructions.

By contrast, our framework supports all the X86-32 and X86-64
instructions used in CompCert (after pretty printing), i.e., a total
of 146 instructions (among which 112 are for both X86-32 and X86-64
and 34 are pure 64-bit instructions). As shown in Table 1 of the
paper, our effort is composed of two parts: 1) 150 lines of CSLED
specifications (in [x86.csled](csled/x86/x86.csled)) for automatically
generating encoders and decoders, and
2) 2249 lines of specification and 478 lines of proofs (in Coq) to
implement and verify the instruction translator (in
[x86/TranslateInstr.v](x86/TranslateInstr.v) and
[x86/RelocBinDecode.v](x86/RelocBinDecode.v)).


By the above statistics, one needs to write about 72 lines of code for
verifying one instruction in CompCertELF ( (374+1356)/24 ~= 72 ). On
the other hand, one only needs to write about 20 lines of code for
verifying one instruction using our framework ( (2249+478+150)/146 ~= 20
). As the total number of instructions grows, the effort saved can be
quite significant.

Finally, CompCertELF does not support RISC-V. In comparison, we
support all 119 RISC-V instructions used in CompCert (after pretty
printing) with statistics in Table 1 of our paper (which we do not
repeat here).