# Towards a Framework for Developing Verified Assemblers for the ELF Format

This material contains the implementation and applications of the
framework presented in our paper. The framework is a template of
verified assemblers that implements the architecture-independent
components. Its code mainly resides in [assembler](assembler) directory. Beside
that, we utilize CSLED[^1] to simplify the implementation and verification
of the instruction encoding, whose code resides in [csled](csled) directory.
As discussed in Section 4 and Section 5 of the paper, we apply our
framework to X86 and RISC-V to generate verified assemblers and
connect them to the backend of Stack-Aware CompCert (based on CompCert
v3.8). These code respectively reside in [x86](x86) and [riscV](riscV) directories.

## Prerequisites

> The following guide assumes that the architecture of your machine is
X86-64. 

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

    # Install and initialize opam (if you haven't used it before)
    sudo apt install opam
    opam init --bare

    # Create an "opam switch" dedicated to building the framework
    opam update
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
    cd bison-3.6.1
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
    cd ~ & wget https://github.com/riscv-collab/riscv-gnu-toolchain/releases\/download/2022.09.30/riscv32-glibc-ubuntu-20.04-nightly-2022.09.30-nightly.tar.gz -O riscv32-gnu-toolchain.tar.gz
    tar -xf riscv32-gnu-toolchain.tar.gz
    ~/riscv32-gnu-toolchain/bin/riscv32-unknown-linux-gnu-gcc -v

    # Install Qemu
    # Prerequisites of Qemu
    sudo apt install autoconf automake autotools-dev curl libmpc-dev libmpfr-dev libgmp-dev \
              gawk build-essential texinfo gperf libtool patchutils bc \
              zlib1g-dev libexpat-dev pkg-config  libglib2.0-dev libpixman-1-dev libsdl2-dev \
              git tmux python3 python3-pip ninja-build
    # Install Qemu from source
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
  lemmas to verify the consistency between encoders and decoders
  where $n$ is the number of instructions. So it is impractical for
  the readers to run the proofs. We provide three options (O0, O1 and
  O2) to speed up the proofs by replacing the enormous proof scripts
  with `Admitted` so that it can save lots of time. Note that we have
  already checked the complete proofs in our machines. We also
  evaluate the consumption of time which is listed below.

| Options | Time Consumption |
|---------|:----------------:|
| O0 (no `Admitted`)     | ~1h30min        |
| O1 (half `Admitted`)   | ~40min          |
| O2 (all `Admitted`)    | ~10min          |

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
    ./configure rv32-linux -toolprefix ~/riscv/bin/riscv32-unknown-linux-gnu- -simulator qemu-riscv32 -simu-ld ~/riscv/sysroot -csled-opt O2
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
| $P_{\mathcal{R}}$: Relocatable Programs | [assembler/RelocProg.v](assembler/RelocProg.v)<br>[assembler/RelocProgSemantics.v](assembler/RelocProgSemantics.v)($[\![P_0]\!]$)<br>[assembler/RelocProgSemantics1.v](assembler/RelocProgSemantics1.v)($[\![P_1]\!]$)<br>[assembler/RelocProgSemantics2.v](assembler/RelocProgSemantics2.v)($[\![P_2]\!]$) | [x86/RelocProgSemanticsArchi.v](x86/RelocProgSemanticsArchi.v)<br>[x86/RelocProgSemanticsArchi1.v](x86/RelocProgSemanticsArchi1.v) | [riscV/RelocProgSemanticsArchi.v](riscV/RelocProgSemanticsArchi.v)<br>[riscV/RelocProgSemanticsArchi1.v](riscV/RelocProgSemanticsArchi1.v) | 
| $P_{\mathcal{E}}$: Relocatable ELF | [elf/RelocElf.v](elf/RelocElf.v)<br>[elf/RelocElfSemantics.v](elf/RelocElfSemantics.v)($[\![P_3]\!]$) | [x86/RelocElfArchi.v](x86/RelocElfArchi.v) | [riscV/RelocElfArchi.v](x86/RelocElfArchi.v) |
$\mathbb{C}_0$: Generation of Relocatable Programs | [assembler/Symbtablegen.v](assembler/Symbtablegen.v)<br>[assembler/Symbtablegenproof.v](assembler/Symbtablegenproof.v) | [x86/SymbtablegenproofArchi.v](x86/SymbtablegenproofArchi.v) | [riscV/SymbtablegenproofArchi.v](riscV/SymbtablegenproofArchi.v) |
$\mathbb{C}_1$: Generation of Relocation Table | [assembler/Reloctablesgen.v](assembler/Reloctablesgen.v)<br>[assembler/Reloctablesgenproof.v](assembler/Reloctablesgenproof.v) | [x86/ReloctablesgenArchi.v](x86/ReloctablesgenArchi.v)<br>[x86/ReloctablesgenproofArchi.v](x86/ReloctablesgenproofArchi.v) | [riscV/ReloctablesgenArchi.v](x86/ReloctablesgenArchi.v)<br>[riscV/ReloctablesgenproofArchi.v](x86/ReloctablesgenproofArchi.v) |
$\mathbb{C}_2$: Instruction and Data Encoding | [assembler/RelocBingen.v](assembler/RelocBingen.v)<br>[assembler/RelocBingenproof.v](assembler/RelocBingenproof.v) | Translators: [x86/TranslateInstr.v](x86/TranslateInstr.v)<br>[x86/RelocBinDecode.v](x86/RelocBinDecode.v)<br>CSLED Spec: [x86.csled](csled/x86/x86.csled) | Translators: [riscV/TranslateInstr.v](riscV/TranslateInstr.v)<br>[riscV/RelocBinDecode.v](riscV/RelocBinDecode.v)<br>CSLED Spec: [riscv.csled](csled/riscv/riscv.csled) |
$\mathbb{C}_3$: Generation of Relocatable ELF | [elf/RelocElfgen.v](elf/RelocElfgen.v)<br>[elf/RelocElfgenproof.v](elf/RelocElfgenproof.v) | [x86/RelocElfgenproofArchi.v](x86/RelocElfgenproofArchi.v) | [riscV/RelocElfgenproofArchi.v](riscV/RelocElfgenproofArchi.v) |

By the way, the top-level definitions of the target printers are defined
in [x86/CompilerAux.v](x86/CompilerAux.v) and [riscV/CompilerAux.v](riscV/CompilerAux.v).


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
    make clean && make all
    # Start the test
    make test

If you configure to RV-32/64, you need to ensure that the RISC-V GNU
Toolchain and Qemu have been installed and configured in your machine.
The installation and configuration are introduced above. If they are
all done, you can type the same commands to run the test.

    cd test
    # Compile the test cases
    make clean && make all
    # Start the test
    make test

### Performance Evaluation

We evaluate the performance of the generated code with the scripts
provided by CompCert in [test/c/Makefile](test/c/Makefile). This code
is compiled by CompCert and assembled by our assemblers or by the GNU
assembler (GAS). The scripts measure the time (in seconds) by running
the code multiple times. and calculating their average value. 

    # Evaluate the code generated by our assemblers
    cd test/c
    make all
    make bench

    # Evaluate the code generated by CompCert and GNU assembler
    cd test/c
    make all_compcert_gcc
    make bench_compcert_gcc

 We run the above scripts in WSL2 Ubuntu20.04 on a machine with
 Intel(R) Core(TM) i9-12900H CPU. The result of the evaluation is
 shown in [performance.md](performance.md).

### Comparison of development with CompCertELF

We show a comparison with CompCertELF[^2] in terms of the work of
implementation and proof in Section 5.2 of the paper. Here we give
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
|  Instruction Encoding (Coq)    | 966  | 1356  | 2178 |  469  |
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
2) 2178 lines of specification and 469 lines of proofs (in Coq) to
implement and verify the instruction translator (in
[x86/TranslateInstr.v](x86/TranslateInstr.v) and
[x86/RelocBinDecode.v](x86/RelocBinDecode.v)).


By the above statistics, one needs to write about 72 lines of code for
verifying one instruction in CompCertELF ( (374+1356)/24 ~= 72 ). On
the other hand, one only needs to write about 20 lines of code for
verifying one instruction using our framework ( (2178+469+150)/146 ~=
19 ). As the total number of instructions grows, the effort saved can
be quite significant.

Finally, CompCertELF does not support RISC-V. In comparison, we
support all 119 RISC-V instructions used in CompCert (after pretty
printing) with statistics in Table 1 of our paper (which we do not
repeat here).

### Reference

[^1]: Xu, X., Wu, J., Wang, Y., Yin, Z., Li, P. (2021). Automatic
Generation and Validation of Instruction Encoders and Decoders. In:
Silva, A., Leino, K.R.M. (eds) Computer Aided Verification. CAV 2021.
Lecture Notes in Computer Science(), vol 12760. Springer, Cham.
https://doi.org/10.1007/978-3-030-81688-9_34

[^2]: Wang Y, Xu X, Wilke P, et al. CompCertELF: verified separate compilation of C programs into ELF object files[J]. Proceedings of the ACM on Programming Languages, 2020, 4(OOPSLA): 1-28.