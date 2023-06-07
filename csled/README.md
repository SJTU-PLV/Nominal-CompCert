# Automatic Generation and Validation of Instruction Encoders and Decoders (Artifact)

This artifact demonstrates a framework for generating verified instruction
encoders and decoders from specifications that precisely capture the
instruction formats in ISA manuals. It accompanies the following paper:

  > Automatic Generation and Validation of Instruction Encoders and Decoders. 

In the remaining sections, we will first introduce the structure of
the artifact, then present the steps for evaluating the artifact.

## The Structure of the Artifact

The key constituents of the framework are 

1. A specification language called CSLED (an enhancement to Norman
   Ramsey's Specification Language for Encoding and Decoding) for
   declaratively describing instruction formats in CSIC/RISC;

2. A program called the __generator__ that takes as input CSLED files
   containing instruction specifications and produces as output
   components that collectively form the verified instruction encoders
   and decoders.

The generator is the composition of a front-end and a back-end:

1. The front-end consists of a parser and a checker for transforming
   textual CSLED specifications into their intermediate representation
   (IR) in memory.

2. The back-end contains a collection of algorithms for generating verified
   encoders and decoders from the IR. Specifically, it includes the
   following algorithms, each of which takes the IR as input and
   generates components written in Coq:

   (1) An algorithm for generating inductive types characterizing the
   instructions and their operands;

   (2) An algorithm for generating instruction encoders that
   transform elements of the above inductive types into bit-strings;

   (3) An algorithm for generating instruction decoders that
   transform bit-strings back into elements of the inductive types;

   (4) An algorithm for generating the consistency proofs of the above
   encoder and decoder pairs, i.e., proofs that they are inverses of
   each other;

   (5) An algorithm for generating predicative specifications relating
   the inductive definitions of instructions and operands to their
   binary forms;

   (6) An algorithm for generating proofs that the encoders and
   decoders are sound w.r.t. the above specifications.

   In the proofs of consistency, we make use of the fact that an
   encoder and its corresponding decoder always branch into the same
   case for any given instruction or operand. This requires us to
   prove that branching into different cases in encoding and decoding
   is not possible (as described in Section 6.1 of the paper). The
   conditions for such branching are formulated as a set of
   unsatisfiable propositions that can be easily discharged by using
   SMT solvers (`Z3` in our case); we shall call those conditions
   __verification conditions__ in the remaining sections. 

   The back-end further contains the following components for
   discharging verification conditions:

   (7) An algorithm for generating the verification conditions;

   (8) A python script (named `smt-parser.py`) that discharges these
   conditions using an SMT solver.

The detailed descriptions of the code base can be found at
[here](STRUCTURE.md) for interested readers.


## Prerequisites for Artifact Evaluation:

If you use the VM, you are all set.

If you would like to perform the evaluation on your own machine, you
will need to copy the source code over and install the following
software on a 64-bit Linux distro:

- Python 3.8.5
- OCaml 4.08.1
- Coq 8.11.0
- Z3 4.8.10
- Bison 3.6
- Flex 2.6.4

You will also need to run the following command to install the python dependency:

    pip3 install prettytable z3-solver numpy

Evaluation on local machines may be faster and more memory efficient
than evaluation on the VM.


## Compilation and Usage of the Generator

To compile the generator, run the following command (you may also add
`-j` option to parallelize the make process):

    make generator

As a result, an executable file named `generator` will be produced.

To use the generator, run the following command:

    ./generator <CSLED FILE>

The generator takes CSLED files named `*.csled` as input and produces
(synthesizes) the following files as output:

- `EncDecRet.v`. It contains the inductive definitions of instructions
  and their operands, together with the definitions of their encoders
  and decoders. These are the outputs of above algorithms (1), (2) and
  (3), respectively.

- `EncConsistency.v`, `DecConsistency.v` and `BFtrue.v`. These three
  files together form the consistency proof, i.e., the output of
  algorithm (4). 

  The first file contains one side of the consistency proof: encoding
  of any instruction or operand followed by decoding gets back to the
  original input.

  The second contains the other side of the consistency proof:
  decoding of any bit-string followed by encoding gets back to the
  original bit-string;

  The third contains structural properties of instruction formats and
  bit-strings commonly required for the above proofs.

- `RelSpec.v`. It contains the relational specification of the
  instructions and operands, i.e., the output of algorithm (5).

- `Soundness.v` : It contains the soundness proof of the encoder and
  decoder, i.e., the output of algorithm (6).
  
- `bp_in_smt.txt` and `VerificationCondition.v`. The former file
  contains the verification conditions to be discharged by the SMT
  solver, i.e., the output of algorithm (7). The latter file contains
  a collection of Coq axioms that mirrors the verification conditions
  in `bp_in_smt.txt`. Those axioms are necessary for proving the
  consistency of encoders and decoders.

### A Simple Example 

Consider `five-instr.csled` in the directory `testcases`. It is a
CSLED specification of 5 x86-32 instructions (with the additional Nop
instruction). By running the following command

    ./generator testcases/five-instr.csled

a set of files as described above is generated under the directory `generated`,
where

- `EncDecRet.v` contains the inductive types for instructions
  (`Instruction`) and their addressing mode operands (`Addrmode`), the
  definitions of their encoders (`encode_Addrmode` and
  `encode_Instruction`) and decoders (`decode_Addrmode` and
  `decode_Instruction`).

- `EncConsistency.v` contains half of the proofs of consistency for
  addressing modes and instructions (`encode_Addrmode_consistency` and
  `encode_Instruction_consistency`).

- `DecConsistency.v` contains the other half proofs of consistency
  (`decode_Addrmode_consistency` and `decode_Instruction_consistency`).

- `BFtrue.v` contains some structural properties for instructions and
  addressing modes.

- `RelSpec.v` contains the relational specifications of addressing
  modes and instructions (`Addrmode_spec` and `Instruction_spec`).

- `Soundness.v` contains the soundness proofs for encoding addressing
  modes and instructions (`encode_Addrmode_sound` and
  `encode_Instruction_sound`). The soundness of decoding instructions
  (`decode_Instruction_sound`) is derived from the soundness of
  encoding and consistency as described in Section 6.2 of the paper.
  Since we are eventually only interested in the soundness of
  the top-level inductive type (i.e., `Instruction` in this case), we do
  not prove a similar lemma for addressing modes (which can be easily
  proved by following a similar pattern).

- `bp_in_smt.txt` essentially encodes the verification conditions
  necessary for proving consistency. We elaborate on its format as
  follows.

  An atomic structural condition is presented as three consecutive
  lines of texts. The first line indicates its type, i.e. equal (`EQ`)
  or not equal (`NE`). The second line is a bit-string for masking and
  begins with a letter `M`.  The third line is a regular bit-string
  and begins with a letter `V`.  Together, they form a triple `(REL,
  Mmmm, Vvvv)`, which stands for `mmm REL vvv`.

  Given a class, there is a structural condition (defined in Section
  4.4 of the paper) for each of its branches. In `bp_in_smt.txt`, a
  structural condition is the logical conjunction of a sequence of
  atomic structural conditions which are separated by `******`. The
  structural conditions for different branches of the class are
  separated by `-------`. Furthermore, the structural conditions for
  different classes are separated by `+++++++`.
  
  The verification conditions are implicitly defined in
  `bp_in_smt.txt` as follows: for every combination of two different
  branches in a given class, there exists a verification condition
  that is the conjunction of the two structural conditions associated
  with the two branches.

- `VerificationCondition.v` contains a collection of axioms that
  mirrors the verification conditions described above.


## Validation of the Generated Proofs

To make sure that the generated (synthesized) proofs of consistency
and soundness are indeed correct, we validate them as follows:

- First, to make sure that the verification conditions can indeed be
  discharged by the SMT solver, we run the following command:

      make smt

  As a result, the python script `smt-parser.py` reads in the
  verification conditions from `bp_in_smt.txt` and check their
  unsatisifiability using `Z3`.

- Then, we run the following commands to validate the soundness and
  consistency proofs:

      make gendep CoqProject
      make proof

  Here, the first command generates the dependency between the Coq
  files; the second command evaluates the proof scripts of consistency
  and soundness in Coq.

  We advise to not use the `-j` option in `make
  proof`. This is to reduce the amount of memory consumed by proof
  checking in Coq which can be quite big for large test cases, as we
  shall see shortly.


### Continuing with the Simple Example  

To illustrate how proof validation works, we use the proofs generated
from `five-instr.csled` as a simple example. 

- By running `make smt`, we will get the following responses:
  
      python3 smt-parser.py
      Start Solving Proof Conditions with Z3....
      Success!

- By running `make proof`, the proof scripts for consistency and
  soundness will be checked by Coq. This may take several minutes for
  this simple test case.


### Validation of the Full Test Case

As we have discussed in Section 7 of the paper, we have evaluated a
specification containing 186 representative x86-32 instructions. This
specification is defined in `testcases/all.csled`. 

A direct validation of the above test case consumes a lot of memory
and takes a long time. Therefore, we have prepared other test cases by
dividing the full specification into smaller pieces, so that the
proofs generated from each of which can be validated by using a
reasonable amount of memory and in a reasonable time.

Specifically, `testcases/forty`, `testcases/sixty` and
`testcases/hundred` contain the results of dividing
`testcases/all.csled`, such that each file in these directories
contains about 40, 60 and 100 instructions, respectively. They can be
tested by following the standard process. 

The following table shows the approximate time (measured by using the
`time` command) required for checking __a single file__ in each of
those directories and the require memory in each case. The evaluation
is performed in the VM hosted in Ubuntu LTS 20.04 running on a machine
with Intel(R) Core(TM) i9-9900K CPU @ 3.60GHz (8 Cores) and 64GB
memory.

| Testcase                    | No. of Instructions | SMT Time | Coq Time | Required Memory|
| --------------------------- | ------------ | -------- | ---------- | ------ |
| testcases/forty/*.csled      | 40           | 6s      | 5m2s       | 1GB   |
| testcases/sixty/*.csled      | 60           | 12s      | 7m7s      | 4GB    |
| testcases/hundred/*.csled    | 100          | 27s      | 13m13s      | 8GB    |
| testcases/all.csled          | 186          | 1m40s      | 54m51s    | 20GB (32GB recommended) |


## Performance Evaluation 

### Evaluate CSLED Encoder and Decoder

In this section, we conduct the performance evaluation as described in
Section 7 of the paper. Note that the evaluation result on the paper is for the
full test case in `all.csled` (containing 186 x86-32 instructions).

After running the generator on a test set, e.g., `testcases/sixty/c2.csled`, 
we extract the OCaml implementations of encoders and decoders 
from their Coq definitions by running the following commands:

    make gendep CoqProject 
    make -j evaluation/Extraction.vo

The second `make` command extracts the encoder and decoder in
```EncDecRet.v``` into an OCaml program in ```encdec.ml```. 

To evaluate the performance of the extracted encoders and decoders, we
further run the following commands :

    cd evaluation/
    bash eval.sh <testFileName> [testNumber]

`<testFileName>` is a `.ml` file related to the specification
we selected before. For example, if we run the generator on
`testcases/sixty/c2.csled` before, the `<testFileName>` 
should be `testcases/sixty/c2.ml`.
This test module randomly selects `[testNumber]`(10000 by default) of instructions 
from the supported ones of the related test case,
encodes the selected instructions into bit strings, 
and decodes the encoding result. It also records and prints out the execution time 
of the encoder and decoder, respectively.

Here, the bash script `eval.sh` first copies the selected test file to
the build directory, then build the evaluation program which 
simply passes the `testNumber` to the test module.
Then the script runs the program for 30 times. After that,
it calls `eval.py` to calculate the statistics.


Then, `eval.sh` prints the evaluation results to the standard output
in the following formats: 
(The example tests `testcases/sixty/c2.ml` with 10000 instructions.)


```
Name      Median  Variance  Variance/Median
CSLEDEnc  0.689   0.00027   0.00039
CSLEDDec  0.928   0.00048   0.00052
```


Note that these results are different from the ones in the paper
because of differences in execution environments. Your results may
also be different for the same reason.

### Compare the CSLED Encoder and Decoder with Handwritten Ones

To compare the CSLED Encoder and Decoder with the handwritten ones,
we provide the handwritten encoder and decoder used in the CompCertElf.
Simply use the following command to profile their performance:

```
./compare-with-hw.sh <testNumber>
```

The input/output format is similar with ones stated in the previous section.