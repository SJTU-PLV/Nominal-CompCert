# Detailed Descriptions of the Code Base

## An Overview


```
.
├── Makefile
├── README.md
├── STRUCTURE.md
├── coq
│   ├── flocq
│   ├── lib
│   └── utils
├── coqgen
│   └── texts
├── evaluation
├── ir
├── main.cc
├── parser
├── smt-parser.py
└── testcases
```

This artifact contains the following contents:

- `Makefile` is for building and testing the framework.
- `README.md` is the readme file.
- `STRUCTURE.md` is this file.
- `coq/` contains Coq libraries used by the framework.
- `parser/` contains the implementation of the CSLED parser.
- `ir/` contains the definition of intermediate representations and a semantic checker.
- `coqgen/` contains the implementation of the generator.
- `main.cc` is the entry point of the generator.  
- `smt-parser.py` is for parsing the generated verification conditions and feeding them
  into to the Z3 solver.  
- `evaluation/` contains code for evaluating the performance of generated encoders and decoders.
- `testcases/` contains the test cases.


## Generator

As described in [README](README.md), the generator is the central
component of the framework. It has a front-end and back-end. It is mostly
implemented in C++.

### The front-end

The front-end is implemented in `parser/` and `ir/`. We use Flex and
Bison to implement the CSLED parser.  The lexer and parser are defined in
`parser/lexical.l` and `parser/syntax.y`, respectively.  Specifically,
`parser/syntax.y` implements the syntax in Fig.4 of the paper. 

The output AST of the parser is defined in `parser/ast.hh`. A visitor
pattern for traversing the AST is implemented in
`parser/visitor.hh`. The semantic checking and resolution of names for
AST are implemented by using this visitor in
`ir/name_checker.cc`. After checking, the AST is translated into
IR. This translation is defined in `ir/ir.cc`. The IR is defined in
`ir/types.hh`.

### The back-end

The back-end is implemented in `coqgen/`.  `coqgen/coqgen.cc` is its
entry point. It applies different algorithms to the IR to
generate Coq proof scripts (`.v` files) and verification conditions.

- `coqgen/type_printer.cc` implements the generation of inductive
  types of instructions and operands.

- `coqgen/encoder.cc` implements the generation of encoders.

- `coqgen/decoder.cc` implements the generation of decoders.

- `coqgen/enc_consistency_printer.cc` and
  `coqgen/dec_consistency_printer.cc` implement the generation of
  consistency proofs.

- `coqgen/spec_printer.cc` implements the generation of relational specifications.

- `coqgen/soundness_printer.cc` implements the generation of soundness
  proofs w.r.t. the above relational specifications.

- `coqgen/bf_true_printer.cc` implements the generation of structural
  properties for instructions and addressing modes.

- `coqgen/proof_condition_printer.cc` and `coqgen/bp_printer.cc`
  implement the generation of verification conditions. The former is
  for generating the verification conditions in `bp_in_smt.txt`. The
  latter is for translating these verification conditions into Axioms
  in Coq.

- `coqgen/texts` contains snippets of Coq code to be combined with
  the generated Coq scripts to form complete scripts.

- `coqgen/util.cc` contains some utility functions in C++.

## Coq Libraries

`coq/utils/BPProperty.v` contains some properties about the bit-level
operations in Coq. Other files under the `coq` directory are imported
from [CompCert](https://compcert.org/). We make use of the Error monad
operation and the byte data formats in the CompCert library.

## Evaluation

The `evaluation` directory contains code for evaluating the performance of
generated encoders and decoders. 

- `evaluation/Extraction.v` is used to extract OCaml functions from
Coq definitions.

- `evalencdec.ml` is used to randomly generate instructions, encode
them, and decode the results back.

- Other files are mostly used for collecting data.



