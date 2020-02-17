# CompCertO

A version of CompCert featuring an open module semantics, designed to
target the framework of *refinement-based game semantics*.

## Overview

This is a modified version of CompCert v3.5. The language semantics
and correctness proofs have been updated to describe the behavior of
individual compilation units. Most passes from Clight to Asm have
been update, for the x86 architecture.

## Building

Since our compiler uses Clight as the source language, the first few
passes are not available and the full extracted compiler cannot be
built. However the Coq version of the Clight to Asm compiler can be
compiled in the following way.

Build requirements are similar to that of CompCert v3.5. In addition,
our modifications rely on the Coqrel library, which must be built
first. We will include Coqrel in any self-contained archive we
distribute, but if you are working in a git clone, you must first
retreive it with the following commands:

    % git submodule init
    % git submodule update

In any case, to build Coqrel, proceed in the following way:

    % (cd coqrel && ./configure && make)

You can then build the updated proof as follows:

    % ./configure x86_64-linux
    % make

If appropriate to your setting, we recommend you use a -j option when
invoking make so as to enable parallel compilation.

The remainder of this document is the original `README.md` distributed
with CompCert v3.5.

---

# CompCert
The verified C compiler.

## Overview
The CompCert C verified compiler is a compiler for a large subset of the
C programming language that generates code for the PowerPC, ARM, x86 and
RISC-V processors.

The distinguishing feature of CompCert is that it has been formally
verified using the Coq proof assistant: the generated assembly code is
formally guaranteed to behave as prescribed by the semantics of the
source C code.

For more information on CompCert (supported platforms, supported C
features, installation instructions, using the compiler, etc), please
refer to the [Web site](http://compcert.inria.fr/) and especially
the [user's manual](http://compcert.inria.fr/man/).

## License
CompCert is not free software.  This non-commercial release can only
be used for evaluation, research, educational and personal purposes.
A commercial version of CompCert, without this restriction and with
professional support, can be purchased from
[AbsInt](https://www.absint.com).  See the file `LICENSE` for more
information.

## Copyright
The CompCert verified compiler is Copyright Institut National de
Recherche en Informatique et en Automatique (INRIA) and 
AbsInt Angewandte Informatik GmbH.


## Contact
General discussions on CompCert take place on the
[compcert-users@inria.fr](https://sympa.inria.fr/sympa/info/compcert-users)
mailing list.

For inquiries on the commercial version of CompCert, please contact
info@absint.com
