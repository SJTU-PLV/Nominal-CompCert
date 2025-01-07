# Fully Composable and Adequate Verified Compilation with Direct Refinement between Open Modules



## Closed Smallstep Extension

Inorder to support behavior refinement between closed programs based on CompCertO with DR,
we added the following components:

### 1. The Loading process of open semantics

First we re-introduce the closed semantics and simulations from CompCert in 
[SmallstepClosed.v](common/SmallstepClosed.v) alongwith the definition and lemmas of
Behavior refinement in [Behaviors.v](common/Behaviors.v).

The Loading process of open semantics is defined in [Loading.v](common/Loading.v). 
We need to provide [Initial_state] and [Final_state] to define a closed semantics
from open semantics.

### 2. The Preservation from open simulation to closed simulation

As part of the correctness of loading process, we prove that loading operation for
C and assembly semantics can preserve the open simulation between them using the
simulation convention [cc_compcert] to closed simulation between closed semantics.

The Preservation of forward and backward simulation are proved in [ClosedForward.v](driver/ClosedForward.v)
and [ClosedBackward.v](driver/ClosedBackward.v), respectively. Note that the 
preservation of backward simulation requires more preconditions.

Given the above theorems, we are able to prove the backward simulation (i.e. BehRef) for
[Clight] programs which are separately compiled and finally linked into a closed 
assembly program (Theorem [transf_bsim_link_clight] in [ClosedBackward.v]). We
first horizontally compose the *open* forward simulations, flip it 
into *open* backward simulations and finally "close" it into a closed backward simulation.

Also we can prove the backward simulation between **single** closed [C] programs 
and its compilation result (Theorem [transf_bsim_single_c] in the same file) 
by trivially close the open backward simulation provided by Compiler Correctness 
of CompCertO.

### 3. The Horizontal Composition of open backwrad simulations for separate compilation from C to assembly

Inorder to support the separate compilation of C programs, we need to directly 
compose the open backward simulations between different C units. This is done 
in [SmallstepLinkingBack.v](common/SmallstepLinkingBack.v). This composition 
requires that the source semantics are *deterministic* at interface (defined as 
[determinate_big] in [Smallstep.v](common/Smallstep.v)) and cannot accept a query
at the same time.

Note that we changed the compose operation of open semantics a little bit  (requiring 
the stack of states are alternating between "left" and "right" semantics) in
[SmallstepLinking.v](common/SmallstepLinking.v). The existing composition of
forward simulations ([SmallstepLinkingForward.v](common/SmallstepLinkingForward.v))
and backward simulations shared the same linking operation.

Using the Hori.Comp. of Backward simulations, we are able to prove the behavior refinement
for separately compiled C programs as Theorem [separate_transf_c_program_preservation]
in [ClosedBackward.v](driver/ClosedBackward.v).



## Build Requirements

The compiler is based on CompCertO and CompCert v3.13. You can find the user manual of 
CompCert [here](http://compcert.inria.fr/man/).

The development is known to compile with the following software:
- Menhir v.20220210
- Coq v8.12.0
- OCaml v4.10.1

## Instructions for compiling

We recommend using the `opam` package manager to set up a build environment. 
We have tested the building on Linux with the following shell commands.

    # Initialize opam (if you haven't used it before)
    opam init --bare
    
    # Create an "opam switch" dedicated to building the code
    opam switch create direct-refinement ocaml-base-compiler.4.10.1
    
    # Install the necessary packages
    opam repository add coq-released https://coq.inria.fr/opam/released
    opam install coq.8.12.0 menhir.20220210
    
    # Configure the current shell to use the newly created opam switch
    eval $(opam env)

In addition, our modifications rely on the Coqrel library (repo in
[here](https://github.com/CertiKOS/coqrel),
which must be built first. To build Coqrel, proceed in the following
way:

    % (cd coqrel && ./configure && make)

Finally, you can then build the compiler as follows:

    % ./configure x86_64-linux
    % make

If appropriate to your setting, we recommend you use a `-j` option
when invoking make so as to enable parallel compilation.

You can run the test cases provided by CompCert (except for those using the
interpreter) as follows:

    % cd test
	% make 
	% make test
	
The generated [documentation](doc/index.html) is provided by CompCertO.
