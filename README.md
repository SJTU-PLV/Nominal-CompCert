# Fully Composable and Adequate Verified Compilation with Direct Refinement between Open Modules

## Requirements

The compiler is based on CompCertO and CompCert v3.10. You can find the user manual of 
CompCert [here](http://compcert.inria.fr/man/).

The development is known to compile with the following software:
- Menhir v.20201216
- Coq v8.9.1
- OCaml v4.08.1

## Instructions for compiling

We recommend using the `opam` package manager to set up a build environment. 
We have tested the building on Linux with the following shell commands.

    # Initialize opam (if you haven't used it before)
    opam init --bare
    
    # Create an "opam switch" dedicated to building the code
    opam switch create direct-refinement ocaml-base-compiler.4.08.1
    
    # Install the necessary packages
    opam repository add coq-released https://coq.inria.fr/opam/released
    opam install coq.8.9.1 camlp5.7.14 menhir.20201216
    
    # Configure the current shell to use the newly created opam switch
    eval $(opam env)

In addition, our modifications rely on the Coqrel library (repo in
[here](https://github.com/CertiKOS/coqrel/tree/38dd003d28c91b1b93c01a160a31cdbc3348916a)),
which must be built first. To build Coqrel, proceed in the following
way:

    % (cd coqrel && ./configure && make)

Finally, you can then build the compiler as follows:

    % ./configure x86_64-linux
    % make

If appropriate to your setting, we recommend you use a `-j` option
when invoking make so as to enable parallel compilation.

[TODO]The generated [documentation](doc/index.html) is provided by CompCertO.

## Structure of the Proofs

For reference, you can browse the original CompCert source code [here]
(http://compcert.inria.fr/doc/index.html). We also export our code as
[browsable HTML files](./doc/). Note that we use nominal memory model from
[Nominal CompCert](https://dl.acm.org/doi/10.1145/3498686) in our implementation
for future extensions, while our result does not rely on it.

[TODO: make documentation and leave the html folder in the archive.]

We briefly present the contents of CompCertO, then introduce our implementation of direct
refinement and the examples of end-to-end verification using direct refinement.

### CompCertO

[CompCertO](https://flint.cs.yale.edu/flint/publications/compcerto.html) is a version of CompCert
developed by the Yale FLINT group. The semantic model of CompCert is extended to describe the behavior
of individual compilation units and enable compositional verification.


The language interfaces and simulation conventions are defined in [common/LanguageInterface.v]
(doc/LanguageInterface.html). This file also contains the "concatenation" of simulation conventions
[cc_compose](doc/LanguageInterface.html#cc_compose), C level interface [li_c](doc/LanguageInterface.html#li_c)
and C level simulation convention [cc_c](doc/LanguageInterface.html#cc_c) parameterized over
[CompCert Kripke Logical Relation](doc/CKLR.html#cklr) (which we call Kripke Memory Relation in the paper).
The definition of different memory relations and their properties are in the `cklr` directory.

The open semantics and open simulations are defined in [common/Smallstep.v](doc/Smallstep.html).
[Open semantics](doc/Smallstep.html#semantics) is essentially a mapping from global 
[symbol table](doc/Globalenvs.html#Genv.symtbl) to [open LTS](doc/Smallstep.html#lts) and a skeleton
of local definitions.
The [forward simulation](doc/Smallstep.html#forward_simulation) and the
[vertical composition](doc/Smallstep.html#compose_forward_simulations) are also defined here.
The horizontal composition is defined in [SmallstepLinking.v](doc/SmallstepLinking.html).

You can refer the [CompCertO documentation page](doc/index.html) for further detailed description of CompCertO implementation.

### Direct Refinement 

* `injp` transitivity

    The [definition](doc/InjectFootprint.html#injp) and [transitivity](doc/InjectFootprint.html#injp_injp_eq) of
	`injp` are in [cklr/InjectFootprint.v](doc/InjectFootprint.html). Note that the properties 
	[Mem.ro_unchanged](doc/Memory.html#Mem.ro_unchanged) and [injp_max_perm_decrease](doc/InjectFootprint.html) 
	in `injp_acc` are the same as the assumptions [ec_readonly](doc/Event.html#ec_readonly) and
	[ec_max_perm](doc/Event.html#ec_max_perm) of external functions defined in original CompCert.

    The proof of `injp` transitivity is commented according to the appendix C of our [technical report](popl24-technical-report.pdf).
	We update the memory injections using [update_meminj12](doc/InjectFootprint.html#update_meminj12) and construct
	the intermediate memory state [m2'](doc/InjectFootprint.html#m2') using the memory operations 
	[Mem.step2](doc/Memory.html#Mem.step2) and [Mem.copy_sup](doc/Memory.html#Mem.copy_sup) 
	defined in [common/Memory.v](doc/Memory.html).

* Proofs of individual passes

    For the passes using static analysis, we define the invariant [ro](doc/ValueAnalysis.html#ro) in 
	[backend/ValueAnalysis.v](doc/ValueAnalysis.html). The proof which uses `injp` to guarantee the dynamic values of
	unreachable local variables for these passes can be found in the lemmas `transf_external_states` in 
	[Constpropproof](doc/Constpropproof.html#transf_external_states), [CSEproof](doc/CSEproof.html#transf_external_states) 
	and [Deadcodeproof](doc/Deadcodeproof.html#transf_external_states).

    For [Unusedglob](doc/Unusedglob.html) pass, we assume that the global symbol table are the same for source and target
	semantics. While some local static definitions are removed. We use `injp` in the incoming simulation convention in
	[backend/SimplLocalsproof.v](doc/SimplLocalsproof.html#transf_program_correct') as an example to show that `injp` is a
	reasonable guarantee condition to provide by the compilation passes. The proofs of remaining passes are unchanged from CompCertO.

* Unification of the simulation conventions.
   
  The basic simulation convention between C and assembly [$\mathit{CA}$](doc/CA.html#cc_c_asm) and [$\mathit{CAinjp}$](doc/CA.html#cc_c_asm_injp)
  are defined in [driver/CA.v](doc/CA.html). The proof of
  [$\mathit{c}_{\mathit{injp}} \cdot \mathit{CA} \equiv \mathit{CAinjp}$](doc/CA.html#ccinjp__injp_ca_equiv) 
  can also be found here. We add some refinements about `wt` and `ro` in the end of [driver/CallConv.v](doc/CallConv.v).
  Some new refinement properties about `injp` can be found in the end of [cklr/InjectFootprint.v].

  The direct simulation convention $\mathit{ro} \cdot \mathit{wt} \cdot \mathit{CAinjp} \cdot \mathit{asm}_{\mathit{injp}}$
  is defined as [cc_compcert](doc/Compiler.html#cc_compcert) in [driver/Compiler.v](doc/Compiler.html). 
  
  The unification of simulation convention at the incoming and outgoing side is also carried out here. The implementation is
  actually "expanding" the [cc_compcert](doc/Compiler.html#cc_compcert) step by step to satisty the requirement of all compilation
  passes. For examples, the lemmas [cc_expand](doc/Compiler.html#cc_expand) and [cc_collapse](doc/Compiler.html#cc_collapse) describe
  the main result of the incoming and outgoing side.

### Examples of end-to-end verification

* The Client-Server example:
    The definitions of client and server can be found in [demo/Client.v](doc/Client.html) and [demo/Server.v](doc/Server.html). The C-level specification of the server is defined in
    [demo/Serverspec.v](doc/Serverspec.html), the refinement
    between the server and its specification can be found in
    [demo/Serverproof.v](doc/Serverproof.html)
    [TODO:two versions?]

    + Top-level specification and its refinement proof (Lemma 5.3 in Section 5.2): [demo/ClientServerCspec.v](demo/ClientServerCspec.v)(unoptimized) and [demo/ClientServerCspec2.v](demo/ClientServerCspec2.v)(optimized)
    + Final theorem (Theorem 5.7 in Section 5.2): [demo/ClientServer.v](demo/ClientServer.v)

* The Mutual Sum example from CompCertM:

    We take the mutual summation example from CompCertM to test our framework. The open modules $M_C$ and $M_A$ are defined in [demo/Demo.v](doc/Demo.html). The definition of specification $L_A$ and its refinement with $M_A$ can be found in [demo/Demospec.v](doc/Demospec.html) and [demo/Demoproof.v](doc/Demoproof.html) The Top-level specification of composed semantics and the refinement proof are in [demo/DemoCspec.v](doc/DemoCspec.html) and [demo/Demotopspec.v](doc/Demotopspec.html).

    The final theorem [topspec_correct] is also in [demo/Demotopspec.v](doc/Demotopspec.html#topspec_correct).
    Note that our verification result of this example is slightly different from CompCertM. We build an open simulation which can take arbitrary incoming memories while
    CompCertM establish the RUSC relation (and behavior refinement) based on source-level module-local invariants about the memory.

    
* Client-Server with multiple mutual recursion:
    + Definition of client: [demo/ClientMR.v](demo/ClientMR.v)
    + Top-level specification and its refinement proof: [demo/ClientServerMRCSpec.v](demo/ClientServerMRCSpec.v)
    + Final theorem: [demo/ClientServer.v](demo/ClientServer.v) -- [`spec_sim_mr`](demo/ClientServer.v#L202)
