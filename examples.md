## Section 5: End-to-End Verification of Heterogenous Modules

In the section 5 of the paper, we introduce the end-to-end
verification of the client-server example (whose code and proof
structure are shown in Figure 3 and Figure 4, respectively) based on
the direct refinement. 

### Definitions of the Client-Server Example

The C or assembly code of `client.c`, `server.s` and `server_opt.s`
are shown in Figure 3 in our paper.

* `client.c` is defined in [Client.v](demo/Client.v).
* `server.s` and `server_opt.s` are defined in [Server.v](demo/Server.v).

### Refinement for the Hand-written Server (Section 5.1)

* (Definition 5.1) The hand-written specification ($L_S$) for the
  optimized server (i.e., `server_opt.s`) is defined by `L2` in [Serverspec.v](demo/Serverspec.v#L116). The hand-written specification (not
  discussed in the paper) for `server.s` is defined by `L1` in [Serverspec.v](demo/Serverspec.v#L98).
* (Theorem 5.2) The theorem of $L_S
  \leqslant_{\mathbb{C}}[\![\texttt{server\_opt.s}]\!]$ is defined by
  `semantics_preservation_L2` in [Serverproof.v](demo/Serverproof.v).
  This proof is decomposed into  $L_S \leqslant_{\texttt{wt}} L_S$ and
  $L_S \leqslant_{\texttt{ro}\cdot\texttt{CAinjp}}
  [\![\texttt{server\_opt.s}]\!]$, which are stated in
  `self_simulation_wt'` and `CAinjp_simulation_L2`, respectively. More specifically, for the verification of $L_S \leqslant_{\texttt{ro}\cdot\texttt{CAinjp}} [\![\texttt{server\_opt.s}]\!]$, the simulation relation is defined by `match_state_c_asm` in [Serverproof.v](demo/Serverproof.v).

### End-to-End Correctness Theorem (Section 5.2)

* Definition of the top-level specification (optimized version) $L_{\texttt{CS}}$ is by `top_spec2` in [ClientServerCspec2.v](demo/ClientServerCspec2.v). The unoptimized top-level specification is defined by `top_spec1` in [ClientServerCspec1.v](demo/ClientServerCspec2.v).
* (Lemma 5.3) $L_{\texttt{CS}} \leqslant_{\texttt{ro}\cdot\texttt{wt}\cdot \texttt{c}_{\texttt{injp}}} [\![\texttt{client.c}]\!] \oplus L_S$ is defined by `top_simulation_L2` in [ClientServerCspec2.v](demo/ClientServerCspec2.v). The simulation relation is defined by `match_state` in the same file. Note that `top_simulation_L1` is the refinement theorem for the unoptimized server, i.e., $L_S$ and $L_{\texttt{CS}}$ in $L_{\texttt{CS}} \leqslant_{\texttt{ro}\cdot\texttt{wt}\cdot \texttt{c}_{\texttt{injp}}} [\![\texttt{client.c}]\!] \oplus L_S$ are replaced by `L1` and `top_spec1`, respectively.
* (Theorem 5.4) `compose_simulation` in [Smallstep.v](common/Smallstep.v) and `asm_linking` in [AsmLinking.v](x86/AsmLinking.v).
* (Lemma 5.5) `compose_Client_Server_correct2` in [ClientServer.v](demo/ClientServer.v).
* (Lemma 5.6) `ro_injp_cc_compcert` in [ClientServer.v](demo/ClientServer.v).
* (Theorem 5.7) `spec_sim_2` in [ClientServer.v](demo/ClientServer.v).
  
### Other Examples

The following examples are not discussed in our paper, because they
are more complicated than the client-server example introduced in our
paper. However, we implement and verify them to show the effectiveness of our framework.

#### Mutual Recursive Client-Server Example

We define a mutual recursive client-server example where the server
code is the same as `server.s` in [Server.v](demo/Server.v) and the
client code can repeatedly invoke the server to encrypt a list of
data. The C code of the new client (denoted by `client_mr.c`) is shown
below:

```c
/* client_mr.c */
int input[N], result[N];
int index;

void request (int *r){
  if (index == 0) {
    index += 1;
    encrypt(input[index - 1], request);
  }
  else if (0 < index < N){
    result[index - 1] = *r;
    index += 1;
    encrypt(input[index - 1], request);
  }
  else {
    result[index - 1] = *r;
    return;
  }
}
```

* `client_mr.c` is defined by the Coq definition `client` in
  [ClientMR.v](demo/ClientMR.v).
* The definition of server is the same as the example (`server.s`)
  introduced in our paper, i.e., it is defined by  `L1` in
  [Server.v](demo/Server.v). Note that we implement the repeated
  invocation by directly passing the `request` function in `client` to
  the server. Thereby the server can jump to the call-back function
  (the `request` function in client) to encrypt the subsequent data.
* The top level specification is defined by `top_spec1` in
  [ClientServerMRCSpec.v](demo/ClientServerMRCSpec.v).
* The refinement $\texttt{top\_spec1} \leqslant_{\texttt{ro}\cdot\texttt{wt}\cdot \texttt{c}_{\texttt{injp}}} [\![\texttt{client\_mr.c}]\!] \oplus \texttt{L1}$ is defined by `top_simulation_L1`, `top1_ro` and `top1_wt` in [ClientServerMRCspec.v](demo/ClientServerMRCSpec.v).
* The final theorem $\texttt{top\_spec1} \leqslant_{\mathbb{C}} [\![\texttt{CompCert}(\texttt{client\_mr.c}) + \texttt{server.s}]\!]$ is defined by `spec_sim_mr` in [ClientServer.v](demo/ClientServer.v).

#### Mutual Summation Example

We present the application of our method to an example borrowed from
CompCertM[^1] — two programs that mutually invoke each other to finish
a summation task. One program (denoted by `M_C`) is implemented in C
and the other (denoted by `M_A`) is implemented in assembly. Their code are shown below:

```C {.line-numbers}
/* C implementation of M_C */
  static int memoized[1000] = {0};
  int f(int i) {
    int sum;
    if (i == 0) return 0;
    sum = memoized[i];
    if (sum == 0) 
    { sum = g(i-1) + i;
      memoized[i] = sum; }
    return sum;
  }
  /* C code corresponding to M_A */
  static int s[2] = {0,0};
  int g(int i){
    int sum;
    if (i == 0) return 0;
    if (i == s[0]) 
      { sum = s[1]; } 
    else 
      { sum = f(i-1) + i;
        s[0] = i;
        s[1] = sum; }
    return sum;
  }
```

```x86asm
/* Assembly implementation of M_A */  
g:  Pallocframe 24 16 0 
    Pmov RBX 8(RSP) // save RBX
    /* begin */
    Pmov RDI RBX 
    Ptestl RBX RBX  // i==0
    Pjne l0  
    Pxorl_r RAX     // rv=0
    Pjmp l1
l0: Pmov s[0] RAX 
    Pcmpl RAX RBX  // i==s[0]
    Pje l2
    Pleal -1(RBX) RDI 
    Pcall f        // f(i-1)
    Pleal (RAX,RBX) RAX//sum=f(i-1)+i
    Pmov RBX s[0]  // s[0] = i
    Pmov RAX s[1]  // s[1] = sum
    Pjmp l1 
l2: Pmov s[1] RAX  // rv=s[1]
    /* return */
l1: Pmov 8(RSP) RBX 
    Pfreeframe 24 16 0 
    Pret
```

The procedure of the refinement is shown below:
* First, like what we do for the server in the above example, we define a high-level specification (called `L_A`) for `M_A`. The definition of `L_A` is in [Demospec.v](demo/Demospec.v) with the same name. The refinement $\texttt{L\_A} \leqslant_\mathbb{C} [\![\texttt{M\_A}]\!]$ is defined by `M_A_semantics_preservation` in [Demoproof](demo/Demoproof.v). The simulation relation of this proof is defined by `match_state_c_asm` in the same file.
* Second, for `M_C`, we also define a specification `L_C` and show that $\texttt{L\_C} \leqslant_{\texttt{ro}\cdot\texttt{wt}\cdot \texttt{c}_{\texttt{injp}}}[\![\texttt{M\_C}]\!]$. `L_C` is defined by `L_C` in [DemoCspec.v](demo/DemoCspec.v) and the refinement is defined by `cspec_simulation`, `cspec_ro` and `cspec_self_simulation_wt` in [DemoCspec.v](demo/DemoCspec.v).
* With the above definitions, we define a top-level specification called `top_spec` in [Demotopspec.v](demo/Demotopspec.v). We prove that $\texttt{top\_spec}  \leqslant_{\texttt{ro}\cdot\texttt{wt}\cdot \texttt{c}_{\texttt{injp}}} \texttt{L\_C} \oplus \texttt{L\_A}$ in [Demotopspec.v](demo/Demotopspec.v) by `top_simulation`, `top_ro` and `topspec_self_simulation_wt`.
* Finally, with the above refinements and the correctness of CompCert(O), we show $\texttt{top\_spec} \leqslant_\mathbb{C} \texttt{CompCert}(\texttt{M\_C}) \oplus [\![\texttt{M\_A}]\!]$ in `topspec_correct` in [Demotopspec.v](demo/Demotopspec.v).

## Reference

[^1]: Youngju Song, Minki Cho, Dongjoo Kim, Yonghyun Kim, Jeehoon Kang, and Chung-Kil Hur. 2020. CompCertM: CompCert with C-Assembly Linking and Lightweight Modular Verification. Proc. ACM Program. Lang. 4, POPL, Article 23 (Jan. 2020),31pages. https://doi.org/10.1145/3371091