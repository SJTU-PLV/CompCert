# Fully Composable and Adequate Verified Compilation with Direct Refinement between Open Modules

## Requirements

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

## Current status

Todos: 

Injp Composition : InjectFootprint.v <- high priority
leaving passes : SSAsmproof, RealAsmproof, PseudoInstructionsproof.
semantics: RealAsm, PseudoInstruction.
Some CKLR 'rel' files : Clightrel, RTLrel, Asmrel, AsmLinking. :
(seems doable but verbose, needs to change CKLR, and fix the "oracle semanics changes..")
Final Composition : CA.v Compiler.v


Roadmap: 
1) injp comp;
2) 定义RealAsm 和 PseudoInstruction open semantics
3) 写 leaving passes 的证明框架 (有一个需要injp or ext?)
4) 完成final composition
  4.1 RealAsm Linking
  4.2 底层额外的接口能处理吗
  4.3 写出final theorem
5) Fix self-simulation (CKLR)
6) Fix other admits
