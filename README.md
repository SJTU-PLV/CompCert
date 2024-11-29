# Rust Verified Compiler Based on CompCertO

## Requirements

The development is known to compile with the following software:
- Menhir v.20230608
- Coq v8.12.0
- OCaml v4.10.0

## Instructions for compiling

We recommend using the `opam` package manager to set up a build environment. 
We have tested the building on **Linux** with the following shell commands. Note that we only target X86, so MacOS with M-series chips is unable to compiler the test cases.

    # Initialize opam (if you haven't used it before)
    opam init --bare
    
    # Create an "opam switch" dedicated to building the code
    opam switch create rcompcerto ocaml-base-compiler.4.10.0
    
    # Install the necessary packages
    opam repository add coq-released https://coq.inria.fr/opam/released
    opam install coq.8.12.0 menhir.20230608
    
    # Configure the current shell to use the newly created opam switch
    eval $(opam env)

In addition, our modifications rely on the Coqrel library (repo in [here](https://github.com/CertiKOS/coqrel)), which must be built first. To build Coqrel, proceed in the following way:

    % (cd coqrel && ./configure && make)

Finally, you can then build the compiler as follows:

    % ./configure x86_64-linux
	% make depend
    % make all
    # or make all -jn (where n is the number of cores)

## Run the compiler
The generated binary executable compiler is named `ccomp` in the main directory. A simple instruction of running the compiler is:
```
./ccomp test.rs -o test
```
Here `test.rs` is the source file written in our `Rustsurface` language and `test` is the name of the target executable file. After the compilation, the compiler would generate `rust_compile.log` which contains the pretty-printed rust intermediate programs generated during the compilation.

### Test the compiler

The test cases are in ['rustexamples/compiler_tests'](./rustexamples/compiler_tests/). To run the test cases of the compiler, use the following commands:

```
cd rustexamples/compiler_tests
# compile the test cases
make all 
# run the test
make test
```

The structure of the test cases is explained in [here](./rustexamples/compiler_tests/README.md).

## Structure of the source code

**Languages:**
* [Rustsurface.ml](./rustparser/Rustsurface.ml): the Rust surface language for users
* [Rustsyntax.v](./rustfrontend/Rustsyntax.v): the Rust surface language formalized in Coq
* [Rustlight.v](./rustfrontend/Rustlight.v): the source language of the verified compiler
  + [Rusttypes.v](./rustfrontend/Rusttypes.v): the type system
  + [Rustlightown.v](./rustfrontend/Rustlightown.v): the semantics of Rustlight
  + [InitDomain.v](./rustfrontend/InitDomain.v): contains the  components of the ownership semantics
* [RustIR.v](./rustfrontend/RustIR.v): the syntax of RustIR language
  + [RustIRown.v](./rustfrontend/RustIRown.v): RustIR semantics with ownership
  + [RustIRsem.v](./rustfrontend/RustIRsem.v): RustIR semantics without ownership
* [Clight.v](./cfrontend/Clight.v): the syntax and semantics of Clight (implemented by CompCert)

**Compilation:**
* Lexer and Parser: [RustsurfaceLexer.mll](./rustparser/RustsurfaceLexer.mll), [RustsurfaceParser.mly](./rustparser/RustsurfaceParser.mly), some code in [Rustsurface.ml](./rustparser/Rustsurface.ml) and [Rustlightgen.v](./rustfrontend/Rustlightgen.v)
* Lowering:
  + Implementation: [RustIRgen.v](./rustfrontend/RustIRgen.v)
  + Verification: [RustIRgenProof.v](./rustfrontend/RustIRgenProof.v)
* Drop Elaboration:
  + Implementation: the intermediate CFG of RustIR is defined in [RustIRcfg.v](./rustfrontend/RustIRcfg.v), the ownership analysis in [InitAnalysis.v](./rustfrontend/InitAnalysis.v), the main part of drop elaboration in [ElaborateDrop.v](./rustfrontend/ElaborateDrop.v)
  + Verification: some code in [InitAnalysis.v](./rustfrontend/InitAnalysis.v) and [RustIRcfg.v](./rustfrontend/RustIRcfg.v), and all of the [ElaborateDropProof.v](./rustfrontend/ElaborateDropProof.v)
* Clight Generation:
  + Implementation: [Clightgen.v](./rustfrontend/Clightgen.v)
  + Verification: [Clightgenspec.v](./rustfrontend/Clightgenspec.v) and [Clightgenproof.v](./rustfrontend/Clightgenproof.v)
* CompCertO backend: we utilize the CompCertO C compiler as the backend of our Rust compiler. The structure of the CompCertO is similar to the structure of CompCert. The version of CompCertO we use is based on the work of [Direct Refinement](https://github.com/SJTU-PLV/direct-refinement-popl24-artifac).

**Simulation Convention:**

The calling conventions adapted in the Rust interface: [RA.v](./driver/RA.v) and [CallConv.v](./driver/CallConvRust.v)

To see the statistics of the LOC of our development, use the following command:
```
bash eval.sh
```

