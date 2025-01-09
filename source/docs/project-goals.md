Verus is an experimental verification framework for Rust-like code.  The main goal is to verify full functional correctness of low-level systems code, building on ideas from existing verification frameworks like [Dafny](https://github.com/dafny-lang/dafny), [Boogie](https://github.com/boogie-org/boogie), [F*](https://github.com/FStarLang/FStar), [VCC](https://www.microsoft.com/en-us/research/project/vcc-a-verifier-for-concurrent-c/), [Prusti](https://github.com/viperproject/prusti-dev), [Cogent](https://github.com/NICTA/cogent), [Coq](https://coq.inria.fr/), and [Isabelle/HOL](https://isabelle.in.tum.de/overview.html).

Goals:
- provide a pure mathematical language for expressing specifications (like Dafny, F*, Coq, Isabelle/HOL)
- provide a mathematical language for expressing proofs (like Dafny, F*, Coq, Isabelle/HOL) based exclusively on classical logic (like Dafny)
- provide a low-level, imperative language for expressing executable code (like VCC), based on Rust (like Prusti)
- generate small, simple verification conditions that an SMT solver like [Z3](https://github.com/Z3Prover/z3) can solve efficiently, based on the following principles:
  - keep the mathematical specification language close to the SMT solver's mathematical language (like Boogie)
  - use lightweight linear type checking, rather than SMT solving, to reason about memory and aliasing (like Cogent and [linear Dafny](https://github.com/secure-foundations/dafny/tree/betr/docs/Linear))

We do not intend to ...
- ... support all Rust features and libraries (instead, we will focus a subset that is easy to verify)
- ... verify unsafe Rust code (instead, verification will rely on Rust's type safety, as ensured by Rust's type checker)
- ... verify the verifier itself
- ... verify the Rust/LLVM compilers
