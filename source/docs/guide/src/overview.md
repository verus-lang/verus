# Verus overview

Verus is a tool for verifying the correctness of code written in Rust.
The main goal is to verify full functional correctness of low-level systems code,
building on ideas from existing verification frameworks like
[Dafny](https://github.com/dafny-lang/dafny),
[Boogie](https://github.com/boogie-org/boogie),
[F*](https://github.com/FStarLang/FStar),
[VCC](https://www.microsoft.com/en-us/research/project/vcc-a-verifier-for-concurrent-c/),
[Prusti](https://github.com/viperproject/prusti-dev),
[Creusot](https://github.com/xldenis/creusot),
[Aeneas](https://github.com/AeneasVerif/aeneas),
[Cogent](https://github.com/NICTA/cogent),
[Coq](https://coq.inria.fr/),
and
[Isabelle/HOL](https://isabelle.in.tum.de/overview.html).
Verification is static: Verus adds no run-time checks,
but instead uses computer-aided theorem proving to statically verify
that executable Rust code will always satisfy some user-provided specifications
for all possible executions of the code.

In more detail, Verus aims to:
- provide a pure mathematical language for expressing specifications
  (like Dafny, Creusot, F*, Coq, Isabelle/HOL)
- provide a mathematical language for expressing proofs
  (like Dafny, F*, Coq, Isabelle/HOL)
  based exclusively on classical logic (like Dafny)
- provide a low-level, imperative language for expressing executable code (like VCC),
  based on Rust (like Prusti, Creusot, and Aeneas)
- generate small, simple verification conditions that an SMT solver
  like [Z3](https://microsoft.github.io/z3guide/docs/logic/intro) can solve efficiently,
  based on the following principles:
  - keep the mathematical specification language close to
    the SMT solver's mathematical language (like Boogie)
  - use lightweight linear type checking, rather than SMT solving,
    to reason about memory and aliasing
    (like Cogent, Creusot, Aeneas, and [linear Dafny](https://github.com/secure-foundations/dafny/tree/betr/docs/Linear))

We believe that Rust is a good language for achieving these goals.
Rust combines low-level data manipulation, including manual memory management,
with an advanced, high-level, safe type system.
The type system includes features commonly found in higher-level verification languages,
including algebraic datatypes (with pattern matching), type classes, and first-class functions.
This makes it easy to express specifications and proofs in a natural way.
More importantly, Rust's type system includes sophisticated support for linear types and borrowing,
which takes care of much of the reasoning about memory and aliasing.
As a result, the remaining reasoning can ignore most memory and aliasing issues,
and treat the Rust code as if it were code written in a purely functional language,
which makes verification easier.

# This guide

This guide assumes that you're already somewhat familiar with the basics of Rust programming.
(If you're not, we recommend spending a couple hours on the [Learn Rust](https://www.rust-lang.org/learn) page.)
Familiarity with Rust is useful for Verus,
because Verus builds on Rust's syntax and Rust's type system to express specifications, proofs, and executable code.
In fact, there is no separate language for specifications and proofs;
instead, specifications and proofs are written in Rust syntax and type-checked with Rust's type checker.
So if you already know Rust, you'll have an easier time getting started with Verus.

Nevertheless, verifying the correctness of Rust code requires concepts and techniques
beyond just writing ordinary executable Rust code.
For example, Verus extends Rust's syntax (via macros) with new concepts for
writing specifications and proofs, such as `forall`, `exists`, `requires`, and `ensures`,
as well as introducing new types, like the mathematical integer types `int` and `nat`.
It can be challenging to prove that a Rust function satisfies its postconditions (its `ensures` clauses)
or that a call to a function satisfies the function's preconditions (its `requires` clauses).
Therefore, this guide's tutorial will walk you through the various concepts and techniques,
starting with relatively simple concepts (basic proofs about integers),
moving on to more moderately difficult challenges (inductive proofs about data structures),
and then on to more advanced topics such as proofs about arrays using `forall` and `exists`
and proofs about concurrent code.

All of these proofs are aided by an automated theorem prover
(specifically, [Z3](https://microsoft.github.io/z3guide/docs/logic/intro),
a satisfiability-modulo-theories solver, or "SMT solver" for short).
The SMT solver will often be able to prove simple properties,
such as basic properties about booleans or integer arithmetic,
with no additional help from the programmer.
However, more complex proofs often require effort from both the programmer and the SMT solver.
Therefore, this guide will also help you understand the strengths and limitations of SMT solving,
and give advice on how to fill in the parts of proofs that SMT solvers cannot handle automatically.
(For example, SMT solvers usually cannot automatically perform proofs by induction,
but you can write a proof by induction simply by writing a recursive Rust function whose `ensures`
clause expresses the induction hypothesis.)
