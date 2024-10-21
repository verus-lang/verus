# Summary

[Verus overview](./overview.md)

# Getting started

- [Getting started](./getting_started.md)

# Tutorial: Fundamentals

- [Basic specifications](specs.md)
    - [assert, requires, ensures, ghost code](./requires_ensures.md)
    - [Expressions and operators for specifications](./operators.md)
    - [Integers and arithmetic](./integers.md)
    - [Equality](./equality.md)
- [Specification code, proof code, executable code](modes.md)
    - [spec functions](spec_functions.md)
    - [proof functions, proof blocks, assert-by](proof_functions.md)
    - [spec functions vs. proof functions, recommends](spec_vs_proof.md)
    - [Ghost code vs. exec code](ghost_vs_exec.md)
    - [const declarations](const.md)
- [Recursion and loops](recursion_loops.md)
    - [Recursive spec functions, decreases, fuel](recursion.md)
    - [Recursive exec and proof functions, proofs by induction](induction.md)
    - [Loops and invariants](while.md)
        - [Loops with break](break.md)
    - [Lexicographic decreases clauses and mutual recursion](lex_mutual.md)
- [Datatypes: struct and enum](datatypes.md)
    - [Struct](datatypes_struct.md)
    - [Enum](datatypes_enum.md)
- [Libraries](vstd.md)
    - [Specification libraries: Seq, Set, Map](spec_lib.md)
    - [Executable libraries: Vec](exec_lib.md)
- [Spec closures](spec_closures.md)

# Tutorial: Understanding the prover

- [Using assert and assume to develop proofs](develop_proofs.md)
- [Quantifiers](quants.md)
    - [forall and triggers](forall.md)
    - [Multiple variables, multiple triggers, matching loops](multitriggers.md)
    - [exists and choose](exists.md)
    - [Proofs about forall and exists](quantproofs.md)
    - [Example: binary search](binary_search.md)
    - [Ambient (`broadcast`) lemmas](broadcast_proof.md)
- [SMT solving, automation, and where automation fails](smt_failures.md)
    - [What's decidable, what's undecidable, what's fast, what's slow]() <!--- Chris --->
    - [Integers and nonlinear arithmetic](nonlinear.md)
    - [Bit vectors and bitwise operations](bitvec.md)
    - [forall and exists: writing and using triggers, inline functions]() <!--- Chris --->
    - [Recursive functions]() <!--- Chris --->
    - [Extensional equality](extensional_equality.md)
    - [Libraries: incomplete axioms for Seq, Set, Map]() <!--- Chris --->
- [Managing proof performance and why it's critical](smt_perf_overview.md)
    - [Measuring verification performance](performance.md)
    - [Quantifier profiling](profiling.md)
    - [Modules, hiding, opaque, reveal]() <!--- Chris --->
    - [Hiding local proofs with `assert (...) by { ... }`](assert_by.md)
    - [Structured proof by calculation](calc.md)
    - [Proof by computation](assert_by_compute.md)
    - [Spinning off separate SMT queries]()
    - [Breaking proofs into smaller pieces](breaking_proofs_into_pieces.md)
- [Checklist: what to do when proofs go wrong](checklist.md)

# Tutorial: Verification and Rust

- [Mutation, references, and borrowing]() <!--- Andrea --->
    - [Requires and ensures with mutable references]() <!--- Andrea --->
    - [Assertions containing mutable references]() <!--- Andrea --->
- [Traits]()
- [Higher-order executable functions](./higher-order-fns.md)
    - [Passing functions as values](./exec_funs_as_values.md)
    - [Closures](./exec_closures.md)
- [Ghost and tracked variables]()
- [Strings]() <!--- Andrea --->
    - [String library]() <!--- Andrea --->
    - [String literals]() <!--- Andrea --->
- [Macros]()

- [Unsafe code & complex ownership](./complex_ownership.md)
  - [Cells / interior mutability](./interior_mutability.md)
  - [Pointers](./pointers.md)
  - [Concurrency](concurrency.md)

- [Understanding the guarantees of a verified program](./guarantees.md)
  - [Assumptions and trusted components](./tcb.md)
  - [Memory safety is conditional on verification](./memory-safety.md)
  - [Calling verified code from unverified code](./call-from-unverified-code.md)

# Installation, configuration, and tooling

- [Installation and setup]()
  - [IDE Support](ide_support.md)
  - [Installing and configuring Singular](./install-singular.md)

- [Project setup and development]()
  - [Working with crates]()
  - [Invoking Verus code from Rust]()
  - [Documentation with Rustdoc](./verusdoc.md)

# Reference

- [Supported and unsupported Rust features](./features.md)
- [Verus syntax by example](syntax.md)
- [Modes]()
  - [Function modes]()
  - [Variable modes](./reference-var-modes.md)
- [Spec expressions](./spec-expressions.md)
  - [Rust subset](./spec-rust-subset.md)
  - [Operator Precedence](./spec-operator-precedence.md)
  - [Arithmetic](./spec-arithmetic.md)
  - [Bit operators](./spec-bit-ops.md)
  - [Coercion with `as`](./reference-as.md)
  - [Spec equality (`==`)](./spec-equality.md)
  - [Extensional equality (`=~=`, `=~~=`)](./ref-extensional-equality.md)
  - [Prefix and/or (&&& and |||)](./prefix-and-or.md)
  - [Chained operators](./reference-chained-op.md)
  - [Implication (`==>`, `<==`, and `<==>`)](./reference-implication.md)
  - [Quantifiers (`forall`, `exists`)](./spec-quantifiers.md)
  - [Such that (`choose`)](./spec-choose.md)
  - [Trigger annotations](./trigger-annotations.md)
  - [The view function `@`](./reference-at-sign.md)
  - [Spec index operator `[]`](./reference-spec-index.md)
  - [`decreases_to!`](./reference-decreases-to.md)
- [Proof features]()
  - [assert and assume]()
  - [assert ... by](./reference-assert-by.md)
  - [assert forall ... by](./reference-assert-forall-by.md)
  - [assert ... by(bit_vector)](./reference-assert-by-bit-vector.md)
  - [assert ... by(nonlinear_arith)](./reference-assert-by-nonlinear.md)
  - [assert ... by(compute) / by(compute_only)](./reference-assert-by-compute.md)
  - [reveal, reveal_with_fuel, hide](./reference-reveal-hide.md)
- [Function specifications]()
  - [requires / ensures]()
  - [opens_invariants](./reference-opens-invariants.md)
  - [no_unwind](./reference-unwind-sig.md)
  - [Traits and signature inheritance](./reference-signature-inheritance.md)
  - [Specifications on FnOnce](./reference-signature-fnonce.md)
  - [recommends]()
- [Loop specifications]()
  - [invariant]()
  - [invariant_except_break / ensures]()
- [Recursion and termination]()
  - [decreases ... when ... via ...](./reference-decreases.md)
  - [Datatype ordering]()
  - [Cyclic definitions]()
- [Type invariants](./reference-type-invariants.md)
- [Attribute list](./reference-attributes.md)
- [The "global" directive](./reference-global.md)
- [Misc. Rust features]()
  - [Statics](./static.md)
  - [char](./char.md)
  - [Unions](./reference-unions.md)
  - [Pointers and cells](./reference-pointers-cells.md)
- [Command line]()
  - [--record](./reference-flag-record.md)
- [Planned future work]()
