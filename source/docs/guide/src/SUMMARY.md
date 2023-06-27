# Summary

[Verus overview](./overview.md)

# Getting started

- [Getting started](./getting_started.md)

# Tutorial

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
- [Datatypes: struct and enum]() <!--- Andrea --->
    - [Defining datatypes]() <!--- Andrea --->
    - [Querying the discriminant (`#[is_variant]`)]() <!--- Andrea --->
    - [Proving properties of fields]() <!--- Andrea --->
- [Basic libraries](pervasive.md)
    - [Specification libraries: Seq, Set, Map](spec_lib.md)
    - [INTERLUDE: using assert and assume to develop proofs](develop_proofs.md)
    - [Executable libraries: Vec](exec_lib.md)
- [Quantifiers and spec closures](quants.md)
    - [forall and triggers](forall.md)
    - [Multiple variables, multiple triggers, matching loops](multitriggers.md)
    - [exists and choose](exists.md)
    - [Proofs about forall and exists](quantproofs.md)
    - [Example: binary search](binary_search.md)
    - [spec closures]() <!--- Chris --->
    - [broadcast_forall](broadcast_forall.md) <!--- Chris --->
- [Runtime `exec` Features]()
    - [Exec closures]()
- [SMT solving, automation, and where automation fails]() <!--- Chris --->
    - [What's decidable, what's undecidable, what's fast, what's slow]() <!--- Chris --->
    - [integers: nonlinear arithmetic and bit vectors]() <!--- Chris and Chanhee --->
    - [forall and exists: writing and using triggers, inline functions]() <!--- Chris --->
    - [recursive functions]() <!--- Chris --->
    - [extensional equality]() <!--- Chris --->
    - [libraries: incomplete axioms for Seq, Set, Map]() <!--- Chris --->
- [Improving SMT performance]() <!--- Chris --->
    - [Modules, hiding, opaque, reveal]() <!--- Chris --->
    - [Quantifier profiling](profiling.md) <!--- Bryan --->
    - [Hiding local proofs with `assert (...) by { ... }`](assert_by.md)
    - [Proof by computation](assert_by_compute.md) <!--- Bryan --->
    - [Spinning off separate SMT queries]()
    - [Breaking proofs into smaller pieces]() <!--- Chris --->
- [Mutation, references, and borrowing]() <!--- Andrea --->
    - [Requires and ensures with mutable references]() <!--- Andrea --->
    - [Assertions containing mutable references]() <!--- Andrea --->
- [Traits]()
- [Ghost and tracked variables]()
- [Low-level pointers and concurrency]()
- [Attributes and directives]()
    - [external and external_body]()
    - [inline]()
    - [opaque]()
    - [decreases_by]()
    - [broadcast_forall]()
    - [when_used_as_spec]()
- [Strings]() <!--- Andrea --->
    - [String library]() <!--- Andrea --->
    - [String literals]() <!--- Andrea --->
- [Macros]()
- [Tools and command-line options]()
    - [Proof Debugger]() <!--- Chanhee --->
    - [IDE Support](ide_support.md)
    - [Syntax Highlighting]()

- [Verification and Rust]()
  - [Why Rust?]()
  - [Supported Rust features]()
  - [Borrowing and lifetimes]()
  - [Mutable borrows]()
  - [Interior mutability](./interior_mutability.md)
  - [Alternatives to unsafe]()

- [Understanding the guarantees of a verified program]()
  - [Assumptions and trusted components]()
  - [Identifying a project's TCB]()
  - [Memory safety is conditional on verification](./memory-safety.md)

- [Project setup and development]()
  - [Working with crates]()
  - [Invoking Verus code from Rust]()
  - [Documentation with Rustdoc]()



# Reference

- [Supported and unsupported Rust features](./features.md)
- [Modes]()
  - [Function modes]()
  - [Variable modes]()
- [Spec expressions]()
  - [Rust subset]()
  - [Arithmetic]()
  - [Spec equality ==]()
  - [Extensional equality `=~=` and `=~~=`]()
  - [&&& and |||]()
  - [Chained inequalities]()
  - [Implication (`==>`, `<==`, and `<==>`)]()
  - [`forall`, `exists`]()
  - [`choose`]()
  - [Function expressions]()
  - [Trigger annotations]()
  - [The view function `@`](./reference-at-sign.md)
  - [Spec index operator `[]`](./reference-spec-index.md)
- [Proof features]()
  - [assert and assume]()
  - [assert ... by](./reference-assert-by.md)
  - [assert forall ... by](./reference-assert-forall-by.md)
  - [assert ... by(bit_vector)](./reference-assert-by-bit-vector.md)
  - [assert ... by(nonlinear_arith)]()
  - [assert ... by(compute) / by(compute_only)]()
  - [reveal]()
  - [fuel]()
- [Function specifications]()
  - [requires / ensures]()
  - [opens_invariants]()
  - [recommends]()
- [Loop specifications]()
  - [invariant]()
  - [ensures / invariant_ensures]()
- [Recursion and termination]()
  - [decreases ...]()
  - [decreases ... when ...]()
  - [decreases ... via ...]()
  - [Datatype ordering]()
  - [Cyclic definitions]()
- [Command line]()
  - [--arch-word-bits]()
