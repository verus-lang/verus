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
    - [broadcast_forall]() <!--- Chris --->
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
    - [assert-by]() <!--- Chris --->
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
    - [IDE Support]() <!--- Chanhee --->
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

- [Verus syntax reference]()
- [Supported and unsupported features](./features.md)
- [Planned future work]()
