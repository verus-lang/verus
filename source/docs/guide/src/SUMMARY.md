# Summary

[Verus overview](./overview.md)

# Getting started

- [Getting started](./getting_started.md)

# Tutorial

- [Basic specifications]()
    - [assert, requires, ensures, ghost code](./requires_ensures.md)
    - [Specifications: expressions and operators]()
    - [Integers and arithmetic](./integers.md)
- [Executable code, proof code, specification code]()
    - [Modes: exec, proof, spec]()
    - [spec functions]()
    - [proof functions, proof blocks, assert-by]()
- [Recursion and loops]()
    - [Recursive functions, decreases, proofs by induction]()
    - [Loops and invariants]()
- [Datatypes: struct and enum]()
- [Basic libraries]()
    - [view and spec_index operations]()
    - [Mathematical libraries: Seq, Set, Map]()
    - [Executable libraries: Vec]()
- [Quantifiers and spec closures]()
    - [spec closures]()
    - [forall, exists, choose, triggers, assert-forall-by]()
    - [broadcast_forall]()
- [SMT solving, automation, and where automation fails]()
    - [What's decidable, what's undecidable, what's fast, what's slow]()
    - [forall and exists: writing and using triggers]()
    - [extensional equality]()
    - [integers: nonlinear arithmetic and bit vectors]()
    - [recursive functions]()
- [Troubleshooting SMT performance]()
    - [Modules, hiding, opaque, reveal]()
    - [Quantifier profiling]()
    - [assert-by]()
    - [Spinning off separate SMT queries]()
    - [Breaking proofs into smaller pieces]()
- [Mutation, references, and borrowing]()
- [Traits]()
- [Ghost and tracked variables]()
- [Low-level pointers and concurrency]()
- [Attributes]()
    - [external and external_body]()
    - [inline]()
- [Tools and command-line options]()
    - [Proof Debugger]()
    - [IDE Support]()
    - [Syntax Highlighting]()

- [Verification and Rust]()
  - [Why Rust?]()
  - [Supported Rust features]()
  - [Borrowing and lifetimes]()
  - [Mutable borrows]()
  - [Interior mutability]()
  - [Alternatives to unsafe]()

- [Understanding the guarantees of a verified program]()
  - [Assumptions and trusted components]()
  - [Identifying a project's TCB]()
  - [Memory safety is conditional on preconditions]()

- [Project setup and development]()
  - [Working with crates]()
  - [Invoking Verus code from Rust]()
  - [Documentation with Rustdoc]()



# Reference

- [Supported and unsupported features]()
- [Planned future work]()
