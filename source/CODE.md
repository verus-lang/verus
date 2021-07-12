

# Top-Level Code Structure

- `tools`: Handy scripts for running Dust in various configurations.
- `builtin`: Defines verification-related Rust "functions" (e.g., `assert`,
  `decreases`), so that the Rust compiler will automatically create correctly
  typed internal representations.  These are handled in a custom manner inside
  of Dust.
- `builtin_macros`: Provides useful macros for the `builtin` library.  These
  are in a separate crate, since Rust requires procedural macros to be in their
  own crate.
- `vir`: The Verification Intermediate Representation (AIR) defines the
  internal subset of Rust that we currently support for verification purposes.
  Inside this directory, we also define a Statement-oriented Syntax Tree (SST),
  so that we can convert from Rust's (and VIR's) mutually recursive expression
  and statement ASTs into a form (the SST) in which expressions do not contain
  statements.
- `air`: The Assertion Intermediate Representation (AIR) is a simplified
  program language similar to [Boogie](https://github.com/boogie-org/boogie),
  designed to move us closer to Z3.
- `rust_verify`: The main Dust driver and logic.
- `rust_verify_test_macros`: Provides useful macros for creating unit tests for
  Dust.  Factored into a separate crate, due to the use of procedural macros.


# Overall Workflow

Given an input Rust program, Dust runs the usual Rust compiler to obtain its 
High-level Intermediate Representation (HIR) of the program.  It converts the HIR
into VIR, converts the VIR into SST form, converts the SST into AIR, and then sends queries to Z3 based on the AIR.

At present, we are not yet performing linearity checking, nor do we support compilation.

