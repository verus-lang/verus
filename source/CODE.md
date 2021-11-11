# Overall Workflow

Given an input Rust program, Verus runs the Rust compiler to obtain Rust's
High-level Intermediate Representation (HIR) of the program.  Verus then converts the HIR
into VIR's AST form, converts the VIR AST into VIR SST form,
converts the VIR SST into AIR, and then converts AIR into SMT queries for Z3.

# Top-Level Code Structure

The main directories are:
- `rust_verify`: The main Verus driver and logic.
- `vir`: The Verification Intermediate Representation (VIR) defines an
  abstract syntax tree (AST) for the
  internal subset of Rust that we currently support for verification.
  Inside this directory, we also define a Statement-oriented Syntax Tree (SST),
  so that we can convert from Rust's (and VIR's) mutually recursive expression
  and statement ASTs into a form (the SST) in which expressions do not contain
  statements.
- `air`: The Assertion Intermediate Representation (AIR) is an
  intermediate verification language based on assert and assume statements,
  along with mutable updates to local variables.

Additional files are found in:
- `rust_verify_test_macros`: Provides useful macros for creating unit tests for
  Verus.  Factored into a separate crate, due to the use of procedural macros.
- `builtin`: Defines verification-related Rust "functions" (e.g., `assert`,
  `decreases`), so that the Rust compiler will automatically create correctly
  typed internal representations.  These are handled in a custom manner inside
  of Verus.
- `builtin_macros`: Provides useful macros for the `builtin` library.  These
  are in a separate crate, since Rust requires procedural macros to be in their
  own crate.
- `tools`: Scripts for running Verus in various configurations.
