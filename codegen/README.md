# syn_codegen

This is an internal (not published on crates.io) crate which is used to generate
the files in the `gen/` directory of `syn`. It is used to ensure that the
implementations for `Fold`, `Visit`, and `VisitMut` remain in sync with the
actual AST.

To run this program, run `cargo run` in this directory, and the `gen/` folder
will be re-generated.

This program is slow, and is therefore not run when building `syn` as part of
the build script to save on compile time.
