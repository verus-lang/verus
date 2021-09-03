//! VIR (Verifier Intermediate Representation) is an abstract syntax that represents
//! the elements of Rust code relevant to verification.
//! Compared to the original Rust code, VIR focuses on values,
//! rather than on how values are stored in memory.
//! For example, Box, Rc, and Arc are irrelevant to VIR and are not present in VIR.
//! We rely on Rust for type checking and lifetime checking -- VIR does not
//! attempt to replicate these (although it does do "mode" checking to check correct
//! usage of the 3 modes: exec, proof, and spec).
//!
//! The vir crate defines both the abstract syntax and the transformations from
//! the abstract syntax into the AIR verification format, which is then
//! verified by the Z3 SMT solver:
//!
//! Rust-AST --> Rust-HIR --> VIR --> AIR --> Z3-SMT
//!
//! VIR actually consists of two distinct abstract syntax trees, VIR-AST and VIR-SST:
//!
//! Rust-AST --> Rust-HIR --> VIR-AST --> VIR-SST --> AIR --> Z3-SMT
//!
//! VIR-AST keeps the original tree structure of mutually nested Rust HIR expressions and statements.
//! (Note: we chose to translate Rust-HIR --> VIR-AST rather than Rust-MIR --> VIR-AST to preserve
//! this tree structure as much as possible.)
//! VIR-SST, on the other hand, disallows statements inside expressions and disallows side
//! effects inside expressions (though it otherwise allows arbitrarily complex nested expressions).
//! The generated AIR code closely follows the structure of the VIR-SST code.
//!
//! To ensure that VIR stays simple and easy to use, the vir crate does not depend on rustc.

#![feature(or_patterns)]

pub mod ast;
mod ast_to_sst;
pub mod ast_util;
mod ast_visitor;
pub mod context;
pub mod datatype_to_air;
pub mod def;
pub mod func_to_air;
pub mod headers;
pub mod model;
pub mod modes;
mod prelude;
mod recursion;
mod scc;
mod sst;
mod sst_to_air;
mod sst_vars;
mod sst_visitor;
mod triggers;
mod triggers_auto;
mod util;
pub mod well_formed;
