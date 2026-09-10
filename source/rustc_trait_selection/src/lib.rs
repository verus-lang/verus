//! This crate defines the trait resolution method.
//!
//! - **Traits.** Trait resolution is implemented in the `traits` module.
//!
//! For more information about how rustc works, see the [rustc-dev-guide].
//!
//! [rustc-dev-guide]: https://rustc-dev-guide.rust-lang.org/
//!
//! # Note
//!
//! This API is completely unstable and subject to change.

// tidy-alphabetical-start
#![feature(associated_type_defaults)]
#![feature(default_field_values)]
#![feature(deref_patterns)]
#![feature(hash_set_entry)]
#![feature(iter_intersperse)]
#![feature(iterator_try_reduce)]
#![feature(never_type)]
#![feature(option_into_flat_iter)]
#![feature(try_blocks)]
#![feature(unwrap_infallible)]
#![feature(yeet_expr)]
#![recursion_limit = "512"] // For rustdoc
#![feature(rustc_private)]
// tidy-alphabetical-end

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_infer;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_next_trait_solver;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_transmute;
extern crate thin_vec;
extern crate smallvec;


pub mod diagnostics;
pub mod error_reporting;
pub mod infer;
pub mod opaque_types;
pub mod regions;
pub mod solve;
pub mod traits;
