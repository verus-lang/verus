#![feature(rustc_private)]
#![feature(internal_output_capture)]
#![feature(box_patterns)]

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_lint;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_mir_build;
extern crate rustc_query_system;
extern crate rustc_resolve;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_trait_selection;
extern crate rustc_typeck;
extern crate smallvec;
extern crate regex;

mod attributes;
pub mod config;
pub mod context;
pub mod debugger;
pub mod def;
pub mod driver;
pub mod erase;
mod erase_rewrite;
pub mod file_loader;
mod lifetime;
pub mod rust_to_vir;
pub mod rust_to_vir_adts;
pub mod rust_to_vir_base;
pub mod rust_to_vir_expr;
pub mod rust_to_vir_func;
#[cfg(feature = "singular")]
pub mod singular;
pub mod typecheck;
pub mod util;
pub mod verifier;
