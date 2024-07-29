#![feature(rustc_private)]
#![feature(internal_output_capture)]
#![feature(box_patterns)]
#![feature(exit_status_error)]

// not using this as a dependency, only necessary to make the rlib for the compiler crates
// available to cargo
extern crate rustc_driver;

extern crate rustc_arena;
extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_error_messages;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_hir_analysis;
extern crate rustc_hir_pretty;
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
extern crate smallvec;

mod attributes;
mod buckets;
pub mod commands;
pub mod config;

#[path = "../../../tools/common/consts.rs"]
pub mod consts;

pub mod context;
pub mod debugger;
pub mod def;
pub mod driver;
pub mod erase;
mod expand_errors_driver;
pub mod file_loader;
mod fn_call_to_vir;
mod hir_hide_reveal_rewrite;
mod import_export;
pub mod lifetime;
mod lifetime_ast;
mod lifetime_emit;
mod lifetime_generate;
pub mod profiler;
pub mod reveal_hide;
mod rust_intrinsics_to_vir;
pub mod rust_to_vir;
pub mod rust_to_vir_adts;
pub mod rust_to_vir_base;
pub mod rust_to_vir_expr;
pub mod rust_to_vir_func;
pub mod rust_to_vir_global;
mod rust_to_vir_impl;
pub mod rust_to_vir_trait;
#[cfg(feature = "singular")]
pub mod singular;
mod spans;
mod trait_conflicts;
mod user_filter;
pub mod util;
pub mod verifier;
pub mod verus_items;
