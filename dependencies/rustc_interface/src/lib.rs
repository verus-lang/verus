#![feature(rustc_private)]

#![feature(box_patterns)]
#![feature(decl_macro)]
#![feature(internal_output_capture)]
#![feature(thread_spawn_unchecked)]
#![feature(once_cell)]
#![feature(try_blocks)]
#![recursion_limit = "256"]
#![allow(rustc::potential_query_instability)]
#![deny(rustc::untranslatable_diagnostic)]
#![deny(rustc::diagnostic_outside_of_impl)]

extern crate rustc_ast;
extern crate rustc_ast_lowering;
extern crate rustc_ast_passes;
extern crate rustc_attr;
extern crate rustc_borrowck;
extern crate rustc_builtin_macros;
extern crate rustc_codegen_ssa;
extern crate rustc_codegen_llvm;
extern crate rustc_const_eval;
extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_expand;
extern crate rustc_hir;
extern crate rustc_hir_analysis;
extern crate rustc_hir_typeck;
extern crate rustc_incremental;
extern crate rustc_lint;
extern crate rustc_macros;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_mir_build;
extern crate rustc_mir_transform;
extern crate rustc_monomorphize;
extern crate rustc_passes;
extern crate rustc_parse;
extern crate rustc_plugin_impl;
extern crate rustc_privacy;
extern crate rustc_query_impl;
extern crate rustc_resolve;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_symbol_mangling;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_traits;
extern crate rustc_ty_utils;

#[macro_use]
extern crate tracing;

mod callbacks;
mod errors;
pub mod interface;
mod passes;
mod proc_macro_decls;
mod queries;
pub mod util;

pub use callbacks::setup_callbacks;
pub use interface::{run_compiler, Config};
pub use passes::{DEFAULT_EXTERN_QUERY_PROVIDERS, DEFAULT_QUERY_PROVIDERS};
pub use queries::Queries;

#[cfg(test)]
mod tests;
