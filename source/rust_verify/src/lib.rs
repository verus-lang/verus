#![feature(rustc_private)]
#![feature(internal_output_capture)]
#![feature(or_patterns)]
#![feature(box_patterns)]

extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_lint;
extern crate rustc_middle;
extern crate rustc_mir_build;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_typeck;

pub mod config;
pub mod context;
pub mod erase;
pub mod model;
pub mod rust_to_vir;
pub mod rust_to_vir_adts;
pub mod rust_to_vir_base;
pub mod rust_to_vir_expr;
pub mod rust_to_vir_func;
pub mod typecheck;
pub mod util;
pub mod verifier;
