//! Construction of MIR from HIR.

// tidy-alphabetical-start
#![allow(rustc::diagnostic_outside_of_impl)]
#![allow(rustc::untranslatable_diagnostic)]
#![allow(dead_code)]
#![allow(noop_method_call)]
#![feature(assert_matches)]
#![feature(box_patterns)]
#![feature(if_let_guard)]
#![feature(let_chains)]
#![feature(try_blocks)]
#![feature(rustc_private)]
#![feature(never_type)]
#![warn(unreachable_pub)]
// tidy-alphabetical-end

extern crate rustc_middle;
extern crate rustc_data_structures;
extern crate rustc_ast;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_errors;
extern crate rustc_infer;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_session;
extern crate rustc_pattern_analysis;
extern crate rustc_macros;
extern crate rustc_lint;
extern crate rustc_arena;
extern crate rustc_fluent_macro;
extern crate rustc_apfloat;
extern crate either;
extern crate rustc_hir_typeck;

mod build;
mod check_unsafety;
mod errors;
pub mod lints;
mod thir;
pub mod verus;
pub mod upvar;
pub mod expr_use_visitor;

use rustc_middle::util::Providers;

rustc_fluent_macro::fluent_messages! { "../messages.ftl" }

pub fn verus_provide(providers: &mut Providers) {
    providers.thir_body = thir::cx::thir_body;
}

pub fn provide(providers: &mut Providers) {
    providers.check_match = thir::pattern::check_match;
    providers.lit_to_const = thir::constant::lit_to_const;
    providers.hooks.build_mir = build::mir_build;
    providers.closure_saved_names_of_captured_variables =
        build::closure_saved_names_of_captured_variables;
    providers.check_unsafety = check_unsafety::check_unsafety;
    providers.thir_body = thir::cx::thir_body;
    providers.hooks.thir_tree = thir::print::thir_tree;
    providers.hooks.thir_flat = thir::print::thir_flat;
}
