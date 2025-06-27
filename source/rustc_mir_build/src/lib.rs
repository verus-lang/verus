//! Construction of MIR from HIR.

// tidy-alphabetical-start
#![allow(rustc::diagnostic_outside_of_impl)]
#![allow(rustc::untranslatable_diagnostic)]
#![feature(assert_matches)]
#![feature(box_patterns)]
#![feature(if_let_guard)]
#![feature(try_blocks)]
#![feature(rustc_private)]
#![feature(never_type)]
// tidy-alphabetical-end

extern crate rustc_abi;
extern crate rustc_apfloat;
extern crate rustc_arena;
extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_errors;
extern crate rustc_fluent_macro;
extern crate rustc_hir;
extern crate rustc_hir_typeck;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_lint;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_pattern_analysis;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_trait_selection;

// The `builder` module used to be named `build`, but that was causing GitHub's
// "Go to file" feature to silently ignore all files in the module, probably
// because it assumes that "build" is a build-output directory. See #134365.
pub mod builder;
mod check_tail_calls;
mod check_unsafety;
mod errors;
pub mod thir;

#[path = "../../rustc_mir_build_additional_files/verus.rs"]
pub mod verus;

#[path = "../../rustc_hir_typeck/src/expr_use_visitor.rs"]
pub mod expr_use_visitor;

#[path = "../../rustc_hir_typeck/src/upvar.rs"]
pub mod upvar;

use rustc_middle::util::Providers;

rustc_fluent_macro::fluent_messages! { "../messages.ftl" }

pub fn verus_provide(providers: &mut Providers) {
    providers.thir_body = thir::cx::thir_body;
}

pub fn provide(providers: &mut Providers) {
    providers.check_match = thir::pattern::check_match;
    providers.lit_to_const = thir::constant::lit_to_const;
    providers.closure_saved_names_of_captured_variables =
        builder::closure_saved_names_of_captured_variables;
    providers.check_unsafety = check_unsafety::check_unsafety;
    providers.check_tail_calls = check_tail_calls::check_tail_calls;
    providers.thir_body = thir::cx::thir_body;
}
