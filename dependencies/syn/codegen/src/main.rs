// This crate crawls the Syn source directory to find all structs and enums that
// form the Syn syntax tree.
//
// A machine-readable representation of the syntax tree is saved to syn.json in
// the repo root for other code generation tools to consume. The syn-codegen
// crate (https://docs.rs/syn-codegen/) provides the data structures for parsing
// and making use of syn.json from Rust code.
//
// Finally this crate generates the Visit, VisitMut, and Fold traits in Syn
// programmatically from the syntax tree description.

#![allow(
    clippy::format_push_string,
    clippy::items_after_statements,
    clippy::manual_let_else,
    clippy::match_like_matches_macro,
    clippy::module_name_repetitions,
    clippy::similar_names,
    clippy::too_many_lines,
    clippy::uninlined_format_args
)]

mod cfg;
mod clone;
mod css;
mod debug;
mod eq;
mod file;
mod fold;
mod full;
mod gen;
mod hash;
#[cfg(feature = "json")]
mod json;
mod lookup;
mod operand;
mod parse;
mod snapshot;
mod version;
mod visit;
mod visit_mut;
mod workspace_path;

fn main() -> anyhow::Result<()> {
    color_backtrace::install();
    let defs = parse::parse()?;
    clone::generate(&defs)?;
    debug::generate(&defs)?;
    eq::generate(&defs)?;
    hash::generate(&defs)?;
    #[cfg(feature = "json")]
    json::generate(&defs)?;
    fold::generate(&defs)?;
    visit::generate(&defs)?;
    visit_mut::generate(&defs)?;
    snapshot::generate(&defs)?;
    css::generate(&defs)?;
    Ok(())
}
