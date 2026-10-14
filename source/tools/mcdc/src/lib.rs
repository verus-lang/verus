//! MC/DC coverage for the Verus verifier crates: a source rewriter that records, for every
//! evaluation of a boolean decision, which atoms were evaluated and their values, and an
//! analyzer for the recorded evaluations. See README.md.

pub mod analyze;
pub mod cli;
pub mod edit;
pub mod instrument;

pub use instrument::manifest;

// Compiled here only to check that the embedded runtime builds; instrumented crates receive it as
// text through `instrument::RUNTIME`.
#[cfg(test)]
#[allow(dead_code)]
#[path = "runtime/mcdc_rt.rs"]
mod runtime;
