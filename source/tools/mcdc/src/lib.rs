//! MC/DC coverage for the Verus verifier crates: a source rewriter that records, for every
//! evaluation of a boolean decision, which atoms were evaluated and their values, and an
//! analyzer for the recorded evaluations, and mutant schemata switched at run time by a bitset.
//! See README.md.

pub mod analyze;
pub mod cli;
pub mod edit;
pub mod instrument;
pub mod mutate;

pub use instrument::manifest;

// Compiled here only to check that the embedded runtime builds; instrumented crates receive it as
// text through `instrument::RUNTIME`.
#[cfg(test)]
#[allow(dead_code)]
#[path = "runtime/mcdc_rt.rs"]
mod runtime;

// The mutant runtime, compiled here with test constants to check that it builds.
#[cfg(test)]
#[allow(dead_code)]
mod __mcdc {
    pub use super::runtime::rec;
}
#[cfg(test)]
#[allow(dead_code, unused)]
mod __mut {
    pub const BUILD_COMMIT: &str = "0000000000000000000000000000000000000000";
    pub const BUILD_COUNT: u32 = 0;
    pub const BUILD_DIGEST: u64 = 0;
    pub const BUILD_MUTANTS: bool = false;
    include!("runtime/mut_rt.rs");
}
