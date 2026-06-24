mod cli;
pub mod metadata;
mod plan;
mod subcommands;
pub mod test_utils;
mod toolchains;

pub const BIN_NAME: &str = "cargo-verus";

pub use plan::{ExecutionPlan, execute_plan, plan_execution};
