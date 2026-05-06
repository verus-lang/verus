mod cli;
mod metadata;
mod plan;
mod subcommands;
pub mod test_utils;

pub const BIN_NAME: &str = "cargo-verus";

pub use plan::{ExecutionPlan, execute_plan, plan_execution};
