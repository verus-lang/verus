use std::env;
use std::path::Path;
use std::process::ExitCode;

use anyhow::Result;

use crate::{
    cli::{CargoVerusCli, VerusSubcommand},
    subcommands::{self, CargoRunPlan, NewCreationPlan, VerusConfig},
};

pub enum ExecutionPlan {
    CreateNew(NewCreationPlan),
    RunCargo(CargoRunPlan),
}

pub fn execute_plan(plan: &ExecutionPlan) -> Result<ExitCode> {
    use ExecutionPlan::*;

    match plan {
        CreateNew(creation_plan) => subcommands::create_new_project(creation_plan),
        RunCargo(cargo_run_plan) => subcommands::run_cargo(cargo_run_plan),
    }
}

pub fn plan_execution<'a>(
    current_dir: Option<&Path>,
    args: impl IntoIterator<Item = &'a str>,
) -> Result<ExecutionPlan> {
    let parsed_cli = CargoVerusCli::from_args(args.into_iter())?;

    let current_dir =
        if let Some(path) = current_dir { path.to_owned() } else { env::current_dir()? };

    let cfg = match parsed_cli.command {
        VerusSubcommand::New(new_cmd) => {
            let creation_plan = match (new_cmd.bin, new_cmd.lib) {
                (Some(name), None) => NewCreationPlan { current_dir, name, is_bin: true },
                (None, Some(name)) => NewCreationPlan { current_dir, name, is_bin: false },
                _ => unreachable!("clap enforces exactly one of --bin/--lib"),
            };
            return Ok(ExecutionPlan::CreateNew(creation_plan));
        }
        VerusSubcommand::Verify(options) => VerusConfig {
            current_dir,
            subcommand: "check",
            options,
            compile_primary: false,
            verify_deps: true,
            warn_if_nothing_verified: true,
        },
        VerusSubcommand::Focus(options) => VerusConfig {
            current_dir,
            subcommand: "check",
            options,
            compile_primary: false,
            verify_deps: false,
            warn_if_nothing_verified: true,
        },
        VerusSubcommand::Build(options) => VerusConfig {
            current_dir,
            subcommand: "build",
            options,
            compile_primary: true,
            verify_deps: true,
            warn_if_nothing_verified: false,
        },
        VerusSubcommand::Check(options) => VerusConfig {
            current_dir,
            subcommand: "check",
            options,
            compile_primary: false,
            verify_deps: true,
            warn_if_nothing_verified: true,
        },
    };

    let cargo_run_plan = subcommands::plan_cargo_run(cfg)?;

    Ok(ExecutionPlan::RunCargo(cargo_run_plan))
}
