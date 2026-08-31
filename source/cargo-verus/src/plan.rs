use std::path::{Path, PathBuf};
use std::process::ExitCode;

use anyhow::Result;

use crate::{
    cli::{CargoVerusCli, ToolchainSubcommand, VerusSubcommand},
    subcommands::{self, CargoRunPlan, NewCreationPlan, VerusConfig},
};

pub enum ExecutionPlan {
    CreateNew(NewCreationPlan),
    ListToolchains,
    RunCargo(CargoRunPlan),
}

pub fn execute_plan(plan: &ExecutionPlan) -> Result<ExitCode> {
    use ExecutionPlan::*;

    match plan {
        CreateNew(creation_plan) => subcommands::create_new_project(creation_plan),
        ListToolchains => subcommands::list_toolchains(),
        RunCargo(cargo_run_plan) => subcommands::run_cargo(cargo_run_plan),
    }
}

pub fn plan_execution<'a>(
    current_dir: impl AsRef<Path>,
    args: impl IntoIterator<Item = &'a str>,
) -> Result<ExecutionPlan> {
    let parsed_cli = CargoVerusCli::from_args(args.into_iter())?;

    let current_dir: PathBuf = current_dir.as_ref().to_owned();

    let cfg = match parsed_cli.command {
        VerusSubcommand::New(new_cmd) => {
            let vstd_dependency = subcommands::plan_new_project_vstd_dependency()?;
            let creation_plan = match (new_cmd.bin, new_cmd.lib) {
                (Some(name), None) => {
                    NewCreationPlan { current_dir, name, is_bin: true, vstd_dependency }
                }
                (None, Some(name)) => {
                    NewCreationPlan { current_dir, name, is_bin: false, vstd_dependency }
                }
                _ => unreachable!("clap enforces exactly one of --bin/--lib"),
            };
            return Ok(ExecutionPlan::CreateNew(creation_plan));
        }
        VerusSubcommand::Toolchain(toolchain_cmd) => match toolchain_cmd.command {
            ToolchainSubcommand::List => return Ok(ExecutionPlan::ListToolchains),
        },
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
