//
// Copyright (c) 2024 The Verus Contributors
// Copyright (c) 2014-2024 The Rust Project Developers
//
// SPDX-License-Identifier: MIT
//
// Derived, with significant modification, from:
// https://github.com/rust-lang/rust-clippy/blob/master/src/main.rs
//
use std::process::ExitCode;
use std::{env, process::Command};

use anyhow::{anyhow, bail, Context, Result};
use clap::Parser;
use colored::Colorize;

mod cli;
mod metadata;
mod subcommands;
#[cfg(any(test, feature = "integration-tests"))]
pub mod test_utils;

use crate::cli::{CargoVerusCli, VerusSubcommand};

pub fn main() -> Result<ExitCode> {
    let plan = make_exec_plan(env::args())?;

    match plan {
        ExecPlan::CreateNew { name, is_bin } => {
            subcommands::create_new_project(&name, is_bin)?;
            Ok(ExitCode::SUCCESS)
        }
        ExecPlan::RunVerus { mut command, warn_nothing_verified } => {
            let exit_status = command
                .spawn()
                .context("Failed to spawn cargo")?
                .wait()
                .context("Failed to wait for cargo")?;

            if warn_nothing_verified {
                eprint!(
                    "{}",
                    "\
        WARNING: You asked for verification, but cargo did not find any crates that opted into verification.
                 If this is unexpected, try adding this entry to your Cargo.toml file:
                    [package.metadata.verus]
                    verify = true
        "
                    .red(),
                );
            }

            match exit_status.code() {
                Some(code) => u8::try_from(code).map(From::from).map_err(|_| {
                    anyhow!("Command {command:?} terminated with an odd exit code: {code}")
                }),
                None => bail!("Command {command:?} was terminated by a signal: {exit_status}"),
            }
        }
    }
}

pub enum ExecPlan {
    CreateNew { name: String, is_bin: bool },
    RunVerus { command: Command, warn_nothing_verified: bool },
}

fn make_exec_plan(args: impl Iterator<Item = String>) -> Result<ExecPlan> {
    let normalized_args: Vec<_> = normalize_args(args).collect();
    let parsed_cli =
        CargoVerusCli::parse_from(normalized_args.iter().cloned()).clap_trailing_args_hotfix();

    let (options, subcommand, verify_deps, warn_if_nothing_verified) = match parsed_cli.command {
        VerusSubcommand::New(new_cmd) => match (new_cmd.bin, new_cmd.lib) {
            (Some(name), None) => return Ok(ExecPlan::CreateNew { name, is_bin: true }),
            (None, Some(name)) => return Ok(ExecPlan::CreateNew { name, is_bin: false }),
            _ => unreachable!("clap enforces exactly one of --bin/--lib"),
        },
        VerusSubcommand::Verify(options) => {
            let subcommand = "build";
            let verify_deps = true;
            let warn_if_nothing_verified = true;
            (options, subcommand, verify_deps, warn_if_nothing_verified)
        }
        VerusSubcommand::Focus(options) => {
            let subcommand = "build";
            let verify_deps = false;
            let warn_if_nothing_verified = true;
            (options, subcommand, verify_deps, warn_if_nothing_verified)
        }
        VerusSubcommand::Build(options) => {
            let subcommand = "build";
            let verify_deps = true;
            let warn_if_nothing_verified = false;
            (options, subcommand, verify_deps, warn_if_nothing_verified)
        }
        VerusSubcommand::Check(options) => {
            let subcommand = "check";
            let verify_deps = true;
            let warn_if_nothing_verified = true;
            (options, subcommand, verify_deps, warn_if_nothing_verified)
        }
    };

    let (command, warn_nothing_verified) = subcommands::make_verus_plan(
        subcommand,
        verify_deps,
        &options.cargo_opts,
        &options.verus_args,
        warn_if_nothing_verified,
    )?;

    Ok(ExecPlan::RunVerus { command, warn_nothing_verified })
}

fn normalize_args(args: impl Iterator<Item = String>) -> impl Iterator<Item = String> {
    args.enumerate().filter(|(i, arg)| *i != 1 || arg != "verus").map(|(_, arg)| arg)
}
