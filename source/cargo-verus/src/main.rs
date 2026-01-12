//
// Copyright (c) 2024 The Verus Contributors
// Copyright (c) 2014-2024 The Rust Project Developers
//
// SPDX-License-Identifier: MIT
//
// Derived, with significant modification, from:
// https://github.com/rust-lang/rust-clippy/blob/master/src/main.rs
//
use std::env;
use std::process::ExitCode;

use anyhow::Result;
use clap::Parser;

mod cli;
mod metadata;
mod subcommands;
#[cfg(any(test, feature = "integration-tests"))]
pub mod test_utils;

use crate::cli::{CargoVerusCli, VerusSubcommand};

pub fn main() -> Result<ExitCode> {
    let normalized_args: Vec<_> = normalize_args(env::args()).collect();
    let parsed_cli =
        CargoVerusCli::parse_from(normalized_args.iter().cloned()).clap_trailing_args_hotfix();

    match parsed_cli.command {
        VerusSubcommand::New(new_cmd) => {
            match (new_cmd.bin, new_cmd.lib) {
                (Some(name), None) => subcommands::create_new_project(&name, true)?,
                (None, Some(name)) => subcommands::create_new_project(&name, false)?,
                _ => unreachable!("clap enforces exactly one of --bin/--lib"),
            }
            Ok(ExitCode::SUCCESS)
        }
        VerusSubcommand::Verify(cmd) => {
            let warn_if_nothing_verified = true;
            let verify_deps = true;
            subcommands::run_cargo(
                "build",
                verify_deps,
                &cmd.cargo_opts,
                &cmd.verus_args,
                warn_if_nothing_verified,
            )
        }
        VerusSubcommand::Focus(cmd) => {
            let warn_if_nothing_verified = true;
            let verify_deps = false;
            subcommands::run_cargo(
                "build",
                verify_deps,
                &cmd.cargo_opts,
                &cmd.verus_args,
                warn_if_nothing_verified,
            )
        }
        VerusSubcommand::Build(cmd) => {
            let warn_if_nothing_verified = false;
            let verify_deps = true;
            subcommands::run_cargo(
                "build",
                verify_deps,
                &cmd.cargo_opts,
                &cmd.verus_args,
                warn_if_nothing_verified,
            )
        }
        VerusSubcommand::Check(cmd) => {
            let warn_if_nothing_verified = true;
            let verify_deps = true;
            subcommands::run_cargo(
                "check",
                verify_deps,
                &cmd.cargo_opts,
                &cmd.verus_args,
                warn_if_nothing_verified,
            )
        }
    }
}

fn normalize_args(args: impl Iterator<Item = String>) -> impl Iterator<Item = String> {
    args.enumerate().filter(|(i, arg)| *i != 1 || arg != "verus").map(|(_, arg)| arg)
}
