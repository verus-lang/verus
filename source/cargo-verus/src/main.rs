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

use crate::{
    cli::{CargoVerusCli, VerusSubcommand},
    subcommands::CargoRunConfig,
};

pub fn main() -> Result<ExitCode> {
    let normalized_args: Vec<_> = normalize_args(env::args()).collect();
    let parsed_cli =
        CargoVerusCli::parse_from(normalized_args.iter().cloned()).clap_trailing_args_hotfix();

    let cfg = match parsed_cli.command {
        VerusSubcommand::New(new_cmd) => {
            match (new_cmd.bin, new_cmd.lib) {
                (Some(name), None) => subcommands::create_new_project(&name, true)?,
                (None, Some(name)) => subcommands::create_new_project(&name, false)?,
                _ => unreachable!("clap enforces exactly one of --bin/--lib"),
            }
            return Ok(ExitCode::SUCCESS);
        }
        VerusSubcommand::Verify(options) => CargoRunConfig {
            subcommand: "build",
            options,
            compile_primary: false,
            verify_deps: true,
            warn_if_nothing_verified: true,
        },
        VerusSubcommand::Focus(options) => CargoRunConfig {
            subcommand: "build",
            options,
            compile_primary: false,
            verify_deps: false,
            warn_if_nothing_verified: true,
        },
        VerusSubcommand::Build(options) => CargoRunConfig {
            subcommand: "build",
            options,
            compile_primary: true,
            verify_deps: true,
            warn_if_nothing_verified: false,
        },
        VerusSubcommand::Check(options) => CargoRunConfig {
            subcommand: "check",
            options,
            compile_primary: false,
            verify_deps: true,
            warn_if_nothing_verified: true,
        },
    };

    subcommands::run_cargo(cfg)
}

fn normalize_args(args: impl Iterator<Item = String>) -> impl Iterator<Item = String> {
    args.enumerate().filter(|(i, arg)| *i != 1 || arg != "verus").map(|(_, arg)| arg)
}
