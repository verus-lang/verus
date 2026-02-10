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
    cli::{CargoOptions, CargoVerusCli, VerusSubcommand},
    subcommands::CargoRunConfig,
};

fn has_late_verus_arg(opts: &CargoOptions) -> bool {
    for arg in opts.cargo_args.iter() {
        if arg.starts_with("-Z") && arg.len() > 2 {
            eprintln!(
                "Break the command-line argument {0} into two, by using a space after -Z, so that Verus sees it.",
                arg
            );
            return true;
        }
    }
    for arg in opts.cargo_args.iter().skip(1) {
        if arg.starts_with("-p")
            || arg == "--package"
            || arg.starts_with("--package=")
            || arg == "--workspace"
            || arg == "--all"
            || arg == "--exclude"
            || arg.starts_with("--exclude=")
            || arg == "--manifest-path"
            || arg.starts_with("--manifest-path=")
            || arg == "--all-features"
            || arg == "--no-default-features"
            || arg == "--features"
            || arg.starts_with("--features=")
            || arg == "--frozen"
            || arg == "--locked"
            || arg == "--offline"
            || arg == "--config"
            || arg.starts_with("--config=")
            || arg.starts_with("-Z")
        {
            eprintln!(
                "The Verus-relevant command-line argument {0} can't follow the Verus-irrelevant argument {1} because that will cause the Verus-relevant argument to be ignored",
                arg, opts.cargo_args[0]
            );
            return true;
        }
    }

    false
}

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
        VerusSubcommand::Verify(options) => {
            if has_late_verus_arg(&options.cargo_opts) {
                return Ok(ExitCode::from(2));
            }
            CargoRunConfig {
                subcommand: "build",
                options,
                compile_primary: false,
                verify_deps: true,
                warn_if_nothing_verified: true,
            }
        }
        VerusSubcommand::Focus(options) => {
            if has_late_verus_arg(&options.cargo_opts) {
                return Ok(ExitCode::from(2));
            }
            CargoRunConfig {
                subcommand: "build",
                options,
                compile_primary: false,
                verify_deps: false,
                warn_if_nothing_verified: true,
            }
        }
        VerusSubcommand::Build(options) => {
            if has_late_verus_arg(&options.cargo_opts) {
                return Ok(ExitCode::from(2));
            }
            CargoRunConfig {
                subcommand: "build",
                options,
                compile_primary: true,
                verify_deps: true,
                warn_if_nothing_verified: false,
            }
        }
        VerusSubcommand::Check(options) => {
            if has_late_verus_arg(&options.cargo_opts) {
                return Ok(ExitCode::from(2));
            }
            CargoRunConfig {
                subcommand: "check",
                options,
                compile_primary: false,
                verify_deps: true,
                warn_if_nothing_verified: true,
            }
        }
    };

    subcommands::run_cargo(cfg)
}

fn normalize_args(args: impl Iterator<Item = String>) -> impl Iterator<Item = String> {
    args.enumerate().filter(|(i, arg)| *i != 1 || arg != "verus").map(|(_, arg)| arg)
}
