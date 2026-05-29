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

use cargo_verus::{execute_plan, plan_execution};

fn main() -> Result<ExitCode> {
    let args: Vec<String> = env::args().collect();
    let plan = plan_execution(None, args.iter().map(String::as_str))?;
    let exit_code = execute_plan(&plan)?;
    Ok(exit_code)
}
