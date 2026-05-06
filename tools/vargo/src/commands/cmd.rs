use anyhow::Context;

use crate::cli::VargoCmd;
use crate::cli::VargoOptions;
use crate::commands::log_command;
use crate::commands::test_rust_min_stack;
use crate::VargoContext;

pub fn cmd(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoCmd,
) -> anyhow::Result<()> {
    let mut cmd = std::process::Command::new("rustup");
    cmd.env("RUST_MIN_STACK", test_rust_min_stack())
        .arg("run")
        .arg(context.rust_toolchain.as_ref().expect("not in nextest"))
        .args(&vargo_cmd.command)
        .stderr(std::process::Stdio::inherit())
        .stdout(std::process::Stdio::inherit());

    log_command(&cmd, options.vargo_verbose);

    cmd.status()
        .context("vargo could not execute rustup")
        .and_then(|status| {
            if status.success() {
                Ok(())
            } else if let Some(code) = status.code() {
                Err(anyhow::anyhow!("`rustup run` returned status code {code}"))
            } else {
                Err(anyhow::anyhow!("`rustup run` was terminated by a signal"))
            }
        })
}
