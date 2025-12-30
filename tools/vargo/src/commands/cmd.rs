use crate::cli::VargoCmd;
use crate::cli::VargoOptions;
use crate::commands::log_command;
use crate::commands::test_rust_min_stack;
use crate::VargoContext;
use crate::VargoResult;

pub fn cmd(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoCmd,
) -> VargoResult<()> {
    let mut cmd = std::process::Command::new("rustup");
    cmd.env("RUST_MIN_STACK", test_rust_min_stack())
        .arg("run")
        .arg(context.rust_toolchain.as_ref().expect("not in nextest"))
        .args(&vargo_cmd.command)
        .stderr(std::process::Stdio::inherit())
        .stdout(std::process::Stdio::inherit());

    log_command(&cmd, options.vargo_verbose);

    cmd.status()
        .map_err(|x| format!("vargo could not execute rustup ({})", x))
        .and_then(|x| {
            if x.success() {
                Ok(())
            } else {
                Err(format!("vargo returned status code {:?}", x.code()))
            }
        })
}
