// Vargo is a wrapper around cargo that sets up the environment for building
// Verus and collects build artifacts for libraries used by vstd and client
// code so that later compilation stages (building, verifying vstd and running tests)
// can use them. This is necessary because cargo only builds libraries in
// `target/debug` or `target/release` when they are the main build target, and
// not when they're a dependency of another target.

#[path = "../../common/consts.rs"]
mod consts;

use clap::Parser;

mod cli;
mod commands;
mod context;
mod macros;
mod smt_solver;
mod util;

use cli::VargoCli;
use cli::VargoParsedCli;
use cli::VargoSubcommand;

use context::VargoContext;
use macros::info;

// Add vargo's sources into the binary itself
// This allows vargo to check if its own source has changed, prompting the user to rebuild
pub const VARGO_SOURCE_FILES: &[(&str, &[u8])] = &[
    ("src/cli.rs", include_bytes!("cli.rs")),
    ("src/commands/build.rs", include_bytes!("commands/build.rs")),
    ("src/commands/check.rs", include_bytes!("commands/check.rs")),
    ("src/commands/clean.rs", include_bytes!("commands/clean.rs")),
    ("src/commands/cmd.rs", include_bytes!("commands/cmd.rs")),
    ("src/commands/fmt.rs", include_bytes!("commands/fmt.rs")),
    (
        "src/commands/metadata.rs",
        include_bytes!("commands/metadata.rs"),
    ),
    ("src/commands/mod.rs", include_bytes!("commands/mod.rs")),
    (
        "src/commands/nextest.rs",
        include_bytes!("commands/nextest.rs"),
    ),
    ("src/commands/run.rs", include_bytes!("commands/run.rs")),
    ("src/commands/test.rs", include_bytes!("commands/test.rs")),
    (
        "src/commands/update.rs",
        include_bytes!("commands/update.rs"),
    ),
    ("src/context.rs", include_bytes!("context.rs")),
    ("src/macros.rs", include_bytes!("macros.rs")),
    ("src/main.rs", include_bytes!("main.rs")),
    ("src/util.rs", include_bytes!("util.rs")),
    ("src/smt_solver.rs", include_bytes!("smt_solver.rs")),
];

pub static VARGO_NEST: std::sync::RwLock<u64> = std::sync::RwLock::new(0);
pub const VSTD_FILES: &[&str] = &["vstd.vir", "libvstd.rlib", ".vstd-fingerprint"];
pub const VERUS_ROOT_FILE: &str = "verus-root";

#[cfg(target_os = "macos")]
mod lib_exe_names {
    pub const LIB_PRE: &str = "lib";
    pub const LIB_DL: &str = "dylib";
    pub const EXE: &str = "";
}

#[cfg(target_os = "linux")]
mod lib_exe_names {
    pub const LIB_PRE: &str = "lib";
    pub const LIB_DL: &str = "so";
    pub const EXE: &str = "";
}

#[cfg(target_os = "windows")]
mod lib_exe_names {
    pub const LIB_PRE: &str = "";
    pub const LIB_DL: &str = "dll";
    pub const EXE: &str = ".exe";
}

fn main() {
    let cli: VargoCli = VargoParsedCli::parse().into();
    match run(cli) {
        Ok(()) => (),
        Err(err) => {
            use yansi::Paint;
            eprintln!("{} {}", "vargo error:".bold().red(), format!("{err}").red());
            std::process::exit(1);
        }
    }
}

pub fn set_vargo_env(cli: &VargoCli, context: &VargoContext) {
    if let Some(toolchain) = &context.rust_toolchain {
        std::env::set_var("VARGO_TOOLCHAIN", toolchain);
    }
    if let Some(version_info) = &context.verus_version {
        std::env::set_var("VARGO_BUILD_VERSION", &version_info.version);
        std::env::set_var("VARGO_BUILD_SHA", &version_info.sha);
    }
    std::env::set_var(
        "VARGO_BUILD_PROFILE",
        if cli.command.release() {
            "release"
        } else {
            "debug"
        },
    );
}

fn run(cli: VargoCli) -> anyhow::Result<()> {
    let context = VargoContext::construct(&cli)?;
    set_vargo_env(&cli, &context);

    match &cli.command {
        VargoSubcommand::Build(vargo_cmd) => commands::build(&cli.options, &context, vargo_cmd),
        VargoSubcommand::Check(vargo_cmd) => commands::check(&cli.options, &context, vargo_cmd),
        VargoSubcommand::Clean(vargo_cmd) => commands::clean(&cli.options, &context, vargo_cmd),
        VargoSubcommand::Cmd(vargo_cmd) => commands::cmd(&cli.options, &context, vargo_cmd),
        VargoSubcommand::Fmt(vargo_cmd) => commands::fmt(&cli.options, &context, vargo_cmd),
        VargoSubcommand::Metadata(vargo_cmd) => {
            commands::metadata(&cli.options, &context, vargo_cmd)
        }
        VargoSubcommand::NextestRun(vargo_cmd) => {
            commands::nextest_run(&cli.options, &context, vargo_cmd)
        }
        VargoSubcommand::Run(vargo_cmd) => commands::run(&cli.options, &context, vargo_cmd),
        VargoSubcommand::Test(vargo_cmd) => commands::test(&cli.options, &context, vargo_cmd),
        VargoSubcommand::Update(vargo_cmd) => commands::update(&cli.options, &context, vargo_cmd),
    }
}
