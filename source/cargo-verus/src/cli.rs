use std::path::PathBuf;

use clap::{ArgAction, Args, Parser, Subcommand};

#[derive(Clone, Debug, Parser)]
#[command(
    name = "verus",
    bin_name = "cargo verus",
    arg_required_else_help = true,
    about,
    styles = clap_cargo::style::CLAP_STYLING,
)]
pub struct CargoVerusCli {
    #[command(subcommand)]
    pub command: VerusSubcommand,
}

#[derive(Clone, Debug, Subcommand)]
pub enum VerusSubcommand {
    /// Create a new Verus project
    New(NewCommand),

    /// Verify the current crate with 'cargo build'
    Verify(VerifyCommand),

    /// Verify only crate contents, without dependencies.
    Focus(VerifyCommand),

    /// Verify and build the current crate with 'cargo build'
    Build(VerifyCommand),

    /// Runs the 'cargo check' subcommand
    Check(VerifyCommand),
}

#[derive(Clone, Debug, Args)]
#[group(required = true, multiple = false)]
pub struct NewCommand {
    /// Create a binary
    #[arg(short, long)]
    pub bin: Option<String>,

    /// Create a library
    #[arg(short, long)]
    pub lib: Option<String>,
}

#[derive(Clone, Debug, Args)]
pub struct VerifyCommand {
    #[command(flatten)]
    pub cargo_opts: CargoOptions,

    #[arg(
        value_name = "ARGS",
        last = true,
        num_args = 0..,
        allow_hyphen_values = true,
        help = "Arguments passed to 'verus' after `--`"
    )]
    pub verus_args: Vec<String>,
}

#[derive(Clone, Debug, Args)]
pub struct CargoOptions {
    #[command(flatten)]
    pub manifest: clap_cargo::Manifest,

    #[command(flatten)]
    pub workspace: clap_cargo::Workspace,

    #[command(flatten)]
    pub features: clap_cargo::Features,

    #[arg(long)]
    pub frozen: bool,

    #[arg(long)]
    pub locked: bool,

    #[arg(long)]
    pub offline: bool,

    #[arg(long)]
    pub target_dir: Option<PathBuf>,

    #[arg(long, value_name = "CONFIG", action = ArgAction::Append)]
    pub config: Vec<String>,

    #[arg(short = 'Z', value_name = "FLAG", action = ArgAction::Append)]
    pub unstable_flags: Vec<String>,

    #[arg(
        value_name = "CARGO_OPTIONS",
        num_args = 0..,
        allow_hyphen_values = true,
        help = "Options forwarded to 'cargo build' or 'cargo check'"
    )]
    pub cargo_args: Vec<String>,
}

impl CargoVerusCli {
    pub fn clap_trailing_args_hotfix(mut self) -> Self {
        // NOTE: For context see this issue: https://github.com/clap-rs/clap/issues/6200
        match &mut self.command {
            VerusSubcommand::Verify(cmd)
            | VerusSubcommand::Focus(cmd)
            | VerusSubcommand::Build(cmd)
            | VerusSubcommand::Check(cmd) => {
                let arg_split_pos = cmd.cargo_opts.cargo_args.iter().position(|arg| arg == "--");
                if let Some(index) = arg_split_pos {
                    let (cargo_args, verus_args) = cmd.cargo_opts.cargo_args.split_at(index);
                    let cargo_args = cargo_args.to_owned();
                    let verus_args = verus_args[1..].to_owned();
                    cmd.cargo_opts.cargo_args = cargo_args;
                    cmd.verus_args = verus_args;
                }
            }
            VerusSubcommand::New(_) => {}
        }
        self
    }
}
