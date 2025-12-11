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
