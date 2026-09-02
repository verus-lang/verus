use std::path::PathBuf;

use anyhow::{Result, anyhow};
use clap::{ArgAction, Args, Parser, Subcommand, ValueEnum};

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

    /// Format Verus and Rust source files
    Fmt(FmtCommand),

    /// Manage Verus toolchains
    Toolchain(ToolchainCommand),

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
pub struct ToolchainCommand {
    #[command(subcommand)]
    pub command: ToolchainSubcommand,
}

#[derive(Clone, Debug, Subcommand)]
pub enum ToolchainSubcommand {
    /// List known toolchains
    List,
}

#[derive(Clone, Debug, Args)]
#[group(skip)]
pub struct NewCommand {
    #[command(flatten)]
    pub project_kind: NewProjectKind,

    /// Override the version reported by `verus --version`
    #[arg(long)]
    pub override_verus_version: Option<String>,
}

#[derive(Clone, Debug, Args)]
#[group(required = true, multiple = false)]
pub struct NewProjectKind {
    /// Create a binary
    #[arg(short, long)]
    pub bin: Option<String>,

    /// Create a library
    #[arg(short, long)]
    pub lib: Option<String>,
}

#[derive(Clone, Debug, Args)]
pub struct FmtCommand {
    /// Check whether formatting is needed without modifying files
    #[arg(long)]
    pub check: bool,

    /// Increase verbosity (use -vv for more output)
    #[arg(short, long, action = ArgAction::Count)]
    pub verbosity: u8,

    #[command(flatten)]
    pub cargo_opts: CargoOptions,

    #[arg(last = true, num_args = 0.., allow_hyphen_values = true)]
    pub verusfmt_args: Vec<String>,
}

#[derive(Clone, Debug, Args)]
pub struct VerifyCommand {
    #[command(flatten)]
    pub cargo_opts: CargoOptions,

    /// Increase verbosity (use -vv for more output)
    #[arg(short, long, action = ArgAction::Count)]
    pub verbosity: u8,

    /// Override the version reported by `verus --version`
    #[arg(long)]
    pub override_verus_version: Option<String>,

    /// Check toolchain components, e.g. version compatibility of verus and vstd.
    #[arg(long)]
    pub check_toolchain: bool,

    /// Crates to receive forwarded Verus args
    #[arg(
        long,
        value_name = "SELECTOR",
        help = "\
Crates to receive forwarded Verus args. Defaults to `all`, except in `focus` mode where it defaults to `roots`. Use `deps` to pass args ONLY to dependencies and NOT to roots.\n",
        long_help = "\
Crates to receive forwarded Verus args.

Defaults to `all`, except in `focus` mode where it defaults to `roots`.
Use `deps` to pass args ONLY to dependencies and NOT to roots."
    )]
    pub fwd_verus_args_to: Option<VerusArgFwdSelector>,

    #[arg(
        value_name = "ARGS",
        last = true,
        num_args = 0..,
        allow_hyphen_values = true,
        help = "Arguments passed to 'verus' after `--`"
    )]
    pub verus_args: Vec<String>,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
pub enum VerusArgFwdSelector {
    All,
    Roots,
    Deps,
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
    pub release: bool,

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

fn has_flag_arg_without_space(opts: &CargoOptions) -> bool {
    for arg in opts.cargo_args.iter() {
        if arg.starts_with("-Z") && arg.len() > 2 {
            eprintln!(
                "Split the command-line argument {0} into two by using a space after -Z (i.e., use -Z {1}) so that cargo verus can correctly parse and forward the flag.",
                arg,
                &arg[2..],
            );
            return true;
        }
    }

    false
}

fn has_late_verus_arg(opts: &CargoOptions) -> bool {
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
            || arg == "--release"
            || arg == "--target-dir"
            || arg.starts_with("--target-dir=")
            || arg == "--config"
            || arg.starts_with("--config=")
            || arg.starts_with("-Z")
        {
            eprintln!(
                "The Verus-relevant command-line argument {0} can't follow the Verus-irrelevant argument {1} because that will cause the Verus-relevant argument to be ignored. To fix this, place Verus-relevant cargo options (like --package, --features, --manifest-path) before any Verus-irrelevant ones.",
                arg, opts.cargo_args[0]
            );
            return true;
        }
    }

    false
}

impl CargoVerusCli {
    pub fn from_args<'a>(args: impl Iterator<Item = &'a str>) -> Result<Self> {
        let normalized_args = normalize_args(args);
        let mut parsed_cli = CargoVerusCli::parse_from(normalized_args).clap_trailing_args_hotfix();

        if parsed_cli.has_inadvisable_verus_arg() {
            eprintln!("Args forwarded to Cargo must precede args forwarded to Verus");
            return Err(anyhow!("Args forwarded to Cargo must precede args forwarded to Verus"));
        }

        if let partial_selectors = parsed_cli.filter_partial_verification_selectors()
            && !partial_selectors.is_empty()
            && !matches!(parsed_cli.command, VerusSubcommand::Focus(_))
        {
            for arg in partial_selectors {
                eprintln!("partial verification selector: `{arg}`");
            }
            return Err(anyhow!("Partial verification must use `cargo verus focus`"));
        }

        parsed_cli.set_fwd_verus_args_to_default();

        Ok(parsed_cli)
    }

    fn set_fwd_verus_args_to_default(&mut self) {
        match &mut self.command {
            VerusSubcommand::New(_) | VerusSubcommand::Fmt(_) | VerusSubcommand::Toolchain(_) => {}
            VerusSubcommand::Verify(cmd)
            | VerusSubcommand::Build(cmd)
            | VerusSubcommand::Check(cmd) => {
                if cmd.fwd_verus_args_to.is_none() {
                    cmd.fwd_verus_args_to = Some(VerusArgFwdSelector::All)
                }
            }
            VerusSubcommand::Focus(cmd) => {
                if cmd.fwd_verus_args_to.is_none() {
                    cmd.fwd_verus_args_to = Some(VerusArgFwdSelector::Roots)
                }
            }
        }
    }

    fn clap_trailing_args_hotfix(mut self) -> Self {
        // NOTE: For context see this issue: https://github.com/clap-rs/clap/issues/6200
        let Some(cmd) = self.get_verify_cmd_mut() else { return self };
        let arg_split_pos = cmd.cargo_opts.cargo_args.iter().position(|arg| arg == "--");
        if let Some(index) = arg_split_pos {
            let (cargo_args, verus_args) = cmd.cargo_opts.cargo_args.split_at(index);
            let cargo_args = cargo_args.to_owned();
            let verus_args = verus_args[1..].to_owned();
            cmd.cargo_opts.cargo_args = cargo_args;
            cmd.verus_args = verus_args;
        }
        self
    }

    fn has_inadvisable_verus_arg(&self) -> bool {
        let Some(cmd) = self.get_verify_cmd() else { return false };
        has_flag_arg_without_space(&cmd.cargo_opts) || has_late_verus_arg(&cmd.cargo_opts)
    }

    fn filter_partial_verification_selectors(&self) -> Vec<&str> {
        let Some(cmd) = self.get_verify_cmd() else {
            return vec![];
        };
        cmd.verus_args
            .iter()
            .map(String::as_str)
            .filter(|arg| is_partial_verification_selector(arg))
            .collect()
    }

    fn get_verify_cmd(&self) -> Option<&VerifyCommand> {
        match &self.command {
            VerusSubcommand::Verify(cmd)
            | VerusSubcommand::Focus(cmd)
            | VerusSubcommand::Build(cmd)
            | VerusSubcommand::Check(cmd) => Some(cmd),
            VerusSubcommand::New(_) | VerusSubcommand::Fmt(_) | VerusSubcommand::Toolchain(_) => {
                None
            }
        }
    }

    fn get_verify_cmd_mut(&mut self) -> Option<&mut VerifyCommand> {
        match &mut self.command {
            VerusSubcommand::Verify(cmd)
            | VerusSubcommand::Focus(cmd)
            | VerusSubcommand::Build(cmd)
            | VerusSubcommand::Check(cmd) => Some(cmd),
            VerusSubcommand::New(_) | VerusSubcommand::Fmt(_) | VerusSubcommand::Toolchain(_) => {
                None
            }
        }
    }
}

fn is_partial_verification_selector(arg: &str) -> bool {
    matches!(
        arg,
        "--verify-function" | "--verify-module" | "--verify-only-module" | "--verify-root"
    ) || arg.starts_with("--verify-function=")
        || arg.starts_with("--verify-module=")
        || arg.starts_with("--verify-only-module=")
}

fn normalize_args<'a>(args: impl Iterator<Item = &'a str>) -> impl Iterator<Item = &'a str> {
    args.enumerate().filter(|(i, arg)| *i != 1 || *arg != "verus").map(|(_, arg)| arg)
}
