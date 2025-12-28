use std::collections::HashSet;

use clap::Args;
use clap::Parser;
use clap::Subcommand;
use clap::ValueEnum;

#[derive(Clone, Debug)]
pub struct VargoCli {
    pub options: VargoOptions,
    pub command: VargoSubcommand,
}

#[derive(Clone, Debug)]
pub struct VargoOptions {
    pub cargo_options: CargoOptions,
    pub vargo_verbose: bool,
    pub solver_version_check: bool,
}

#[derive(Clone, Debug, Args)]
pub struct CargoOptions {
    #[arg(long)]
    pub offline: bool,

    #[arg(short, long, action = clap::ArgAction::Count)]
    pub verbose: u8,

    #[arg(long, value_enum, default_value_t = CargoColor::Auto)]
    pub color: CargoColor,
}

#[derive(Clone, Debug, Args, PartialEq, Eq)]
pub struct BuildOptions {
    #[arg(short, long)]
    pub release: bool,

    #[arg(long)]
    pub vstd_no_verify: bool,

    #[arg(long)]
    pub vstd_no_std: bool,

    #[arg(long, requires = "vstd_no_std")]
    pub vstd_no_alloc: bool,

    #[arg(long)]
    pub vstd_trace: bool,

    #[arg(long)]
    pub vstd_log_all: bool,
}

#[derive(Clone, Debug, Args, PartialEq, Eq)]
pub struct FeaturesOptions {
    #[arg(long)]
    pub no_default_features: bool,

    #[arg(short = 'F', long, action = clap::ArgAction::Append)]
    pub features: Vec<VerusFeatures>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VargoBuild {
    pub package: Option<String>,
    pub exclude: HashSet<String>,
    pub feature_options: FeaturesOptions,
    pub build_options: BuildOptions,
    pub verus_args: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VargoTest {
    pub package: String,
    pub exclude: HashSet<String>,
    pub feature_options: FeaturesOptions,
    pub build_options: BuildOptions,
    pub test_args: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VargoNextestRun {
    pub package: String,
    pub exclude: HashSet<String>,
    pub feature_options: FeaturesOptions,
    pub build_options: BuildOptions,
    pub nextest_args: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VargoRun {
    pub package: Option<String>,
    pub feature_options: FeaturesOptions,
    pub build_options: BuildOptions,
    pub verus_args: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VargoClean {
    pub package: Option<String>,
    pub release: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VargoMetadata {
    pub feature_options: FeaturesOptions,
    pub format_version: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VargoFmt {
    pub package: Option<String>,
    pub exclude: HashSet<String>,
    pub rustfmt_args: Vec<String>,
    pub vstd_no_verusfmt: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VargoCmd {
    pub args: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VargoUpdate {
    pub packages: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VargoSubcommand {
    /// Build Verus
    Build(VargoBuild),

    /// Run Verus tests
    Test(VargoTest),

    /// Run Verus tests using nextest
    NextestRun(VargoNextestRun),

    /// Run a binary package
    Run(VargoRun),

    /// Clean current build
    Clean(VargoClean),

    Metadata(VargoMetadata),

    /// Run the formatter on the codebase
    Fmt(VargoFmt),

    /// Run an arbitrary command in vargo's environment
    Cmd(VargoCmd),

    /// Update packages
    Update(VargoUpdate),
}

impl VargoSubcommand {
    // if the subcommnad supports a --release flag, return that
    // otherwise, return false
    pub fn release(&self) -> bool {
        match self {
            VargoSubcommand::Build(c) => c.build_options.release,
            VargoSubcommand::Test(c) => c.build_options.release,
            VargoSubcommand::NextestRun(c) => c.build_options.release,
            VargoSubcommand::Run(c) => c.build_options.release,
            VargoSubcommand::Clean(c) => c.release,
            VargoSubcommand::Metadata(_) => false,
            VargoSubcommand::Fmt(_) => false,
            VargoSubcommand::Cmd(_) => false,
            VargoSubcommand::Update(_) => false,
        }
    }
}

#[derive(Clone, Debug, Parser)]
#[command(name = "vargo", arg_required_else_help = true, about)]
pub struct VargoParsedCli {
    #[command(flatten)]
    pub cargo_options: CargoOptions,

    #[arg(long)]
    pub vargo_verbose: bool,

    #[arg(long)]
    pub no_solver_version_check: bool,

    #[command(subcommand)]
    pub command: VargoParsedSubcommand,
}

#[derive(Clone, Debug, ValueEnum, PartialEq, Eq, Hash, Copy)]
pub enum VerusFeatures {
    Singular,
    AxiomUsageInfo,
    RecordHistory,
}

impl std::fmt::Display for VerusFeatures {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VerusFeatures::Singular => f.write_str("singular"),
            VerusFeatures::AxiomUsageInfo => f.write_str("axiom-usage-info"),
            VerusFeatures::RecordHistory => f.write_str("record-history"),
        }
    }
}

#[derive(Clone, Debug, ValueEnum)]
pub enum CargoColor {
    Auto,
    Always,
    Never,
}

impl std::fmt::Display for CargoColor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CargoColor::Never => f.write_str("never"),
            CargoColor::Always => f.write_str("always"),
            CargoColor::Auto => f.write_str("auto"),
        }
    }
}

#[derive(Clone, Debug, Subcommand)]
pub enum VargoParsedSubcommand {
    /// Build Verus
    Build {
        #[arg(short, long)]
        package: Option<String>,

        #[arg(long, action = clap::ArgAction::Append)]
        exclude: Vec<String>,

        #[command(flatten)]
        feature_options: FeaturesOptions,

        #[command(flatten)]
        build_options: BuildOptions,

        #[arg(last = true, allow_hyphen_values = true)]
        verus_args: Vec<String>,
    },

    /// Run Verus tests
    Test {
        #[arg(short, long)]
        package: String,

        #[arg(long, action = clap::ArgAction::Append)]
        exclude: Vec<String>,

        #[command(flatten)]
        feature_options: FeaturesOptions,

        #[command(flatten)]
        build_options: BuildOptions,

        #[arg(allow_hyphen_values = true)]
        test_args: Vec<String>,
    },

    /// Run Verus tests with nextest
    Nextest {
        #[command(subcommand)]
        command: NexTestCommand,
    },

    /// Run a binary package
    Run {
        #[arg(short, long)]
        package: Option<String>,

        #[command(flatten)]
        feature_options: FeaturesOptions,

        #[command(flatten)]
        build_options: BuildOptions,

        #[arg(last = true, allow_hyphen_values = true)]
        verus_args: Vec<String>,
    },

    /// Clean current build
    Clean {
        #[arg(short, long)]
        package: Option<String>,

        #[arg(short, long)]
        release: bool,
    },

    /// Get metadata from cargo
    Metadata {
        #[command(flatten)]
        feature_options: FeaturesOptions,

        #[arg(long, default_value = "1")]
        format_version: String,
    },

    /// Run the formatter on the codebase
    Fmt {
        #[arg(short, long)]
        package: Option<String>,

        #[arg(long, action = clap::ArgAction::Append)]
        exclude: Vec<String>,

        #[arg(long)]
        vstd_no_verusfmt: bool,

        #[arg(last = true, allow_hyphen_values = true)]
        rustfmt_args: Vec<String>,
    },

    /// Run an arbitrary command in vargo's environment
    Cmd { args: Vec<String> },

    /// Update packages
    Update { packages: Vec<String> },
}

#[derive(Clone, Debug, Subcommand)]
pub enum NexTestCommand {
    Run {
        #[arg(short, long)]
        package: String,

        #[arg(long, action = clap::ArgAction::Append)]
        exclude: Vec<String>,

        #[command(flatten)]
        feature_options: FeaturesOptions,

        #[command(flatten)]
        build_options: BuildOptions,

        #[arg(allow_hyphen_values = true)]
        nextest_args: Vec<String>,
    },
}

impl From<VargoParsedSubcommand> for VargoSubcommand {
    fn from(value: VargoParsedSubcommand) -> Self {
        match value {
            VargoParsedSubcommand::Build {
                package,
                exclude,
                feature_options,
                build_options,
                verus_args,
            } => VargoSubcommand::Build(VargoBuild {
                package,
                exclude: exclude.into_iter().collect(),
                feature_options,
                build_options,
                verus_args,
            }),
            VargoParsedSubcommand::Test {
                package,
                exclude,
                feature_options,
                build_options,
                test_args,
            } => VargoSubcommand::Test(VargoTest {
                package,
                exclude: exclude.into_iter().collect(),
                feature_options,
                build_options,
                test_args,
            }),
            VargoParsedSubcommand::Nextest {
                command:
                    NexTestCommand::Run {
                        package,
                        exclude,
                        feature_options,
                        build_options,
                        nextest_args,
                    },
            } => VargoSubcommand::NextestRun(VargoNextestRun {
                package,
                exclude: exclude.into_iter().collect(),
                feature_options,
                build_options,
                nextest_args,
            }),
            VargoParsedSubcommand::Run {
                package,
                feature_options,
                build_options,
                verus_args,
            } => VargoSubcommand::Run(VargoRun {
                package,
                feature_options,
                build_options,
                verus_args,
            }),
            VargoParsedSubcommand::Clean { package, release } => {
                VargoSubcommand::Clean(VargoClean { package, release })
            }
            VargoParsedSubcommand::Metadata {
                feature_options,
                format_version,
            } => VargoSubcommand::Metadata(VargoMetadata {
                feature_options,
                format_version,
            }),
            VargoParsedSubcommand::Fmt {
                package,
                exclude,
                rustfmt_args,
                vstd_no_verusfmt,
            } => VargoSubcommand::Fmt(VargoFmt {
                package,
                exclude: exclude.into_iter().collect(),
                vstd_no_verusfmt,
                rustfmt_args,
            }),
            VargoParsedSubcommand::Cmd { args } => VargoSubcommand::Cmd(VargoCmd { args }),
            VargoParsedSubcommand::Update { packages } => {
                VargoSubcommand::Update(VargoUpdate { packages })
            }
        }
    }
}

impl From<VargoParsedCli> for VargoCli {
    fn from(value: VargoParsedCli) -> Self {
        VargoCli {
            options: VargoOptions {
                cargo_options: value.cargo_options,
                vargo_verbose: value.vargo_verbose,
                solver_version_check: !value.no_solver_version_check,
            },
            command: value.command.into(),
        }
    }
}
