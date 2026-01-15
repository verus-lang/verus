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
    /// Run without accessing the network
    #[arg(long)]
    pub offline: bool,

    /// Use verbose output
    #[arg(short, long, action = clap::ArgAction::Count)]
    pub verbose: u8,

    /// Coloring
    #[arg(long, value_enum, default_value_t = CargoColor::Auto)]
    pub color: CargoColor,
}

#[derive(Clone, Debug, Args, PartialEq, Eq)]
pub struct BuildOptions {
    /// Build artifacts in release mode, with optimizations
    #[arg(short, long)]
    pub release: bool,

    /// Do not verify vstd when building
    #[arg(long)]
    pub vstd_no_verify: bool,

    /// Build vstd in `no-std` mode
    #[arg(long)]
    pub vstd_no_std: bool,

    /// Build vstd in `no-alloc` mode
    #[arg(long, requires = "vstd_no_std")]
    pub vstd_no_alloc: bool,

    /// Turn tracing on when building vstd
    #[arg(long)]
    pub vstd_trace: bool,

    /// Turn verbose logging on when building vstd
    #[arg(long)]
    pub vstd_log_all: bool,
}

#[derive(Clone, Debug, Args, PartialEq, Eq)]
pub struct FeaturesOptions {
    /// Do not activate the default features
    #[arg(long)]
    pub no_default_features: bool,

    /// Features to activate
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
pub struct VargoCheck {
    pub package: Option<String>,
    pub exclude: HashSet<String>,
    pub feature_options: FeaturesOptions,
    pub release: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VargoClean {
    pub package: Option<String>,
    pub release: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VargoCmd {
    pub command: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VargoFmt {
    pub package: Option<String>,
    pub exclude: HashSet<String>,
    pub rustfmt_args: Vec<String>,
    pub vstd_no_verusfmt: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VargoMetadata {
    pub feature_options: FeaturesOptions,
    pub format_version: String,
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
pub struct VargoTest {
    pub package: String,
    pub exclude: HashSet<String>,
    pub feature_options: FeaturesOptions,
    pub build_options: BuildOptions,
    pub test_args: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VargoUpdate {
    pub packages: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VargoSubcommand {
    /// Build Verus
    Build(VargoBuild),

    /// Analyze the current package and report errors, but don't build/verify
    Check(VargoCheck),

    /// Clean current build
    Clean(VargoClean),

    /// Run an arbitrary command in vargo's environment
    Cmd(VargoCmd),

    /// Run the formatter on the codebase
    Fmt(VargoFmt),

    /// Get resolved dependencies with concrete used versions in a machine-readable format
    Metadata(VargoMetadata),

    /// Run Verus tests using nextest
    NextestRun(VargoNextestRun),

    /// Run a binary package
    Run(VargoRun),

    /// Run Verus tests
    Test(VargoTest),

    /// Update packages
    Update(VargoUpdate),
}

impl VargoSubcommand {
    // if the subcommand supports a --release flag, return that
    // otherwise, return false
    pub fn release(&self) -> bool {
        match self {
            VargoSubcommand::Build(c) => c.build_options.release,
            VargoSubcommand::Check(c) => c.release,
            VargoSubcommand::Clean(c) => c.release,
            VargoSubcommand::Cmd(_) => false,
            VargoSubcommand::Fmt(_) => false,
            VargoSubcommand::Metadata(_) => false,
            VargoSubcommand::NextestRun(c) => c.build_options.release,
            VargoSubcommand::Run(c) => c.build_options.release,
            VargoSubcommand::Test(c) => c.build_options.release,
            VargoSubcommand::Update(_) => false,
        }
    }
}

#[derive(Clone, Debug, Parser)]
#[command(name = "vargo", arg_required_else_help = true, about)]
pub struct VargoParsedCli {
    #[command(flatten)]
    pub cargo_options: CargoOptions,

    /// Turn on `vargo`s verbose logging
    #[arg(long)]
    pub vargo_verbose: bool,

    /// Skip checking that the server's solver version is correct
    #[arg(long)]
    pub no_solver_version_check: bool,

    #[command(subcommand)]
    pub command: VargoParsedSubcommand,
}

#[derive(Clone, Debug, ValueEnum, PartialEq, Eq, Hash, Copy)]
pub enum VerusFeatures {
    RecordHistory,
    Singular,
}

impl std::fmt::Display for VerusFeatures {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VerusFeatures::RecordHistory => f.write_str("record-history"),
            VerusFeatures::Singular => f.write_str("singular"),
        }
    }
}

#[derive(Clone, Debug, ValueEnum)]
pub enum CargoColor {
    Always,
    Auto,
    Never,
}

impl std::fmt::Display for CargoColor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CargoColor::Always => f.write_str("always"),
            CargoColor::Auto => f.write_str("auto"),
            CargoColor::Never => f.write_str("never"),
        }
    }
}

#[derive(Clone, Debug, Subcommand)]
pub enum VargoParsedSubcommand {
    /// Build Verus
    Build {
        /// Package to build
        #[arg(short, long)]
        package: Option<String>,

        /// Exclude packages from building
        #[arg(long, action = clap::ArgAction::Append)]
        exclude: Vec<String>,

        #[command(flatten)]
        feature_options: FeaturesOptions,

        #[command(flatten)]
        build_options: BuildOptions,

        /// Arguments to pass on to verus (in case verification is needed)
        #[arg(last = true, allow_hyphen_values = true)]
        verus_args: Vec<String>,
    },

    /// Analyze the current package and report errors, but don't build/verify
    Check {
        /// Package to build
        #[arg(short, long)]
        package: Option<String>,

        /// Exclude packages from building
        #[arg(long, action = clap::ArgAction::Append)]
        exclude: Vec<String>,

        #[command(flatten)]
        feature_options: FeaturesOptions,

        /// Check artifacts in release mode
        release: bool,
    },

    /// Clean current build
    Clean {
        /// Package to clean
        #[arg(short, long)]
        package: Option<String>,

        /// Whether to clean debug or release artifacts
        #[arg(short, long)]
        release: bool,
    },

    /// Run an arbitrary command in vargo's environment
    Cmd {
        /// Command to run
        command: Vec<String>,
    },

    /// Run the formatter on the codebase
    Fmt {
        /// Package to format
        #[arg(short, long)]
        package: Option<String>,

        /// Exclude packages from formatting
        #[arg(long, action = clap::ArgAction::Append)]
        exclude: Vec<String>,

        /// Whether to skip formatting vstd
        #[arg(long)]
        vstd_no_verusfmt: bool,

        /// Options passed to rustfmt
        #[arg(last = true, allow_hyphen_values = true)]
        rustfmt_args: Vec<String>,
    },

    /// Get metadata from cargo
    Metadata {
        #[command(flatten)]
        feature_options: FeaturesOptions,

        /// Format version
        #[arg(long, default_value = "1")]
        format_version: String,
    },

    /// Run Verus tests with nextest
    Nextest {
        /// Build and run Verus tests
        #[command(subcommand)]
        command: NexTestCommand,
    },

    /// Run a binary package
    Run {
        /// Package to run
        #[arg(short, long)]
        package: Option<String>,

        #[command(flatten)]
        feature_options: FeaturesOptions,

        #[command(flatten)]
        build_options: BuildOptions,

        /// Arguments to pass on to verus (in case verification is needed)
        #[arg(last = true, allow_hyphen_values = true)]
        verus_args: Vec<String>,
    },

    /// Run Verus tests
    Test {
        /// Package to test
        #[arg(short, long)]
        package: String,

        /// Exclude packages from testing
        #[arg(long, action = clap::ArgAction::Append)]
        exclude: Vec<String>,

        #[command(flatten)]
        feature_options: FeaturesOptions,

        #[command(flatten)]
        build_options: BuildOptions,

        /// Other options (`cargo test --help` for more info)
        #[arg(allow_hyphen_values = true)]
        test_args: Vec<String>,
    },

    /// Update dependencies
    Update {
        /// Package to update
        packages: Vec<String>,
    },
}

#[derive(Clone, Debug, Subcommand)]
pub enum NexTestCommand {
    Run {
        /// Package to test
        #[arg(short, long)]
        package: String,

        /// Exclude packages from testing
        #[arg(long, action = clap::ArgAction::Append)]
        exclude: Vec<String>,

        #[command(flatten)]
        feature_options: FeaturesOptions,

        #[command(flatten)]
        build_options: BuildOptions,

        /// Other options (`cargo nextest run --help` for more info)
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
            VargoParsedSubcommand::Check {
                package,
                exclude,
                feature_options,
                release,
            } => VargoSubcommand::Check(VargoCheck {
                package,
                exclude: exclude.into_iter().collect(),
                feature_options,
                release,
            }),
            VargoParsedSubcommand::Clean { package, release } => {
                VargoSubcommand::Clean(VargoClean { package, release })
            }
            VargoParsedSubcommand::Cmd { command } => VargoSubcommand::Cmd(VargoCmd { command }),
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
            VargoParsedSubcommand::Metadata {
                feature_options,
                format_version,
            } => VargoSubcommand::Metadata(VargoMetadata {
                feature_options,
                format_version,
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
