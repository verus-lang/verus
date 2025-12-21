use clap::Args;
use clap::Parser;
use clap::Subcommand;
use clap::ValueEnum;

#[derive(Clone, Debug)]
pub struct VargoCli {
    pub cargo_options: CargoOptions,
    pub vargo_verbose: bool,
    pub vstd_no_verify: bool,
    pub vstd_no_alloc: bool,
    pub vstd_trace: bool,
    pub solver_version_check: bool,
    pub vstd_log_all: bool,
    pub vstd_no_verusfmt: bool,
    pub release: bool,
    pub package: Option<String>,
    pub exclude: Vec<String>,
    pub features: Vec<VerusFeatures>,
    pub command: VargoSubcommand,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VargoSubcommand {
    /// Build Verus
    Build {
        verus_args: Vec<String>,
    },

    /// Run Verus tests
    Test {
        nextest: bool,
        verus_args: Vec<String>,
    },

    /// Run a binary package
    Run {
        cmd_args: Vec<String>,
    },

    /// Clean current build
    Clean,

    // TODO: figure out what this is
    Metadata,

    /// Run the formatter on the codebase
    Fmt,

    /// Run an arbitrary command
    // TODO: why do we need this at all???
    Cmd {
        args: Vec<String>,
    },

    /// Do something?
    // TODO: this is again weird
    Update,
}

#[derive(Clone, Debug, Parser)]
#[command(name = "vargo", arg_required_else_help = true, about)]
pub struct VargoParsedCli {
    #[command(flatten)]
    pub cargo_options: CargoOptions,

    #[arg(long)]
    pub vargo_verbose: bool,

    #[arg(long)]
    pub vstd_no_verify: bool,

    #[arg(long)]
    pub vstd_no_std: bool,

    #[arg(long, requires = "vstd_no_std")]
    pub vstd_no_alloc: bool,

    #[arg(long)]
    pub vstd_trace: bool,

    #[arg(long)]
    pub no_solver_version_check: bool,

    #[arg(long)]
    pub vstd_log_all: bool,

    #[arg(long)]
    pub vstd_no_verusfmt: bool,

    #[arg(short, long)]
    pub release: bool,

    #[arg(short, long)]
    pub package: Option<String>,

    #[arg(long, action = clap::ArgAction::Append)]
    pub exclude: Vec<String>,

    #[arg(short = 'F', long, action = clap::ArgAction::Append)]
    pub features: Vec<VerusFeatures>,

    #[command(subcommand)]
    pub command: VargoParsedSubcommand,
}

#[derive(Clone, Debug, ValueEnum)]
pub enum VerusFeatures {
    Singular,
    AxiomUsageInfo,
    RecordHistory,
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

#[derive(Clone, Debug, ValueEnum)]
pub enum CargoColor {
    Auto,
    Always,
    Never,
}

#[derive(Clone, Debug, Subcommand)]
pub enum VargoParsedSubcommand {
    /// Build Verus
    Build {
        #[arg(last = true, allow_hyphen_values = true)]
        verus_args: Vec<String>,
    },

    /// Run Verus tests
    Test {
        #[arg(last = true, allow_hyphen_values = true)]
        verus_args: Vec<String>,
    },

    /// Run Verus tests with nextest
    Nextest {
        #[command(subcommand)]
        command: NexTestRun,
    },

    /// Run a binary package
    // TODO: figure out what this is
    Run {
        #[arg(last = true, allow_hyphen_values = true)]
        cmd_args: Vec<String>,
    },

    /// Clean current build
    Clean,

    // TODO: figure out what this is
    Metadata,

    /// Run the formatter on the codebase
    Fmt,

    /// Run an arbitrary command
    // TODO: why do we need this at all???
    Cmd {
        args: Vec<String>,
    },

    /// Do something?
    // TODO: this is again weird
    Update,
}

#[derive(Clone, Debug, Subcommand)]
pub enum NexTestRun {
    Run {
        #[arg(last = true, allow_hyphen_values = true)]
        verus_args: Vec<String>,
    },
}

impl From<VargoParsedSubcommand> for VargoSubcommand {
    fn from(value: VargoParsedSubcommand) -> Self {
        match value {
            VargoParsedSubcommand::Build { verus_args } => VargoSubcommand::Build { verus_args },
            VargoParsedSubcommand::Test { verus_args } => VargoSubcommand::Test {
                nextest: false,
                verus_args,
            },
            VargoParsedSubcommand::Nextest {
                command: NexTestRun::Run { verus_args },
            } => VargoSubcommand::Test {
                nextest: true,
                verus_args,
            },
            VargoParsedSubcommand::Run { cmd_args } => VargoSubcommand::Run { cmd_args },
            VargoParsedSubcommand::Clean => VargoSubcommand::Clean,
            VargoParsedSubcommand::Metadata => VargoSubcommand::Metadata,
            VargoParsedSubcommand::Fmt => VargoSubcommand::Fmt,
            VargoParsedSubcommand::Cmd { args } => VargoSubcommand::Cmd { args },
            VargoParsedSubcommand::Update => VargoSubcommand::Update,
        }
    }
}

impl From<VargoParsedCli> for VargoCli {
    fn from(value: VargoParsedCli) -> Self {
        VargoCli {
            cargo_options: value.cargo_options,
            vargo_verbose: value.vargo_verbose,
            vstd_no_verify: value.vstd_no_verify,
            vstd_no_alloc: value.vstd_no_alloc,
            vstd_trace: value.vstd_trace,
            solver_version_check: !value.no_solver_version_check,
            vstd_log_all: value.vstd_log_all,
            vstd_no_verusfmt: value.vstd_no_verusfmt,
            release: value.release,
            package: value.package,
            exclude: value.exclude,
            features: value.features,
            command: value.command.into(),
        }
    }
}
