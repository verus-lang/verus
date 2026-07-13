#[derive(Clone, Copy, Debug, clap::Parser)]
pub struct Config {
    /// Print all the annotated files
    #[arg(short, long)]
    pub print_all: bool,

    /// Do not ignore items outside of `verus!` by default
    #[arg(long)]
    pub no_external_by_default: bool,

    /// Output as machine-readable json
    #[arg(long)]
    pub json: bool,

    /// Consider delimiter-only lines as layout
    #[arg(long)]
    pub delimiters_are_layout: bool,

    /// Do not apply _trusted_ to proofs
    #[arg(long)]
    pub proofs_arent_trusted: bool,
}

pub enum RunMode {
    DepsPath(std::path::PathBuf),
    OneFile(std::path::PathBuf),
    Dir(Vec<std::path::PathBuf>),
}
