use std::path::PathBuf;

use anyhow::Context;
use cargo_verus_toolchains::{
    external_deps, format_manifest,
    versions::{get_verus_version, get_vstd_version},
};
use clap::Parser;

type Toolchain = cargo_verus_toolchains::Toolchain<String>;

fn main() -> anyhow::Result<()> {
    use std::io::Write;

    let cli = Cli::parse();
    let toolchain = create_toolchain(cli.rolling)?;
    let manifest = format_manifest(&toolchain)?;

    if let Some(output_dir) = cli.write_to_dir {
        let name = if cli.rolling { "rolling-release" } else { &toolchain.verus };
        let path = output_dir.join(&format!("{name}.toml"));
        let mut file = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(&path)
            .context(format!("opening file `{}`", path.display()))?;
        write!(file, "{manifest}").context(format!("writing file `{}`", path.display()))?;
        println!("manifest written to `{}`", path.display());
    };

    print!("{manifest}");
    Ok(())
}

/// Tool to create toolchain manifest files.
#[derive(Clone, Debug, Parser)]
struct Cli {
    /// Write the manifest into a file in a directory.
    #[arg(long)]
    pub write_to_dir: Option<PathBuf>,
    /// The manifest is for a rolling release.
    #[arg(long)]
    pub rolling: bool,
}

fn create_toolchain(is_rolling: bool) -> anyhow::Result<Toolchain> {
    let (verus, _) = get_verus_version(false)?;
    let vstd = get_vstd_version(is_rolling)?;
    let z3 = external_deps::Z3_VERSION.to_string();
    let cvc5 = external_deps::CVC5_VERSION.to_string();
    let singular = external_deps::SINGULAR_VERSION.to_string();
    Ok(Toolchain { verus, vstd, z3, cvc5, singular })
}
