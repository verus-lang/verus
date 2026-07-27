use std::path::PathBuf;

use anyhow::Context;
use cargo_verus_toolchains::format_manifest;
use clap::Parser;
use serde::{Deserialize, Serialize};

use cargo_verus_toolchains::versions::{get_verus_version, get_vstd_version};

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

/// External components that Verus depends on.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct ExternalDeps {
    z3: String,
    singular: String,
}

fn create_toolchain(is_rolling: bool) -> anyhow::Result<Toolchain> {
    let external_deps = get_external_deps()?;
    let (verus, _) = get_verus_version(false)?;
    let vstd = get_vstd_version(is_rolling)?;
    let z3 = external_deps.z3;
    let singular = external_deps.singular;
    Ok(Toolchain { verus, vstd, z3, singular })
}

fn get_external_deps() -> anyhow::Result<ExternalDeps> {
    const PATH: &str = "external-deps.toml";
    let contents = std::fs::read_to_string(PATH).context(format!("reading `{PATH}`"))?;
    let external_deps = toml::from_str(&contents).context(format!("parsing `{PATH}`"))?;
    Ok(external_deps)
}
