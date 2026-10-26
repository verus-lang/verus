use std::{env::consts::EXE_SUFFIX, fs, path::PathBuf};

use anyhow::{Context, bail};
use clap::Parser;

/// Stage the artifacts needed for a Verus release archive.
#[derive(Debug, Parser)]
struct Cli {
    /// Directory containing the built artifacts and staged metadata.
    #[arg(long, default_value = "target-verus/release")]
    build_dir: PathBuf,
    /// New directory to create for the release archive contents.
    #[arg(long, default_value = "release-archive")]
    output_dir: PathBuf,
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    let mut artifacts = cargo_verus_toolchains::installed::required_artifacts();
    artifacts
        .extend(["verus", "rust_verify", "cargo-verus"].map(|name| format!("{name}{EXE_SUFFIX}")));
    artifacts.push("version.json".into());
    #[cfg(target_os = "macos")]
    artifacts.push("macos_allow_gatekeeper.sh".into());
    let mut artifacts: Vec<_> =
        artifacts.into_iter().map(|name| (cli.build_dir.join(&name), name)).collect();

    let z3 = format!("z3{EXE_SUFFIX}");
    artifacts.push((PathBuf::from(&z3), z3));

    for (source, _) in &artifacts {
        if !source.is_file() {
            bail!("missing release artifact: {}", source.display());
        }
    }

    // Require a fresh directory so stale files cannot enter the archive.
    fs::create_dir(&cli.output_dir)
        .with_context(|| format!("creating release directory {}", cli.output_dir.display()))?;
    for (source, artifact) in &artifacts {
        let destination = cli.output_dir.join(artifact);
        fs::copy(source, &destination).with_context(|| {
            format!("copying {} to {}", source.display(), destination.display())
        })?;
    }
    println!("release artifacts staged in {}", cli.output_dir.display());
    Ok(())
}
