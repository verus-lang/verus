use std::{
    env::consts::EXE_SUFFIX,
    fs,
    path::PathBuf,
    process::{Command, Stdio},
};

use anyhow::{Context, bail};
use clap::Parser;

/// Stage the artifacts needed for a Verus release archive.
#[derive(Debug, Parser)]
struct Cli {
    /// Directory containing the built artifacts.
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
    let mut artifacts: Vec<_> =
        artifacts.into_iter().map(|name| cli.build_dir.join(name)).collect();

    #[cfg(target_os = "macos")]
    artifacts.push("../tools/macos_allow_gatekeeper.sh".into());

    artifacts.push(format!("z3{EXE_SUFFIX}").into());

    for source in &artifacts {
        if !source.is_file() {
            bail!("missing release artifact: {}", source.display());
        }
    }

    // Require a fresh directory so stale files cannot enter the archive.
    fs::create_dir(&cli.output_dir)
        .with_context(|| format!("creating release directory {}", cli.output_dir.display()))?;
    for source in &artifacts {
        let destination = cli.output_dir.join(source.file_name().unwrap());
        fs::copy(source, &destination).with_context(|| {
            format!("copying {} to {}", source.display(), destination.display())
        })?;
    }

    let verus = cli.output_dir.join(format!("verus{EXE_SUFFIX}"));
    let output = Command::new(&verus)
        .args(["--version", "--output-json"])
        .stderr(Stdio::inherit())
        .output()
        .with_context(|| format!("running {} --version --output-json", verus.display()))?;
    if !output.status.success() {
        bail!("{} --version --output-json failed: {}", verus.display(), output.status);
    }
    let version_json = cli.output_dir.join("version.json");
    fs::write(&version_json, &output.stdout)
        .with_context(|| format!("writing {}", version_json.display()))?;

    println!("release artifacts staged in {}", cli.output_dir.display());
    Ok(())
}
