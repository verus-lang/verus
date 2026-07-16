use std::{path::PathBuf, process::Command};

use anyhow::Context;
use cargo_verus_toolchains::format_manifest;
use clap::Parser;
use serde::{Deserialize, Serialize};

type Toolchain = cargo_verus_toolchains::Toolchain<String>;
type Crate = cargo_verus_toolchains::Crate<String>;

fn main() -> anyhow::Result<()> {
    use std::io::Write;

    let cli = Cli::parse_from(std::env::args());
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
    let verus = get_verus_version()?;
    let vstd = get_vstd_version(is_rolling)?;
    let z3 = external_deps.z3;
    let singular = external_deps.singular;
    Ok(Toolchain { verus, vstd, z3, singular })
}

fn get_external_deps() -> anyhow::Result<ExternalDeps> {
    const PATH: &str = "external-deps.toml";
    let contents = std::fs::read_to_string(PATH).context("reading `{PATH}`")?;
    let external_deps = toml::from_str(&contents).context("parsing `{PATH}`")?;
    Ok(external_deps)
}

fn get_verus_version() -> anyhow::Result<String> {
    let git_rev_parse = Command::new("git")
        .args(["rev-parse", "-q", "--short=7", "HEAD"])
        .output()
        .context("running `git rev-parse`")?;
    if !git_rev_parse.status.success() {
        anyhow::bail!("failed to run `git rev-parse`");
    }
    let rev_raw = String::from_utf8(git_rev_parse.stdout).context("commit hash is invalid utf8")?;
    let rev = rev_raw.trim();

    let git_show_date = std::process::Command::new("git")
        .args(["show", "-s", "--format=%cs", "HEAD"])
        .output()
        .context("running `git show`")?;
    if !git_show_date.status.success() {
        anyhow::bail!("failed to run `git show`");
    }
    let date_str =
        String::from_utf8(git_show_date.stdout).context("commit date is invalid utf8")?;
    let date_re =
        regex::Regex::new(r"^(\d{4})-(\d{2})-(\d{2})$").context("regex is well formed")?;
    let date_captures =
        date_re.captures(date_str.trim()).context("unexpected date string {date_str:?}")?;
    let year = &date_captures[1];
    let month = &date_captures[2];
    let day = &date_captures[3];

    Ok(format!("0.{year}.{month}.{day}.{rev}"))
}

fn get_vstd_version(is_rolling: bool) -> anyhow::Result<Crate> {
    if is_rolling {
        // For a rolling release, pin to the Git commit.
        let git_rev_parse = Command::new("git")
            .args(["rev-parse", "-q", "--short", "HEAD"])
            .output()
            .context("running `git rev-parse`")?;
        if !git_rev_parse.status.success() {
            anyhow::bail!("failed to run `git rev-parse`");
        }
        let rev = String::from_utf8(git_rev_parse.stdout)
            .context("commit hash is invalid utf8")?
            .trim()
            .to_owned();
        let git = "https://github.com/verus-lang/verus.git".into();
        Ok(Crate::GitCommit { git, rev })
    } else {
        // For a stable release, use the latest published version.
        const VSTD_CARGO_TOML: &str = "vstd/Cargo.toml";
        let contents =
            std::fs::read_to_string(VSTD_CARGO_TOML).context("reading `{VSTD_CARGO_TOML}`")?;
        let table: toml::Table = contents.parse()?;
        let value = table
            .get("package")
            .context("look up key `package`")?
            .get("version")
            .context("look up key `version`")?;
        let toml::Value::String(version) = value else {
            anyhow::bail!("version is not a string");
        };
        Ok(Crate::Registry(version.into()))
    }
}
