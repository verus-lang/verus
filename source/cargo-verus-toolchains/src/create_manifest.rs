use anyhow::Context;
use clap::Parser;
use std::process::Command;

type Toolchain = cargo_verus_toolchains::Toolchain<String>;
type Crate = cargo_verus_toolchains::Crate<String>;

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse_from(std::env::args());
    let toolchain = create_toolchain(cli.rolling)?;
    let manifest = toml::to_string_pretty(&toolchain).context("format manifest")?;
    print!("{manifest}");
    Ok(())
}

/// Tool to create toolchain manifest files.
#[derive(Clone, Debug, Parser)]
pub struct Cli {
    /// The manifest is for a rolling release.
    #[arg(long)]
    pub rolling: bool,
}

fn create_toolchain(is_rolling: bool) -> anyhow::Result<Toolchain> {
    let verus = make_verus_version()?;
    let vstd = get_vstd_version(is_rolling)?;
    let z3 = "TODO".into();
    Ok(Toolchain { verus, vstd, z3 })
}

fn make_verus_version() -> anyhow::Result<String> {
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
        let contents = std::fs::read_to_string("vstd/Cargo.toml")?;
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
