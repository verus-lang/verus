use std::process::Command;

use anyhow::{Context, Result, bail};

type Crate = crate::Crate<String>;

pub fn get_verus_version() -> Result<String> {
    let rev = get_git_rev(Some(7))?;
    let date_str = run_command(&["git", "show", "-s", "--format=%cs", "HEAD"])?;
    let date_re =
        regex::Regex::new(r"^(\d{4})-(\d{2})-(\d{2})$").context("regex is well formed")?;
    let date_captures = date_re
        .captures(date_str.trim())
        .context(format!("unexpected date string {date_str:?}"))?;
    let year = &date_captures[1];
    let month = &date_captures[2];
    let day = &date_captures[3];

    Ok(format!("0.{year}.{month}.{day}.{rev}"))
}

pub fn get_vstd_version(is_rolling: bool) -> Result<Crate> {
    if is_rolling {
        // For a rolling release, pin to the Git commit.
        let rev = get_git_rev(None)?;
        let git = "https://github.com/verus-lang/verus.git".into();
        Ok(Crate::GitCommit { git, rev })
    } else {
        // For a stable release, use the latest published version.
        const VSTD_CARGO_TOML: &str = "vstd/Cargo.toml";
        let contents = std::fs::read_to_string(VSTD_CARGO_TOML)
            .context(format!("reading `{VSTD_CARGO_TOML}`"))?;
        let table: toml::Table =
            contents.parse().context(format!("parsing `{VSTD_CARGO_TOML}`"))?;
        let value = table
            .get("package")
            .context("looking up key `package`")?
            .get("version")
            .context("looking up key `version`")?;
        let toml::Value::String(version) = value else {
            bail!("version is not a string");
        };
        Ok(Crate::Registry(version.into()))
    }
}

/// Get the revision of `HEAD`.
///
/// With `abbreviate_to`, shorten the revision to that many hexadecimal digits.
/// Without it, use the full commit hash, which is what Cargo reports for a Git
/// dependency.
fn get_git_rev(abbreviate_to: Option<usize>) -> Result<String> {
    let short_flag = abbreviate_to.map(|len| format!("--short={len}"));

    let mut args = vec!["git", "rev-parse", "-q"];
    if let Some(short_flag) = &short_flag {
        args.push(short_flag);
    }
    args.push("HEAD");

    let raw_rev = run_command(&args)?;
    Ok(raw_rev.trim().to_owned())
}

fn run_command(program_and_args: &[&str]) -> Result<String> {
    let mut command = Command::new(program_and_args[0]);
    command.args(&program_and_args[1..]);
    let result = command.output().with_context(|| format!("running {command:?}"))?;
    if !result.status.success() {
        bail!("failed to run {command:?}");
    }
    let output = String::from_utf8(result.stdout)
        .with_context(|| format!("reading output of {command:?}"))?;
    Ok(output)
}
