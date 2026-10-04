use std::{path::PathBuf, process::Command};

use anyhow::{Context, Result, bail};

type Crate = crate::Crate<String>;

pub fn get_verus_version(mark_dirty: bool) -> Result<(String, String)> {
    let rev_full = get_git_rev(None)?;
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

    let dirty = if !mark_dirty || run_command(&["git", "diff", "--exit-code", "HEAD"]).is_ok() {
        ""
    } else {
        ".dirty"
    };

    Ok((format!("0.{year}.{month}.{day}.{rev}{dirty}"), rev_full))
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

/// Get the existing Git files that determine the current `HEAD` commit.
///
/// This works for ordinary repositories, linked worktrees, both symbolic and detached `HEAD`s,
/// and packed refs.
pub fn get_git_head_paths() -> Result<Vec<PathBuf>> {
    let mut paths = vec![get_git_path("HEAD")?.context("Git HEAD is missing")?];

    if let Ok(head_ref) = run_command(&["git", "symbolic-ref", "--quiet", "HEAD"])
        && let Some(path) = get_git_path(head_ref.trim())?
    {
        paths.push(path);
    }

    if let Some(path) = get_git_path("packed-refs")? {
        paths.push(path);
    }

    Ok(paths)
}

/// Get the absolute path to a Git file when it exists.
fn get_git_path(path: &str) -> Result<Option<PathBuf>> {
    let path = run_command(&["git", "rev-parse", "--path-format=absolute", "--git-path", path])?;
    let path = PathBuf::from(path.trim());
    Ok(path.exists().then_some(path))
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
