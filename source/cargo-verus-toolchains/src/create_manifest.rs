use anyhow::Context;
use std::process::Command;

type Toolchain = cargo_verus_toolchains::Toolchain<String>;
type Crate = cargo_verus_toolchains::Crate<String>;

fn main() -> anyhow::Result<()> {
    let verus = make_verus_version()?;
    let vstd = Crate::Registry("TODO".into());
    let z3 = "TODO".into();
    let toolchain = Toolchain { verus, vstd, z3 };
    let manifest = toml::to_string_pretty(&toolchain).context("format manifest")?;
    print!("{manifest}");
    Ok(())
}

fn make_verus_version() -> anyhow::Result<String> {
    let git_rev_parse = Command::new("git")
        .args(["rev-parse", "--short=7", "HEAD"])
        .output()
        .context("failed to run `git rev-parse`")?;
    let sha_str = String::from_utf8(git_rev_parse.stdout).context("commit sha is invalid utf8")?;
    let sha_short = sha_str.trim();

    let git_show_date = std::process::Command::new("git")
        .args(["show", "-s", "--format=%cs", "HEAD"])
        .output()
        .context("failed to run `git show`")?;
    let date_str =
        String::from_utf8(git_show_date.stdout).context("commit date is invalid utf8")?;
    let date_re =
        regex::Regex::new(r"^(\d{4})-(\d{2})-(\d{2})$").context("regex is well formed")?;
    let date_captures =
        date_re.captures(date_str.trim()).context("unexpected date string {date_str:?}")?;
    let year = &date_captures[0];
    let month = &date_captures[1];
    let day = &date_captures[2];

    Ok(format!("0.{year}.{month}.{day}.{sha_short}"))
}
