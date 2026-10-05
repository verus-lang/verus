use std::fs::{self, OpenOptions};
use std::io::{self, Write};
use std::path::{Component, Path, PathBuf};

use anyhow::{Context, Result, bail, ensure};
use clap::Parser;
use walkdir::WalkDir;

#[derive(Parser)]
#[command(version, about = "Create readable snapshots of executable Verus source")]
struct Args {
    /// A Rust file, crate directory, or Cargo.toml.
    input: PathBuf,
    /// Write a file or crate copy here. Required for a crate; defaults to stdout for a file.
    #[arg(short, long)]
    output: Option<PathBuf>,
    /// Skip this relative path in crate snapshots (repeatable).
    #[arg(long, value_name = "PATH")]
    exclude: Vec<PathBuf>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    ensure!(
        !fs::symlink_metadata(&args.input).context("cannot find input")?.file_type().is_symlink(),
        "symlink inputs are unsupported: {}",
        args.input.display()
    );
    let input = args.input.canonicalize().context("cannot find input")?;
    if input.is_dir() || input.file_name().is_some_and(|name| name == "Cargo.toml") {
        let root = if input.is_dir() { input.as_path() } else { input.parent().unwrap() };
        ensure!(root.join("Cargo.toml").is_file(), "crate directory must contain Cargo.toml");
        let output = args.output.context("--output is required for a crate snapshot")?;
        copy_crate(root, &output, &args.exclude)
    } else {
        ensure!(args.exclude.is_empty(), "--exclude is only supported for crate snapshots");
        ensure!(input.is_file(), "input must be a regular file or crate directory");
        let source =
            fs::read_to_string(&input).with_context(|| format!("reading {}", input.display()))?;
        let stripped = verus_exec::strip_source(&source)
            .with_context(|| format!("processing {}", input.display()))?;
        if let Some(output) = args.output {
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&output)
                .with_context(|| format!("creating {}", output.display()))?;
            file.write_all(stripped.as_bytes())?;
        } else {
            io::stdout().lock().write_all(stripped.as_bytes())?;
        }
        Ok(())
    }
}

fn copy_crate(root: &Path, output: &Path, excludes: &[PathBuf]) -> Result<()> {
    for exclude in excludes {
        ensure!(
            !exclude.as_os_str().is_empty()
                && exclude.components().all(|component| matches!(component, Component::Normal(_))),
            "--exclude must name a relative path without '.' or '..': {}",
            exclude.display()
        );
    }
    ensure!(!output.exists(), "output already exists: {}", output.display());
    let name = output.file_name().context("output must name a new directory")?;
    let parent = output.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(Path::new("."));
    let parent = parent.canonicalize().context("output parent directory must exist")?;
    ensure!(!parent.starts_with(root), "crate output must be outside the input directory");
    let destination = parent.join(name);
    // Parsing or copying failures leave no partial snapshot at the requested path.
    let temporary = tempfile::Builder::new().prefix(".verus-exec-").tempdir_in(&parent)?;
    for entry in WalkDir::new(root).into_iter().filter_entry(|e| {
        // Worktrees use a .git file pointing at the original repository. It
        // must be excluded too, so the snapshot cannot act on that repository.
        e.file_name() != ".git"
            && !(e.depth() == 1 && e.file_name() == "target" && e.file_type().is_dir())
            && !excludes.iter().any(|exclude| {
                e.path().strip_prefix(root).is_ok_and(|relative| relative.starts_with(exclude))
            })
    }) {
        let entry = entry?;
        let relative = entry.path().strip_prefix(root)?;
        let target = temporary.path().join(relative);
        if entry.file_type().is_symlink() {
            bail!("symlinks are unsupported in crate snapshots: {}", entry.path().display());
        } else if entry.file_type().is_dir() {
            fs::create_dir_all(&target)?;
        } else if !entry.file_type().is_file() {
            bail!("unsupported file type in crate snapshot: {}", entry.path().display());
        } else if entry.path().extension().is_some_and(|ext| ext == "rs") {
            let source = fs::read_to_string(entry.path())
                .with_context(|| format!("reading {}", entry.path().display()))?;
            let stripped = verus_exec::strip_source(&source)
                .with_context(|| format!("processing {}", entry.path().display()))?;
            fs::write(&target, stripped)?;
            fs::set_permissions(&target, entry.metadata()?.permissions())?;
        } else {
            fs::copy(entry.path(), &target)?;
        }
    }
    fs::rename(temporary.path(), destination).context("publishing crate snapshot")?;
    Ok(())
}
