//! The `instrument` subcommand: rewrites the `.rs` files of the verifier crates (see `rewrite`)
//! and writes the manifest of the instrumented decisions.

pub mod manifest;
pub mod rewrite;

pub use rewrite::instrument_source;

use crate::edit::Insert;
use manifest::Decision;
use std::path::{Path, PathBuf};

/// The runtime module, written next to each crate root as `RUNTIME_FILE`.
pub const RUNTIME: &str = include_str!("../runtime/mcdc_rt.rs");
pub const RUNTIME_FILE: &str = "__mcdc_rt.rs";
/// The crates `mcdc instrument` rewrites by default (directories under the Verus source/ dir).
pub const DEFAULT_CRATES: &[&str] =
    &["vir", "rust_verify", "air", "builtin_macros", "state_machines_macros"];

#[derive(Default, Debug)]
pub struct Stats {
    pub files: usize,
    pub files_changed: usize,
    pub decisions: usize,
    pub atoms: usize,
    pub skipped_letchain: usize,
    pub skipped_too_many: usize,
    pub skipped_const: usize,
    pub macro_logic_ops: usize,
    pub letchains: usize,
    pub parse_failures: Vec<String>,
}

impl std::fmt::Display for Stats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "files scanned: {}", self.files)?;
        writeln!(f, "files rewritten: {}", self.files_changed)?;
        writeln!(f, "decisions instrumented: {}", self.decisions)?;
        writeln!(f, "atoms instrumented: {}", self.atoms)?;
        writeln!(
            f,
            "let-chain decisions instrumented (if, while, match guard; included in decisions): {}",
            self.letchains
        )?;
        writeln!(
            f,
            "skipped let-chain decisions (other positions): {}",
            self.skipped_letchain
        )?;
        writeln!(f, "skipped decisions with more than 64 atoms: {}", self.skipped_too_many)?;
        writeln!(f, "skipped decisions in const contexts: {}", self.skipped_const)?;
        writeln!(
            f,
            "&&/|| operators inside macro invocations (not instrumented; quote!/parse_quote! excluded): {}",
            self.macro_logic_ops
        )?;
        write!(f, "parse failures: {}", self.parse_failures.len())?;
        for p in &self.parse_failures {
            write!(f, "\n  parse failure: {}", p)?;
        }
        Ok(())
    }
}

fn rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = match std::fs::read_dir(dir) {
        Ok(r) => r.filter_map(|e| e.ok()).map(|e| e.path()).collect(),
        Err(_) => return,
    };
    entries.sort();
    for p in entries {
        if p.is_dir() {
            rs_files(&p, out);
        } else if p.extension().map_or(false, |x| x == "rs")
            && p.file_name().map_or(false, |n| {
                n != RUNTIME_FILE
                    && n != crate::mutate::RUNTIME_FILE
                    && n != crate::mutate::CONSTS_FILE
            })
        {
            out.push(p);
        }
    }
}

/// Instruments `root/<crate>/src/**/*.rs` in place for each crate, in the given order, with ids
/// starting at 1. Writes the runtime next to each crate root (src/lib.rs, src/main.rs). Returns the
/// decisions (for the manifest) and statistics.
pub fn instrument_tree(root: &Path, crates: &[String]) -> Result<(Vec<Decision>, Stats), String> {
    let (d, s, _) = instrument_tree_except(root, crates, &std::collections::HashSet::new())?;
    Ok((d, s))
}

/// The `.rs` files of the crates (paths relative to `root`), in the order `instrument_tree` numbers
/// them, without the runtime files.
pub fn crate_files(root: &Path, crates: &[String]) -> Result<Vec<String>, String> {
    let mut out = Vec::new();
    for krate in crates {
        let src_dir = root.join(krate).join("src");
        if !src_dir.is_dir() {
            return Err(format!("{} is not a directory", src_dir.display()));
        }
        let mut files = Vec::new();
        rs_files(&src_dir, &mut files);
        for f in files {
            let rel = f.strip_prefix(root).unwrap().to_string_lossy().replace('\\', "/");
            if !rel.ends_with(&format!("/{}", crate::mutate::RUNTIME_FILE))
                && !rel.ends_with(&format!("/{}", crate::mutate::CONSTS_FILE))
            {
                out.push(rel);
            }
        }
    }
    Ok(out)
}

/// The edits of one file that `instrument_tree_except` did not apply: (original text, edits).
pub type Pending = std::collections::HashMap<String, (String, Vec<Insert>)>;

/// `instrument_tree`, except that the files in `keep` (paths relative to `root`) are not rewritten:
/// their MC/DC edits are returned instead, to be applied with other edits. Ids and the manifest do
/// not depend on `keep`.
pub fn instrument_tree_except(
    root: &Path,
    crates: &[String],
    keep: &std::collections::HashSet<String>,
) -> Result<(Vec<Decision>, Stats, Pending), String> {
    let mut next_id: u32 = 1;
    let mut decisions = Vec::new();
    let mut stats = Stats::default();
    let mut pending = Pending::new();
    for krate in crates {
        let src_dir = root.join(krate).join("src");
        if !src_dir.is_dir() {
            return Err(format!("{} is not a directory", src_dir.display()));
        }
        let mut files = Vec::new();
        rs_files(&src_dir, &mut files);
        let mut wrote_runtime = false;
        for f in files {
            let rel = f.strip_prefix(root).unwrap().to_string_lossy().replace('\\', "/");
            let src = std::fs::read_to_string(&f).map_err(|e| format!("{}: {}", f.display(), e))?;
            let fname = f.file_name().unwrap().to_string_lossy().to_string();
            let is_root =
                f.parent() == Some(src_dir.as_path()) && (fname == "lib.rs" || fname == "main.rs");
            let ins = rewrite::instrument_inserts(
                &src,
                &rel,
                krate,
                is_root,
                &mut next_id,
                &mut decisions,
                &mut stats,
            )?;
            if keep.contains(&rel) {
                pending.insert(rel.clone(), (src, ins.unwrap_or_default()));
            } else if let Some(ins) = ins.filter(|i| !i.is_empty()) {
                stats.files_changed += 1;
                let out = crate::edit::render(&src, ins).map_err(|e| format!("{}: {}", rel, e))?;
                std::fs::write(&f, out).map_err(|e| format!("{}: {}", f.display(), e))?;
            }
            if is_root && !wrote_runtime {
                std::fs::write(src_dir.join(RUNTIME_FILE), RUNTIME)
                    .map_err(|e| format!("{}: {}", src_dir.display(), e))?;
                wrote_runtime = true;
            }
        }
    }
    Ok((decisions, stats, pending))
}

/// Copies `from` to `to` recursively, skipping build outputs and VCS metadata (`target`,
/// `target-verus`, `.verus-log`, `.git`). `to` must not exist.
pub fn copy_tree(from: &Path, to: &Path) -> std::io::Result<()> {
    std::fs::create_dir(to)?;
    for e in std::fs::read_dir(from)? {
        let e = e?;
        let name = e.file_name();
        let ft = e.file_type()?;
        let dst = to.join(&name);
        if ft.is_dir() {
            if matches!(name.to_str(), Some("target" | "target-verus" | ".verus-log" | ".git")) {
                continue;
            }
            copy_tree(&e.path(), &dst)?;
        } else if ft.is_symlink() {
            let t = std::fs::read_link(e.path())?;
            #[cfg(unix)]
            std::os::unix::fs::symlink(t, &dst)?;
            #[cfg(not(unix))]
            let _ = t;
        } else {
            std::fs::copy(e.path(), &dst)?;
        }
    }
    Ok(())
}
