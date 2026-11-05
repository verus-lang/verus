//! The `mutate` subcommand: MC/DC instrumentation of the verifier crates plus mutant schemata in a
//! list of files, compiled into one build and switched at run time by a bitset (see `map`).
//!
//! `mutate_tree` first instruments every crate for MC/DC (as `mcdc instrument` does) but leaves the
//! listed files untouched; the MC/DC manifest still numbers their decisions, so ids are the same
//! as in an `mcdc instrument` build of the same source. The listed files are then rewritten by
//! `rewrite::mutate_sources`, whose decisions reuse the manifest ids and whose `crate::__mut::rec`
//! forwards to the MC/DC runtime.

pub mod map;
pub mod rewrite;

use crate::instrument::{self, manifest::Decision};
use std::collections::{HashMap, HashSet};
use std::path::Path;

pub const RUNTIME: &str = include_str!("../runtime/mut_rt.rs");
pub const RUNTIME_FILE: &str = "__mut_rt.rs";
pub const CONSTS_FILE: &str = "__mut_build.rs";

/// Reads a disable list: one entry per line, `#` starts a comment line.
pub fn read_disable(text: &str) -> HashSet<String> {
    text.lines()
        .map(|l| l.trim())
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(|l| l.to_string())
        .collect()
}

pub struct TreeResult {
    pub manifest: Vec<Decision>,
    pub mcdc_stats: instrument::Stats,
    pub out: rewrite::Output,
    pub mutants_tsv: String,
    pub decisions_tsv: String,
    pub digest: u64,
}

/// Instruments `root` (the Verus source/ dir) in place: MC/DC in every crate of `crates`, mutant
/// schemata in `files` (paths relative to `root`; `None` means every `.rs` file of those crates).
/// A mutated file keeps the MC/DC edits of `mcdc instrument`, so the manifest and the records are
/// those of an `mcdc instrument` build of the same source. `commit` (40 characters) and
/// `mutants_on` go into the build constants.
pub fn mutate_tree(
    root: &Path,
    crates: &[String],
    files: Option<&[String]>,
    disabled: &HashSet<String>,
    commit: &str,
    mutants_on: bool,
) -> Result<TreeResult, String> {
    if commit.len() != 40 {
        return Err(format!("commit must have 40 characters: {:?}", commit));
    }
    let files: Vec<String> = match files {
        Some(f) => f.to_vec(),
        None => instrument::crate_files(root, crates)?,
    };
    for f in &files {
        let krate = f.split('/').next().unwrap_or("");
        if !crates.iter().any(|c| c == krate) {
            return Err(format!("{}: crate {} is not instrumented (--crates)", f, krate));
        }
    }
    let skip: HashSet<String> = files.iter().cloned().collect();
    let (manifest, mcdc_stats, mut pending) =
        instrument::instrument_tree_except(root, crates, &skip)?;
    let man_ids: HashMap<(String, usize, usize), u32> =
        manifest.iter().map(|d| ((d.file.clone(), d.line, d.col), d.id)).collect();
    let mut srcs = Vec::new();
    let mut edits = Vec::new();
    for f in &files {
        let (s, e) = pending.remove(f).ok_or_else(|| format!("{}: not a file of the crates", f))?;
        srcs.push((f.clone(), s));
        edits.push(e);
    }
    let mut mcdc_stats = mcdc_stats;
    mcdc_stats.files_changed += edits.iter().filter(|e| !e.is_empty()).count();
    let out = rewrite::mutate_sources_with(&srcs, &man_ids, disabled, edits)?;
    for (f, s) in files.iter().zip(&out.sources) {
        std::fs::write(root.join(f), s).map_err(|e| format!("{}: {}", f, e))?;
    }
    let mutants_tsv = map::mutants_tsv(&out.mutants, commit);
    let digest = map::fnv(mutants_tsv.as_bytes());
    let decisions_tsv = map::decisions_tsv(&out.decisions);
    let consts = map::build_consts(commit, out.mutants.len(), digest, mutants_on);
    // vir owns the runtime (one guard stack for vir and rust_verify); other crates get their own copy
    let mut touched: Vec<String> = Vec::new();
    for f in &files {
        let k = f.split('/').next().unwrap().to_string();
        if !touched.contains(&k) {
            touched.push(k);
        }
    }
    if touched.iter().any(|k| k == "rust_verify") && !touched.iter().any(|k| k == "vir") {
        return Err("rust_verify uses vir::__mut: mutate at least one vir file".into());
    }
    for k in &touched {
        let src_dir = root.join(k).join("src");
        // the library root owns the runtime; a crate without a library uses its binary root
        let lib = if src_dir.join("lib.rs").exists() {
            src_dir.join("lib.rs")
        } else {
            src_dir.join("main.rs")
        };
        let src = std::fs::read_to_string(&lib).map_err(|e| format!("{}: {}", lib.display(), e))?;
        let owner = if k == "rust_verify" { "vir" } else { k.as_str() };
        let add = if k == "rust_verify" {
            "\n#[allow(unused_imports)] pub(crate) use vir::__mut;\n".to_string()
        } else {
            // proc-macro crates cannot export the module
            let proc_macro = k == "builtin_macros" || k == "state_machines_macros";
            let vis = if proc_macro { "pub(crate)" } else { "pub" };
            std::fs::write(src_dir.join(RUNTIME_FILE), RUNTIME).map_err(|e| e.to_string())?;
            std::fs::write(src_dir.join(CONSTS_FILE), &consts).map_err(|e| e.to_string())?;
            format!(
                "\n#[doc(hidden)] #[allow(dead_code, unused)] {} mod __mut {{ include!({:?}); include!({:?}); }}\n",
                vis, CONSTS_FILE, RUNTIME_FILE
            )
        };
        std::fs::write(&lib, format!("{}{}", src, add)).map_err(|e| e.to_string())?;
        // a binary crate root among the mutated files uses the library's runtime
        let main_rel = format!("{}/src/main.rs", k);
        if files.contains(&main_rel) && src_dir.join("lib.rs").exists() {
            let main = root.join(&main_rel);
            let src = std::fs::read_to_string(&main).map_err(|e| format!("{}: {}", main_rel, e))?;
            let add = format!("\n#[allow(unused_imports)] use {}::__mut;\n", owner);
            std::fs::write(&main, format!("{}{}", src, add)).map_err(|e| e.to_string())?;
        }
    }
    Ok(TreeResult { manifest, mcdc_stats, out, mutants_tsv, decisions_tsv, digest })
}

/// Mutant counts per operator, sorted by operator name.
pub fn op_counts(mutants: &[rewrite::Mutant]) -> Vec<(&'static str, usize)> {
    let mut m: std::collections::BTreeMap<&'static str, usize> = Default::default();
    for x in mutants {
        *m.entry(x.op).or_default() += 1;
    }
    m.into_iter().collect()
}
