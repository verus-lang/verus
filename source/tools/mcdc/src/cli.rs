//! Command-line interface. DATA, BASE and NEW arguments are record files (.mcdc, .bin) or
//! directories of them.

use crate::{analyze, instrument, manifest};
use clap::{Parser, Subcommand};
use std::path::{Path, PathBuf};

#[derive(Parser)]
#[command(name = "mcdc", about = "MC/DC coverage of the Verus verifier crates (see README.md)")]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Rewrite SOURCE_DIR/<crate>/src/**/*.rs for each crate and write the manifest (default:
    /// <rewritten dir>/mcdc-manifest.jsonl). With --out, SOURCE_DIR is first copied to DIR (which
    /// must not exist; target/, target-verus/, .verus-log/ and .git/ are not copied) and the copy
    /// is rewritten. --in-place rewrites SOURCE_DIR itself.
    Instrument {
        source_dir: PathBuf,
        #[arg(long, conflicts_with = "in_place", required_unless_present = "in_place")]
        out: Option<PathBuf>,
        #[arg(long)]
        in_place: bool,
        #[arg(long)]
        manifest: Option<PathBuf>,
        /// Comma-separated crate directories (default: vir,rust_verify,air,builtin_macros,
        /// state_machines_macros).
        #[arg(long, value_delimiter = ',')]
        crates: Option<Vec<String>>,
    },
    /// decisions.tsv, per-file.tsv and summary.md: MC/DC, condition and decision coverage.
    Report {
        manifest: PathBuf,
        #[arg(required = true)]
        data: Vec<PathBuf>,
        #[arg(long)]
        out: PathBuf,
    },
    /// GAPS.tsv and GAPS.md: one line per atom without an independence pair, with a pair that
    /// would show it.
    Gaps {
        manifest: PathBuf,
        #[arg(required = true)]
        data: Vec<PathBuf>,
        #[arg(long)]
        out: PathBuf,
        #[arg(long)]
        hints: Option<PathBuf>,
    },
    /// Decisions, outcomes, condition-covered atoms and MC/DC atoms that NEW adds to BASE.
    Delta {
        manifest: PathBuf,
        base: PathBuf,
        #[arg(required = true)]
        new: Vec<PathBuf>,
    },
    /// Merge records into one file of distinct records.
    Compact {
        out: PathBuf,
        #[arg(required = true)]
        data: Vec<PathBuf>,
    },
}

fn read_manifest(p: &Path) -> Result<Vec<manifest::Decision>, String> {
    manifest::read(p)
}

fn cmd_instrument(
    src: PathBuf,
    out: Option<PathBuf>,
    man: Option<PathBuf>,
    crates: Option<Vec<String>>,
) -> Result<(), String> {
    let crates: Vec<String> = match crates {
        Some(c) => c.into_iter().filter(|x| !x.is_empty()).collect(),
        None => instrument::DEFAULT_CRATES.iter().map(|s| s.to_string()).collect(),
    };
    let root = match out {
        Some(o) => {
            if o.exists() {
                return Err(format!("{} exists; --out needs a new directory", o.display()));
            }
            instrument::copy_tree(&src, &o)
                .map_err(|e| format!("copying to {}: {}", o.display(), e))?;
            o
        }
        None => src,
    };
    let man = man.unwrap_or_else(|| root.join("mcdc-manifest.jsonl"));
    let (decisions, stats) = instrument::instrument_tree(&root, &crates)?;
    manifest::write(&man, &decisions).map_err(|e| format!("{}: {}", man.display(), e))?;
    println!("{}", stats);
    println!("rewritten tree: {}\nmanifest: {}", root.display(), man.display());
    Ok(())
}

pub fn run() -> Result<(), String> {
    let cli = Cli::parse();
    match cli.cmd {
        Cmd::Instrument { source_dir, out, in_place: _, manifest, crates } => {
            cmd_instrument(source_dir, out, manifest, crates)
        }
        Cmd::Report { manifest, data, out } => {
            let man = read_manifest(&manifest)?;
            let data = analyze::load(&data)?;
            let txt = analyze::report(&man, &data, &out)?;
            print!("{}", txt);
            let ids: std::collections::BTreeSet<u32> = man.iter().map(|d| d.id).collect();
            let unknown = data.keys().filter(|k| !ids.contains(k)).count();
            if unknown > 0 {
                eprintln!("warning: {} recorded ids are not in the manifest", unknown);
            }
            Ok(())
        }
        Cmd::Gaps { manifest, data, out, hints } => {
            let hints = match hints {
                Some(h) => analyze::read_hints(&h)?,
                None => Default::default(),
            };
            let man = read_manifest(&manifest)?;
            let data = analyze::load(&data)?;
            let (n, rows, prio) = analyze::gaps(&man, &data, &out, &hints)?;
            println!(
                "{} decisions with uncovered atoms, {} GAPS.tsv lines (one per uncovered atom)",
                n, rows
            );
            println!("priority-file decisions with gaps: {}", prio);
            Ok(())
        }
        Cmd::Delta { manifest, base, new } => {
            let man = read_manifest(&manifest)?;
            let base = analyze::load(&[base])?;
            let new = analyze::load(&new)?;
            for l in analyze::delta(&man, &base, &new) {
                println!("{}", l);
            }
            Ok(())
        }
        Cmd::Compact { out, data } => {
            let n = analyze::compact(&out, &data)?;
            println!("{} unique records -> {}", n, out.display());
            Ok(())
        }
    }
}
