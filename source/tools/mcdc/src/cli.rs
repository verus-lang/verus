//! Command-line interface. DATA, BASE and NEW arguments are record files (.mcdc, .bin) or
//! directories of them.

use crate::mutate::{self, map};
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
    /// Instrument SOURCE_DIR in place for MC/DC (as `instrument --in-place`) and rewrite every
    /// file of the crates with mutant schemata, or only the files listed in --files (paths
    /// relative to SOURCE_DIR, one per line). Mutated files keep their MC/DC instrumentation.
    /// Writes manifest.jsonl, mutants.tsv and decisions.tsv to --map-dir.
    Mutate {
        source_dir: PathBuf,
        #[arg(long)]
        files: Option<PathBuf>,
        #[arg(long)]
        map_dir: PathBuf,
        /// Disable list (`file:line` or `file:line@op` entries) for points that do not compile.
        #[arg(long)]
        disable: Option<PathBuf>,
        /// Comma-separated crate directories instrumented for MC/DC (default as for `instrument`).
        #[arg(long, value_delimiter = ',')]
        crates: Option<Vec<String>>,
        /// Commit of the verifier sources recorded in the map and the build (default: the merge
        /// base of HEAD in SOURCE_DIR and --base-ref).
        #[arg(long)]
        commit: Option<String>,
        /// Upstream branch whose merge base with HEAD is the default --commit.
        #[arg(long, default_value = "origin/main")]
        base_ref: String,
        /// Compile the same rewrite with every mutant off (the runtime refuses MUTANT_BITSET).
        #[arg(long)]
        mutants_off: bool,
        /// Write the map only; leave SOURCE_DIR unchanged.
        #[arg(long)]
        dry_run: bool,
    },
    /// Select mutants from mutants.tsv and write a bitset (--out) or list their ids (--list).
    /// Selectors (--id, --ids, --file, --fn, --loc, --stdin) are united; with none, every mutant is
    /// selected. Filters: --class, then --random.
    Mutgen {
        #[arg(long)]
        map: PathBuf,
        #[arg(long)]
        id: Vec<u32>,
        #[arg(long, value_delimiter = ',')]
        ids: Vec<u32>,
        #[arg(long)]
        file: Vec<String>,
        /// Function path or `::` suffix of it (check_expr, Typing::check).
        #[arg(long = "fn")]
        func: Vec<String>,
        /// FILE:LINE (start line of the mutated text).
        #[arg(long)]
        loc: Vec<String>,
        /// Read whitespace-separated ids from stdin.
        #[arg(long)]
        stdin: bool,
        /// Operator names or classes, comma separated (`datapath` matches every datapath-* class).
        #[arg(long, value_delimiter = ',')]
        class: Vec<String>,
        /// SEED:RATE, keep each mutant with probability RATE (reproducible).
        #[arg(long)]
        random: Option<String>,
        #[arg(long)]
        out: Option<PathBuf>,
        #[arg(long)]
        list: bool,
    },
    /// Print the commit, count, digest and selected ids of a bitset file.
    Bitset { file: PathBuf },
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

fn git(dir: &Path, args: &[&str]) -> Option<String> {
    std::process::Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
}

/// The commit of the verifier sources in `dir`: the merge base of HEAD and `base_ref` (the upstream
/// commit the branch is based on), not HEAD, whose tool commits do not change the verifier.
/// Returns the commit and whether the given crate directories differ from it (committed or not).
pub fn base_commit(
    dir: &Path,
    base_ref: &str,
    crates: &[String],
) -> Result<(String, bool), String> {
    let c = git(dir, &["merge-base", "HEAD", base_ref])
        .filter(|s| s.len() == 40)
        .ok_or_else(|| format!("no merge base of HEAD and {} in {}", base_ref, dir.display()))?;
    let mut args = vec!["diff", "--quiet", c.as_str(), "--"];
    args.extend(crates.iter().map(|s| s.as_str()));
    let differs = std::process::Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(&args)
        .status()
        .map(|s| !s.success())
        .unwrap_or(true);
    Ok((c, differs))
}

#[allow(clippy::too_many_arguments)]
fn cmd_mutate(
    src: PathBuf,
    files: Option<PathBuf>,
    map_dir: PathBuf,
    disable: Option<PathBuf>,
    crates: Option<Vec<String>>,
    commit: Option<String>,
    base_ref: String,
    mutants_off: bool,
    dry_run: bool,
) -> Result<(), String> {
    let crates: Vec<String> = match crates {
        Some(c) => c.into_iter().filter(|x| !x.is_empty()).collect(),
        None => instrument::DEFAULT_CRATES.iter().map(|s| s.to_string()).collect(),
    };
    let files: Option<Vec<String>> = match files {
        Some(files) => {
            let list = std::fs::read_to_string(&files)
                .map_err(|e| format!("{}: {}", files.display(), e))?;
            Some(
                list.lines()
                    .map(|l| l.trim())
                    .filter(|l| !l.is_empty() && !l.starts_with('#'))
                    .map(|l| l.to_string())
                    .collect(),
            )
        }
        None => None,
    };
    let disabled = match &disable {
        Some(p) => mutate::read_disable(
            &std::fs::read_to_string(p).map_err(|e| format!("{}: {}", p.display(), e))?,
        ),
        None => Default::default(),
    };
    let commit = match commit {
        Some(c) => c,
        None => {
            let (c, differs) = base_commit(&src, &base_ref, &crates)?;
            if differs {
                eprintln!(
                    "warning: the verifier crates differ from {} (merge base with {}); the map records {}",
                    c, base_ref, c
                );
            }
            c
        }
    };
    let root = if dry_run {
        let tmp = std::env::temp_dir().join(format!("mcdc-mutate-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&tmp);
        std::fs::create_dir_all(&tmp).map_err(|e| e.to_string())?;
        for c in &crates {
            instrument::copy_tree(&src.join(c), &tmp.join(c))
                .map_err(|e| format!("copying {}: {}", c, e))?;
        }
        tmp
    } else {
        src.clone()
    };
    let r = mutate::mutate_tree(&root, &crates, files.as_deref(), &disabled, &commit, !mutants_off);
    if dry_run {
        let _ = std::fs::remove_dir_all(&root);
    }
    let r = r?;
    std::fs::create_dir_all(&map_dir).map_err(|e| format!("{}: {}", map_dir.display(), e))?;
    let w = |name: &str, data: &[u8]| {
        std::fs::write(map_dir.join(name), data).map_err(|e| format!("{}: {}", name, e))
    };
    let mp = map_dir.join("manifest.jsonl");
    manifest::write(&mp, &r.manifest).map_err(|e| format!("{}: {}", mp.display(), e))?;
    w("mutants.tsv", r.mutants_tsv.as_bytes())?;
    w("decisions.tsv", r.decisions_tsv.as_bytes())?;
    println!("{}", r.mcdc_stats);
    println!(
        "mutants: {}  points: {}  decisions: {} (MC/DC manifest ids: {})  points disabled: {}  guards disabled: {}",
        r.out.mutants.len(),
        r.out.points,
        r.out.decisions.len(),
        r.out.manifest_ids_used,
        r.out.points_disabled,
        r.out.guards_disabled
    );
    println!(
        "commit {}  map digest {:016x}  mutants {}",
        commit,
        r.digest,
        if mutants_off { "off" } else { "on" }
    );
    for (op, n) in mutate::op_counts(&r.out.mutants) {
        println!("  {:26} {}", op, n);
    }
    println!("map: {}", map_dir.display());
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
        Cmd::Mutate {
            source_dir,
            files,
            map_dir,
            disable,
            crates,
            commit,
            base_ref,
            mutants_off,
            dry_run,
        } => cmd_mutate(
            source_dir,
            files,
            map_dir,
            disable,
            crates,
            commit,
            base_ref,
            mutants_off,
            dry_run,
        ),
        Cmd::Mutgen { map: mp, id, ids, file, func, loc, stdin, class, random, out, list } => {
            let data = std::fs::read(&mp).map_err(|e| format!("{}: {}", mp.display(), e))?;
            let m = map::parse_map(&data)?;
            let mut sel = map::Selection {
                ids: id,
                files: file,
                fns: func,
                classes: class,
                ..Default::default()
            };
            sel.ids.extend(ids);
            for l in loc {
                let (f, n) = l.rsplit_once(':').ok_or("--loc wants FILE:LINE")?;
                sel.locs.push((f.to_string(), n.parse().map_err(|_| "bad --loc line")?));
            }
            if stdin {
                let mut s = String::new();
                std::io::Read::read_to_string(&mut std::io::stdin(), &mut s)
                    .map_err(|e| e.to_string())?;
                for x in s.split_whitespace() {
                    sel.ids.push(x.parse().map_err(|_| format!("bad id on stdin: {}", x))?);
                }
                if sel.ids.is_empty() {
                    return Err("--stdin given but no id read".into());
                }
            }
            if let Some(r) = random {
                let (a, b) = r.split_once(':').ok_or("--random wants SEED:RATE")?;
                sel.random =
                    Some((a.parse().map_err(|_| "bad seed")?, b.parse().map_err(|_| "bad rate")?));
            }
            let chosen = map::select(&m, &sel)?;
            if list {
                for i in &chosen {
                    println!("{}", i);
                }
            }
            match out {
                Some(o) => {
                    std::fs::write(&o, map::bitset(&m, &chosen))
                        .map_err(|e| format!("{}: {}", o.display(), e))?;
                    eprintln!(
                        "mutgen: {} of {} mutants selected -> {}",
                        chosen.len(),
                        m.count,
                        o.display()
                    );
                }
                None if !list => {
                    eprintln!(
                        "mutgen: {} of {} mutants selected (no --out or --list)",
                        chosen.len(),
                        m.count
                    )
                }
                None => {}
            }
            Ok(())
        }
        Cmd::Bitset { file } => {
            let data = std::fs::read(&file).map_err(|e| format!("{}: {}", file.display(), e))?;
            let (commit, count, digest, ids) =
                map::read_bitset(&data).map_err(|e| format!("{}: {}", file.display(), e))?;
            println!(
                "commit {} count {} digest {:016x} selected {}",
                commit,
                count,
                digest,
                ids.len()
            );
            for i in ids {
                println!("{}", i);
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
