//! Tests of the mutant-schemata rewriter, the mutant map, mutgen selection and the bitset format.

use mcdc::mutate::map::{self, Selection};
use mcdc::mutate::rewrite::{FIRST_LOCAL_DECISION, mutate_sources};
use std::collections::{BTreeSet, HashMap, HashSet};

const SRC: &str = r#"
pub enum Mode { Spec, Proof, Exec }

pub fn check(a: bool, b: bool, v: &mut Vec<u32>, m: Mode) -> Result<u32, String> {
    if a && b {
        v.push(1);
        return Err("both".to_string());
    }
    if v.len() > 2 {
        let x = v.get(0).copied();
        if matches!(m, Mode::Exec) {
            return Ok(x.unwrap_or(0));
        }
    }
    let n = parse(v)?;
    Ok(n + 1)
}

fn parse(v: &Vec<u32>) -> Result<u32, String> {
    match v.first() {
        Some(x) => Ok(*x),
        None => Err("empty".to_string()),
    }
}

fn is_small(x: u32) -> bool {
    x < 10
}
"#;

fn files() -> Vec<(String, String)> {
    vec![("vir/src/sample.rs".to_string(), SRC.to_string())]
}

fn tsv_of(disabled: &HashSet<String>, manifest: &HashMap<(String, usize, usize), u32>) -> String {
    let out = mutate_sources(&files(), manifest, disabled).unwrap();
    map::mutants_tsv(&out.mutants, &"a".repeat(40))
}

#[test]
fn map_is_deterministic() {
    let none = HashSet::new();
    let man = HashMap::new();
    let a = tsv_of(&none, &man);
    let b = tsv_of(&none, &man);
    assert_eq!(a, b);
    assert_eq!(map::fnv(a.as_bytes()), map::fnv(b.as_bytes()));
    // ids are 1..=n in (line, col, operator) order
    let m = map::parse_map(a.as_bytes()).unwrap();
    let ids: Vec<u32> = m.rows.iter().map(|r| r.id).collect();
    assert_eq!(ids, (1..=m.count).collect::<Vec<_>>());
    let lines: Vec<usize> = m.rows.iter().map(|r| r.line).collect();
    let mut sorted = lines.clone();
    sorted.sort();
    assert_eq!(lines, sorted);
}

#[test]
fn operators_and_rewrite() {
    let out = mutate_sources(&files(), &HashMap::new(), &HashSet::new()).unwrap();
    let ops: BTreeSet<&str> = out.mutants.iter().map(|m| m.op).collect();
    for op in [
        "cond-true",
        "cond-false",
        "cond-negate",
        "and-or-swap",
        "decision-negate",
        "delete-stmt",
        "skip-err-return",
        "container-len-plus1",
        "option-get-none",
        "enum-variant",
        "drop-try",
        "const-plus1",
        "rel-boundary",
        "ret-negate",
        "container-first-last",
        "option-unwrap-or-default",
        "err-to-ok",
    ] {
        assert!(ops.contains(op), "missing operator {}: {:?}", op, ops);
    }
    let src = &out.sources[0];
    // line numbers do not change, and the result still parses
    assert_eq!(src.lines().count(), SRC.lines().count());
    syn::parse_file(src).unwrap();
    assert!(src.contains("crate::__mut::guard("));
    // the mutant rewriter itself records no MC/DC (the MC/DC edits are applied with it)
    assert!(!src.contains("__mcdc"));
}

#[test]
fn manifest_ids_are_reused() {
    // the `a && b` decision starts at line 5, column 8 (1-based)
    let mut man = HashMap::new();
    man.insert(("vir/src/sample.rs".to_string(), 5, 8), 42u32);
    let out = mutate_sources(&files(), &man, &HashSet::new()).unwrap();
    let d = out.decisions.iter().find(|d| d.line == 5).unwrap();
    assert_eq!(d.id, 42);
    assert!(d.mcdc);
    assert!(out.decisions.iter().filter(|d| d.id != 42).all(|d| d.id >= FIRST_LOCAL_DECISION));
    assert_eq!(out.manifest_ids_used, 1);
    // condition mutants of that decision name it
    assert!(out.mutants.iter().any(|m| m.atom_decision.map(|x| x.0) == Some(42)));
}

#[test]
fn disable_list_removes_points() {
    let all = mutate_sources(&files(), &HashMap::new(), &HashSet::new()).unwrap();
    let mut dis = HashSet::new();
    dis.insert("vir/src/sample.rs:6@delete-stmt".to_string());
    dis.insert("vir/src/sample.rs:15".to_string());
    let some = mutate_sources(&files(), &HashMap::new(), &dis).unwrap();
    assert!(!some.mutants.iter().any(|m| m.line == 6 && m.op == "delete-stmt"));
    assert!(!some.mutants.iter().any(|m| m.line == 15));
    assert!(some.mutants.len() < all.mutants.len());
    assert!(some.points_disabled >= 2);
}

fn sample_map() -> map::Map {
    let t = tsv_of(&HashSet::new(), &HashMap::new());
    map::parse_map(t.as_bytes()).unwrap()
}

#[test]
fn bitset_round_trip() {
    let m = sample_map();
    let ids: BTreeSet<u32> = [1, 7, m.count].into_iter().collect();
    let b = map::bitset(&m, &ids);
    assert_eq!(&b[0..8], b"VMUTBS01");
    assert_eq!(b.len(), 60 + (m.count as usize + 1).div_ceil(8));
    let (commit, count, digest, back) = map::read_bitset(&b).unwrap();
    assert_eq!(commit, m.commit);
    assert_eq!(count, m.count);
    assert_eq!(digest, m.digest);
    assert_eq!(back, ids);
    assert!(map::read_bitset(&b[..59]).is_err());
    let mut bad = b.clone();
    bad[0] = b'X';
    assert!(map::read_bitset(&bad).is_err());
}

#[test]
fn selector_filters() {
    let m = sample_map();
    let all = map::select(&m, &Selection::default()).unwrap();
    assert_eq!(all.len() as u32, m.count);
    let by_fn =
        map::select(&m, &Selection { fns: vec!["parse".into()], ..Default::default() }).unwrap();
    assert!(!by_fn.is_empty());
    assert!(by_fn.iter().all(|i| m.rows[*i as usize - 1].func.ends_with("::parse")));
    let by_loc = map::select(
        &m,
        &Selection { locs: vec![("vir/src/sample.rs".into(), 5)], ..Default::default() },
    )
    .unwrap();
    assert!(by_loc.iter().all(|i| m.rows[*i as usize - 1].line == 5));
    assert!(!by_loc.is_empty());
    // union of selectors, then class filter
    let u = map::select(
        &m,
        &Selection {
            fns: vec!["parse".into()],
            locs: vec![("vir/src/sample.rs".into(), 5)],
            ..Default::default()
        },
    )
    .unwrap();
    assert_eq!(u, by_fn.union(&by_loc).copied().collect());
    let cond =
        map::select(&m, &Selection { classes: vec!["condition".into()], ..Default::default() })
            .unwrap();
    assert!(cond.iter().all(|i| m.rows[*i as usize - 1].class == "condition"));
    let dp = map::select(&m, &Selection { classes: vec!["datapath".into()], ..Default::default() })
        .unwrap();
    assert!(
        !dp.is_empty() && dp.iter().all(|i| m.rows[*i as usize - 1].class.starts_with("datapath"))
    );
    let op =
        map::select(&m, &Selection { classes: vec!["delete-stmt".into()], ..Default::default() })
            .unwrap();
    assert!(op.iter().all(|i| m.rows[*i as usize - 1].op == "delete-stmt"));
    // random sample: reproducible, a subset, rate 0 and 1 are the extremes
    let r1 = map::select(&m, &Selection { random: Some((7, 0.5)), ..Default::default() }).unwrap();
    let r2 = map::select(&m, &Selection { random: Some((7, 0.5)), ..Default::default() }).unwrap();
    assert_eq!(r1, r2);
    assert!(r1.is_subset(&all));
    assert!(
        map::select(&m, &Selection { random: Some((7, 0.0)), ..Default::default() })
            .unwrap()
            .is_empty()
    );
    assert_eq!(
        map::select(&m, &Selection { random: Some((7, 1.0)), ..Default::default() }).unwrap(),
        all
    );
    // ids out of range are refused
    assert!(map::select(&m, &Selection { ids: vec![m.count + 1], ..Default::default() }).is_err());
    assert!(map::select(&m, &Selection { ids: vec![0], ..Default::default() }).is_err());
}

#[test]
fn map_digest_detects_changes() {
    let t = tsv_of(&HashSet::new(), &HashMap::new());
    let mut changed = t.clone().into_bytes();
    let k = changed.len() - 2;
    changed[k] = b'#';
    assert_ne!(map::fnv(t.as_bytes()), map::fnv(&changed));
    assert!(map::parse_map(b"# commit=abc count=1\nid\n").is_err());
}

// ---- one build with MC/DC and mutants in every file: same manifest and records as build A ----

const PROG_MAIN: &str = r#"use std::cell::RefCell;
mod m;
thread_local! { static LOG: RefCell<Vec<String>> = RefCell::new(Vec::new()); }
pub fn t(name: &str, v: bool) -> bool {
    LOG.with(|l| l.borrow_mut().push(format!("{}={}", name, v)));
    v
}
fn f(a: bool, b: bool, c: bool) -> bool {
    (t("a", a) && t("b", b)) || !t("c", c)
}
fn h(n: u32) -> u32 {
    let mut i = 0;
    while t("lt", i < n) && (t("even", i % 2 == 0) || t("small", i < 3)) {
        i += 1;
    }
    i
}
fn main() {
    for k in 0..8u32 {
        let (a, b, c) = (k & 4 != 0, k & 2 != 0, k & 1 != 0);
        let r = f(a, b, c);
        LOG.with(|l| l.borrow_mut().push(format!("f({},{},{})={}", a, b, c, r)));
    }
    for (p, x) in [(false, Some(1)), (true, None), (true, Some(-1)), (true, Some(5))] {
        let r = m::g(p, x);
        let s = m::k(x, p);
        LOG.with(|l| l.borrow_mut().push(format!("g={} k={}", r, s)));
    }
    let mut it = vec![Some(1u8), Some(4), None, Some(2)].into_iter();
    let n = m::w(true, &mut it);
    let r = h(6);
    LOG.with(|l| l.borrow_mut().push(format!("h={} w={}", r, n)));
    let v: Vec<u32> = (0..5).filter(|x| t("odd", x % 2 == 1) || t("zero", *x == 0)).collect();
    LOG.with(|l| l.borrow_mut().push(format!("v={:?}", v)));
    LOG.with(|l| for e in l.borrow().iter() { println!("{}", e) });
}
"#;

const PROG_M: &str = r#"use crate::t;
pub fn g(p: bool, x: Option<i32>) -> i32 {
    if t("p", p) && let Some(v) = x && t("q", v > 0) { v } else { -1 }
}
pub fn k(x: Option<i32>, p: bool) -> i32 {
    match x {
        Some(v) if t("gp", p) && let 1..=9 = v => v,
        Some(_) => 0,
        None => -1,
    }
}
pub fn w(a: bool, it: &mut std::vec::IntoIter<Option<u8>>) -> u32 {
    let mut n = 0;
    while t("wa", a) && let Some(Some(v)) = it.next() {
        n += v as u32;
    }
    n
}
"#;

fn write_tree(root: &std::path::Path) {
    let src = root.join("t").join("src");
    std::fs::create_dir_all(&src).unwrap();
    std::fs::write(src.join("main.rs"), PROG_MAIN).unwrap();
    std::fs::write(src.join("m.rs"), PROG_M).unwrap();
}

fn compile_run(root: &std::path::Path, records: &std::path::Path) -> String {
    let exe = root.join("prog");
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let st = std::process::Command::new(rustc)
        .args(["--edition", "2024", "-O", "-o"])
        .arg(&exe)
        .arg(root.join("t/src/main.rs"))
        .status()
        .unwrap();
    assert!(st.success(), "rustc failed in {}", root.display());
    let o = std::process::Command::new(&exe).env("MCDC_DIR", records).output().unwrap();
    assert!(o.status.success());
    String::from_utf8_lossy(&o.stdout).to_string()
}

#[test]
fn all_files_mutant_build_has_the_mcdc_of_build_a() {
    use mcdc::{analyze, instrument, mutate};
    let dir = std::env::temp_dir().join(format!("mcdc-ab-test-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let (a, b) = (dir.join("a"), dir.join("b"));
    write_tree(&a);
    write_tree(&b);
    let crates = vec!["t".to_string()];
    let (man_a, _) = instrument::instrument_tree(&a, &crates).unwrap();
    // every file of the crate is mutated (no --files), with no mutant switched on
    let r = mutate::mutate_tree(&b, &crates, None, &HashSet::new(), &"0".repeat(40), true).unwrap();
    assert!(r.out.mutants.len() > 50);
    assert!(r.out.mutants.iter().any(|m| m.file == "t/src/main.rs"));
    assert!(r.out.mutants.iter().any(|m| m.file == "t/src/m.rs"));
    // same manifest
    let js =
        |d: &[mcdc::manifest::Decision]| d.iter().map(|x| format!("{:?}", x)).collect::<Vec<_>>();
    assert_eq!(js(&man_a), js(&r.manifest));
    // same output and same records
    let (ra, rb) = (dir.join("rec-a"), dir.join("rec-b"));
    let out_a = compile_run(&a, &ra);
    let out_b = compile_run(&b, &rb);
    assert_eq!(out_a, out_b);
    let (da, db) = (analyze::load(&[ra]).unwrap(), analyze::load(&[rb]).unwrap());
    assert_eq!(da, db);
    // the let-chain decisions of the mutated files (if, while, match guard) have records
    for kind in ["if-letchain", "while-letchain", "guard-letchain"] {
        let d = r.manifest.iter().find(|d| d.kind == kind).unwrap();
        assert!(d.file == "t/src/m.rs");
        assert!(db.get(&d.id).map_or(0, |s| s.len()) >= 2, "no records for {} {}", kind, d.id);
    }
    assert_eq!(da.len(), man_a.len(), "every decision of the sample is evaluated");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn map_records_the_merge_base_not_head() {
    let dir = std::env::temp_dir().join(format!("mcdc-base-test-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("vir/src")).unwrap();
    let git = |args: &[&str]| {
        let o = std::process::Command::new("git")
            .arg("-C")
            .arg(&dir)
            .args(["-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false"])
            .args(args)
            .output()
            .unwrap();
        assert!(o.status.success(), "git {:?}: {}", args, String::from_utf8_lossy(&o.stderr));
        String::from_utf8_lossy(&o.stdout).trim().to_string()
    };
    git(&["init", "-q"]);
    std::fs::write(dir.join("vir/src/lib.rs"), "pub fn f() {}\n").unwrap();
    git(&["add", "."]);
    git(&["commit", "-q", "-m", "upstream"]);
    let base = git(&["rev-parse", "HEAD"]);
    git(&["branch", "upstream-main"]);
    std::fs::create_dir_all(dir.join("tools")).unwrap();
    std::fs::write(dir.join("tools/x.txt"), "tool\n").unwrap();
    git(&["add", "."]);
    git(&["commit", "-q", "-m", "tool"]);
    let head = git(&["rev-parse", "HEAD"]);
    assert_ne!(base, head);
    let crates = vec!["vir".to_string()];
    let (c, differs) = mcdc::cli::base_commit(&dir, "upstream-main", &crates).unwrap();
    assert_eq!(c, base);
    assert!(!differs);
    // a change to the verifier crates is reported
    std::fs::write(dir.join("vir/src/lib.rs"), "pub fn g() {}\n").unwrap();
    let (c2, differs2) = mcdc::cli::base_commit(&dir, "upstream-main", &crates).unwrap();
    assert_eq!(c2, base);
    assert!(differs2);
    assert!(mcdc::cli::base_commit(&dir, "no-such-ref", &crates).is_err());
    let _ = std::fs::remove_dir_all(&dir);
}
