//! Rewriter tests: the output parses, keeps line numbers, keeps the operators (so evaluation order
//! and short-circuiting are unchanged), and, compiled and run, prints the same side effects in the
//! same order as the original while recording the expected atom vectors.

use mcdc::analyze::{self, eval_tree, parse_tree};
use mcdc::instrument::{RUNTIME, RUNTIME_FILE, Stats, instrument_source};
use mcdc::manifest::Decision;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

fn rewrite(src: &str, is_root: bool) -> (String, Vec<Decision>, Stats) {
    let mut next_id = 1;
    let mut decisions = Vec::new();
    let mut stats = Stats::default();
    let out = instrument_source(
        src,
        "t/src/lib.rs",
        "t",
        is_root,
        &mut next_id,
        &mut decisions,
        &mut stats,
    )
    .unwrap()
    .unwrap_or_else(|| src.to_string());
    (out, decisions, stats)
}

/// Removes every `&&` and `||` that the rewriter added; what remains, in order, must be the
/// original operators.
fn logic_ops(src: &str) -> Vec<&'static str> {
    let b = src.as_bytes();
    let mut v = Vec::new();
    let mut i = 0;
    while i + 1 < b.len() {
        match &b[i..i + 2] {
            b"&&" => {
                v.push("&&");
                i += 2;
            }
            b"||" => {
                v.push("||");
                i += 2;
            }
            _ => i += 1,
        }
    }
    v
}

#[test]
fn output_parses_and_keeps_lines() {
    let src = "\
fn f(a: bool, b: bool, c: bool, x: Option<u8>) -> bool {
    let y = a && (b || !c);
    if !(a || b) && c {
        return y;
    }
    match x {
        Some(k) if k > 3 && a => true,
        _ => {
            while a && b { break; }
            let g = |p: bool| p || c;
            g(a) && f(b, c, a, None)
        }
    }
}
";
    let (out, decs, stats) = rewrite(src, false);
    syn::parse_file(&out).expect("rewritten code parses");
    assert_eq!(out.lines().count(), src.lines().count());
    assert_eq!(stats.decisions, 6);
    let kinds: Vec<&str> = decs.iter().map(|d| d.kind.as_str()).collect();
    assert_eq!(kinds, ["let", "if", "guard", "while", "closure", "expr"]);
    let lines: Vec<usize> = decs.iter().map(|d| d.line).collect();
    assert_eq!(lines, [2, 3, 7, 9, 10, 11]);
    assert_eq!(decs[0].tree, "(0&&(1||2))");
    assert_eq!(decs[0].atoms.iter().map(|a| a.text.as_str()).collect::<Vec<_>>(), ["a", "b", "!c"]);
    assert_eq!(decs[1].tree, "(!(0||1)&&2)");
    // the rewriter adds no && or || of its own outside let-chains
    assert_eq!(logic_ops(&out), logic_ops(src));
}

#[test]
fn nested_decisions_are_separate() {
    let src =
        "fn f(a: bool, b: bool, c: bool) -> bool { a && g(b || c) }\nfn g(x: bool) -> bool { x }\n";
    let (out, decs, _) = rewrite(src, false);
    syn::parse_file(&out).unwrap();
    assert_eq!(decs.len(), 2);
    assert_eq!(decs[0].atoms[1].text, "g(b || c)");
    assert_eq!(decs[1].text, "b || c");
}

#[test]
fn skipped_positions() {
    let src = "\
const C: bool = true && false;
const fn k(a: bool, b: bool) -> bool { a && b }
fn f(a: bool, x: Option<u8>) -> u8 {
    assert!(a || !a);
    let _ = [0u8; (1 > 0 && 2 > 1) as usize];
    x.map_or(0, |v| v)
}
";
    let (out, decs, stats) = rewrite(src, false);
    assert!(decs.is_empty());
    assert_eq!(out, src);
    assert_eq!(stats.skipped_const, 2);
    assert_eq!(stats.macro_logic_ops, 1);
    assert_eq!(stats.skipped_letchain, 0);
}

#[test]
fn let_chain_in_match_guard() {
    let src = "\
fn f(a: bool, x: Option<u8>) -> u8 {
    match x {
        Some(v) if a && let 3 = v => 1,
        Some(_) => 2,
        _ => 0,
    }
}
";
    let (out, decs, stats) = rewrite(src, false);
    syn::parse_file(&out).unwrap();
    assert_eq!(out.lines().count(), src.lines().count());
    assert_eq!(stats.letchains, 1);
    assert_eq!(stats.skipped_letchain, 0);
    assert_eq!(decs[0].kind, "guard-letchain");
    assert_eq!(decs[0].tree, "(0&&1)");
    // every arm body ends the pending guard evaluation
    assert_eq!(out.matches("crate::__mcdc::g_end(1, ").count(), 3);
}

#[test]
fn let_chain_in_if_and_while() {
    let src = "\
fn f(a: bool, x: Option<u8>, mut it: std::vec::IntoIter<u8>) -> u8 {
    if a && let Some(v) = x && v > 2 { v } else { 0 };
    while a && let Some(v) = it.next() { let _ = v; }
    0
}
";
    let (out, decs, stats) = rewrite(src, false);
    syn::parse_file(&out).unwrap();
    assert_eq!(out.lines().count(), src.lines().count());
    assert_eq!(stats.letchains, 2);
    assert_eq!(decs[0].kind, "if-letchain");
    assert_eq!(decs[0].tree, "((0&&1)&&2)");
    assert_eq!(decs[1].kind, "while-letchain");
}

#[test]
fn refuses_instrumented_input() {
    let (out, _, _) = rewrite("fn f(a: bool, b: bool) -> bool { a && b }\n", false);
    let mut stats = Stats::default();
    let r = instrument_source(&out, "x.rs", "t", false, &mut 1, &mut Vec::new(), &mut stats);
    assert!(r.is_err());
}

const PROGRAM: &str = r#"use std::cell::RefCell;
thread_local! { static LOG: RefCell<Vec<String>> = RefCell::new(Vec::new()); }
fn t(name: &str, v: bool) -> bool {
    LOG.with(|l| l.borrow_mut().push(format!("{}={}", name, v)));
    v
}
fn f(a: bool, b: bool, c: bool) -> bool {
    (t("a", a) && t("b", b)) || !t("c", c)
}
fn g(p: bool, x: Option<i32>) -> i32 {
    if t("p", p) && let Some(v) = x && t("q", v > 0) { v } else { -1 }
}
fn h(n: u32) -> u32 {
    let mut i = 0;
    while t("lt", i < n) && (t("even", i % 2 == 0) || t("small", i < 3)) {
        i += 1;
    }
    i
}
fn k(x: Option<i32>, p: bool) -> i32 {
    match x {
        Some(v) if t("gp", p) && let 1..=9 = v => v,
        Some(_) => 0,
        None => -1,
    }
}
fn main() {
    for (x, p) in [(Some(3), false), (Some(3), true), (Some(20), true), (None, true)] {
        let r = k(x, p);
        LOG.with(|l| l.borrow_mut().push(format!("k={}", r)));
    }
    for k in 0..8u32 {
        let (a, b, c) = (k & 4 != 0, k & 2 != 0, k & 1 != 0);
        let r = f(a, b, c);
        LOG.with(|l| l.borrow_mut().push(format!("f({},{},{})={}", a, b, c, r)));
    }
    for (p, x) in [(false, Some(1)), (true, None), (true, Some(-1)), (true, Some(5))] {
        let r = g(p, x);
        LOG.with(|l| l.borrow_mut().push(format!("g={}", r)));
    }
    let r = h(6);
    LOG.with(|l| l.borrow_mut().push(format!("h={}", r)));
    LOG.with(|l| for e in l.borrow().iter() { println!("{}", e) });
}
"#;

fn rustc() -> String {
    std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string())
}

fn compile(dir: &Path, name: &str) -> PathBuf {
    let exe = dir.join(format!("{}-bin", name));
    let st = Command::new(rustc())
        .args(["--edition", "2024", "-O", "-o"])
        .arg(&exe)
        .arg(dir.join(format!("{}.rs", name)))
        .status()
        .expect("run rustc");
    assert!(st.success(), "rustc failed on {}", name);
    exe
}

#[test]
fn rewritten_program_has_same_side_effects_and_records_vectors() {
    let dir = std::env::temp_dir().join(format!("mcdc-rewrite-test-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let (out, decs, _) = rewrite(PROGRAM, true);
    std::fs::write(dir.join("orig.rs"), PROGRAM).unwrap();
    std::fs::write(dir.join("inst.rs"), &out).unwrap();
    std::fs::write(dir.join(RUNTIME_FILE), RUNTIME).unwrap();
    let orig = compile(&dir, "orig");
    let inst = compile(&dir, "inst");
    let rec_dir = dir.join("records");
    let o1 = Command::new(&orig).output().unwrap();
    let o2 = Command::new(&inst).env("MCDC_DIR", &rec_dir).output().unwrap();
    assert!(o1.status.success() && o2.status.success());
    // Same side effects in the same order: every atom evaluation is logged by `t`.
    assert_eq!(String::from_utf8_lossy(&o1.stdout), String::from_utf8_lossy(&o2.stdout));
    assert!(o1.stdout.len() > 200);

    let data = analyze::load(&[rec_dir.clone()]).unwrap();
    let by_fn = |f: &str| decs.iter().find(|d| d.func == f).unwrap();
    // f: all 8 assignments were run; the records are exactly the short-circuit evaluations.
    let df = by_fn("f");
    let tree = parse_tree(&df.tree).unwrap();
    let mut expect = BTreeSet::new();
    for k in 0..8u32 {
        let asg = [k & 4 != 0, k & 2 != 0, k & 1 != 0];
        let mut evd = vec![None; 3];
        let o = eval_tree(&tree, &asg, &mut evd);
        let mut v = 0u128;
        for (i, b) in evd.iter().enumerate() {
            if let Some(b) = b {
                v |= (if *b { 3 } else { 1 }) << (2 * i);
            }
        }
        expect.insert((o, v));
    }
    assert_eq!(data[&df.id], expect);
    assert_eq!(analyze::analyze(3, &data[&df.id]).mcdc.len(), 3);
    // g: let-chain. (F--)=>F, (TF-)=>F (pattern did not match), (TTF)=>F, (TTT)=>T.
    let dg = by_fn("g");
    let v = |p: &str| -> u128 {
        p.chars().enumerate().fold(0, |acc, (i, c)| match c {
            'T' => acc | 3 << (2 * i),
            'F' => acc | 1 << (2 * i),
            _ => acc,
        })
    };
    let expect_g: BTreeSet<(bool, u128)> =
        [(false, v("F--")), (false, v("TF-")), (false, v("TTF")), (true, v("TTT"))]
            .into_iter()
            .collect();
    assert_eq!(data[&dg.id], expect_g);
    assert_eq!(analyze::analyze(3, &data[&dg.id]).mcdc.len(), 3);
    // h: one record per loop test, including the final false one.
    let dh = by_fn("h");
    assert!(data[&dh.id].contains(&(false, v("TFF"))));
    assert!(data[&dh.id].contains(&(true, v("TT-"))));
    // k: let-chain in a match guard. (F-)=>F, (TT)=>T, (TF)=>F (pattern did not match).
    let dk = by_fn("k");
    assert_eq!(dk.kind, "guard-letchain");
    let expect_k: BTreeSet<(bool, u128)> =
        [(false, v("F-")), (true, v("TT")), (false, v("TF"))].into_iter().collect();
    assert_eq!(data[&dk.id], expect_k);
    let _ = std::fs::remove_dir_all(&dir);
}
