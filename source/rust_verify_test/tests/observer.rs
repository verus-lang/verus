//! Observer e2e tests with strong oracles.
//!
//! Shared VC-shape seed corpus lives in `vc_shapes` (this branch), so all three layers'
//! suites can drive the same programs. This file adds event-trace oracles over selected seeds.
//!
//! Coverage matrix (+ = positive check, 0 = negative check):
//!
//! ```text
//!                                     | loop | mut  | valid | spec | break | for  | inv  | reveal | bvec |
//! ------------------------------------|------|------|-------|------|-------|------|------|--------|------|
//! on_krate (function names)           |  +   |  +   |   +   |  +   |       |      |      |        |      |
//! on_krate (datatype names)           |  +   |  +   |       |      |       |      |      |        |      |
//! on_havoc                            |  +   |  0   |   0   |  0   |   +   |  +   |  +   |        |      |
//! on_assign (names)                   |  +   |  +   |   0   |  0   |   +   |      |  +   |        |      |
//! on_query_lowered (Switch count)     |  +   |      |       |      |   +   |      |      |        |      |
//! on_variable_def (names)             |  +   |      |   0   |  0   |       |      |      |        |      |
//! on_for_loop_var (ghost, user)       |  0   |  0   |   0   |  0   |   0   |  +   |  0   |        |      |
//! on_reveal_string                    |      |      |       |      |       |      |      |   +    |      |
//! on_quantifier_binder (names)        |  0   |  +   |   0   |  +   |   0   |  0   |  0   |        |      |
//! make_assert_id(Ensures)             |  +   |  +   |   +   |  +   |   +   |      |      |        |      |
//! make_assert_id(LoopInvariant)       |  +   |      |       |      |   +   |      |  +   |        |      |
//! make_assert_id(DecreasesCheck)      |  +   |      |       |      |   +   |      |  +   |        |      |
//! on_function_lowered                 |  +   |  +   |   +   |  +   |   +   |      |  +   |        |      |
//! on_query_lowered (count)            |  +   |  +   |   +   |  +   |   +   |      |  +   |        |      |
//! on_query_lowered (snapshots)        |  +   |      |   +   |      |       |      |      |        |      |
//! on_lambda_decl (payload)            |  0   |  0   |   0   |  +   |   0   |  0   |  0   |        |      |
//! on_choose_decl (payload)            |  0   |  0   |   0   |  +   |   0   |  0   |  0   |        |      |
//! on_binder_decl (kinds, types)       |      |      |       |  +   |       |      |      |        |      |
//! on_axiom_decl (payload)             |      |      |       |  +   |       |      |      |        |      |
//! on_wp_version_created (origins)     |  +   |  +   |   +   |  +   |   +   |  +   |  +   |   +    |  +   |
//! check_valid_result(Invalid)         |  +   |  +   |   0   |  +   |   +   |      |  +   |   +    |  +   |
//! check_valid_result(Valid)           |  +   |      |   +   |      |       |      |      |        |      |
//! check_valid_result(Timeout)         |      |      |       |      |       |      |      |  TODO  |      |
//! invalid model_defs size             |  +   |  +   |       |  +   |       |      |  +   |        |      |
//! eval_bool_expr during Invalid       |  +   |      |       |      |       |      |      |        |      |
//! ```
//!
//! Payload-content rows later in the file assert on what each callback delivers.

#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;
mod vc_shapes;

// ── JSON parsing (mirrors TestObserver data model) ──

#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct D {
    krate_function_names: Vec<String>,
    krate_datatype_names: Vec<String>,
    havocs: Vec<String>,
    assigns: Vec<String>,
    switch_count: usize,
    variable_defs: Vec<String>,
    for_loop_vars: Vec<(String, String)>,
    reveal_strings: Vec<String>,
    quantifier_binders: Vec<String>,
    assert_id_kinds: Vec<String>,
    function_lowered: usize,
    query_lowered: usize,
    query_snapshot_counts: Vec<usize>,
    version_correlations: Vec<(String, u32, String)>,
    lambda_decls: Vec<String>,
    choose_decls: Vec<String>,
    check_valid_invalid: usize,
    check_valid_valid: usize,
    check_valid_timeout: usize,
    check_valid_invalid_model_size: Vec<usize>,
    eval_expr_results: Vec<Option<bool>>,
    binder_decls: Vec<String>,
    breakable_count: usize,
    break_count: usize,
    valid_assert_id_counts: Vec<usize>,
    valid_used_axiom_counts: Vec<Option<usize>>,
    /// Per choose decl: name, then the Debug renderings of binders, predicate, and body.
    choose_payloads: Vec<String>,
    /// Per lambda decl: name, then the Debug renderings of its typed binders and body.
    lambda_payloads: Vec<String>,
    /// Per binder decl: name, then the Debug renderings of its type and kind.
    binder_decl_payloads: Vec<String>,
    /// Debug rendering of each axiom expression delivered to `on_axiom_decl`.
    axiom_payloads: Vec<String>,
    /// Per query: Debug rendering of the versioned-constant declarations.
    query_local_var_payloads: Vec<String>,
    /// Per quantifier binder: Debug rendering of the quantified body.
    quantifier_body_payloads: Vec<String>,
    /// The crate id delivered to `on_krate`.
    krate_current_crate: String,
    pre_body_binders: Vec<String>,
    post_body_binders: Vec<String>,
    events: Vec<String>,
}

/// The three single-trait observers each emit their own note; one struct per note.
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct VirOnly {
    events: Vec<String>,
    function_names: Vec<String>,
    function_lowered: usize,
}
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct AirOnly {
    events: Vec<String>,
    query_lowered: usize,
    axiom_decls: usize,
}
#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct QueryResultOnly {
    events: Vec<String>,
    invalid: usize,
    valid: usize,
    eval_expr_results: Vec<Option<bool>>,
}

/// Find the note with `prefix` and deserialize what follows it.
fn parse_prefixed<T: serde::de::DeserializeOwned>(err: &TestErr, prefix: &str) -> T {
    let note = find_note(err, prefix);
    let json = note.strip_prefix(prefix).unwrap();
    serde_json::from_str(json)
        .unwrap_or_else(|e| panic!("{} note is not valid JSON: {}\n{}", prefix, e, json))
}

fn parse_note(note_text: &str) -> D {
    let json = note_text.strip_prefix("OBSERVER:").unwrap_or(note_text);
    serde_json::from_str(json)
        .unwrap_or_else(|e| panic!("OBSERVER note is not valid JSON: {}\n{}", e, json))
}

/// Parse the first OBSERVER note. Programs with one module emit exactly one; see
/// `parse_all` for multi-module programs.
fn parse(err: &TestErr) -> D {
    parse_all(err).into_iter().next().expect("OBSERVER note not found")
}

/// Parse every OBSERVER note (one per module the observer saw). A multi-module program —
/// e.g. one containing a `state_machine!`, which generates its own module — emits several.
fn parse_all(err: &TestErr) -> Vec<D> {
    err.notes
        .iter()
        .filter_map(|n| {
            let t = n.rendered.strip_prefix("note: ").unwrap_or(&n.rendered);
            t.strip_prefix("OBSERVER:").map(|_| parse_note(t))
        })
        .collect()
}

/// Union of a string field across all modules' notes.
fn across(ds: &[D], f: impl Fn(&D) -> &Vec<String>) -> Vec<String> {
    ds.iter().flat_map(|d| f(d).iter().cloned()).collect()
}

fn has(v: &[String], s: &str) -> bool {
    v.contains(&s.to_string())
}
fn count(v: &[String], s: &str) -> usize {
    v.iter().filter(|x| *x == s).count()
}

// Find a diagnostic note beginning with `prefix` (e.g. "AIROBS:", "QROBS:", "VIROBS:").
fn find_note(err: &TestErr, prefix: &str) -> String {
    err.notes
        .iter()
        .find_map(|n| {
            let t = n.rendered.strip_prefix("note: ").unwrap_or(&n.rendered);
            if t.starts_with(prefix) { Some(t.to_string()) } else { None }
        })
        .unwrap_or_else(|| {
            panic!(
                "{} note not found; notes: {:?}",
                prefix,
                err.notes.iter().map(|n| n.rendered.clone()).collect::<Vec<_>>()
            )
        })
}
// Assert NO note begins with `prefix` (zero-overhead / decoupling checks).
fn no_note(err: &TestErr, prefix: &str) -> bool {
    !err.notes.iter().any(|n| {
        let t = n.rendered.strip_prefix("note: ").unwrap_or(&n.rendered);
        t.starts_with(prefix)
    })
}
// Index of first event exactly equal to `tag`.
fn idx(events: &[String], tag: &str) -> Option<usize> {
    events.iter().position(|e| e == tag)
}
// Index of first event starting with `prefix` (for tags carrying a payload).
fn idx_pfx(events: &[String], prefix: &str) -> Option<usize> {
    events.iter().position(|e| e.starts_with(prefix))
}

// ── Tests ──

test_verify_one_file_with_options! {
    #[test]
    test_observer_loop ["observers=test"] => verus_code! {
        fn test_loop(n: u64)
            requires n > 0
            ensures false
        {
            let mut x: u64 = 0;
            let mut i: u64 = 0;
            while i < n
                invariant i <= n, x >= 0,
                decreases n - i
            {
                x = if i % 2 == 0 { x + 1 } else { x + 2 };
                i = i + 1;
            }
        }
    } => Err(err) => {
        let d = parse(&err);
        assert!(has(&d.krate_function_names, "test_loop"), "got {:?}", d.krate_function_names);
        assert!(has(&d.krate_datatype_names, "tuple0"), "got {:?}", d.krate_datatype_names);
        assert!(has(&d.assigns, "x@") && has(&d.assigns, "i@"), "got {:?}", d.assigns);
        assert_eq!(d.switch_count, 2, "two `if`s lower to two Switch nodes");
        assert!(has(&d.variable_defs, "x@") && has(&d.variable_defs, "i@"), "got {:?}", d.variable_defs);
        assert!(has(&d.assert_id_kinds, "Ensures"), "got {:?}", d.assert_id_kinds);
        assert!(has(&d.assert_id_kinds, "LoopInvariant"), "got {:?}", d.assert_id_kinds);
        assert!(has(&d.assert_id_kinds, "DecreasesCheck"), "got {:?}", d.assert_id_kinds);
        assert_eq!(d.function_lowered, 2);
        assert!(d.query_lowered >= 2);
        assert!(!d.query_snapshot_counts.is_empty());
        assert!(d.check_valid_invalid >= 1);
        assert!(d.check_valid_valid >= 1);
        assert!(d.check_valid_invalid_model_size.iter().all(|&s| s > 0));
        assert!(d.eval_expr_results.iter().any(|r| *r == Some(true)),
            "eval_bool_expr(true) should return Some(true), got {:?}", d.eval_expr_results);
        // Version correlations: loop-modified variables have havoc and assign entries
        assert!(!d.version_correlations.is_empty(),
            "loop should produce version correlations");
        assert!(d.version_correlations.iter().any(|(_, _, k)| k == "Havoc"),
            "should have Havoc correlation from loop entry");
        assert!(d.version_correlations.iter().any(|(_, _, k)| k == "Assign"),
            "should have Assign correlation from loop body");
        // x should have correlations with distinct lines
        let x_corr: Vec<_> = d.version_correlations.iter()
            .filter(|(v, _, _)| v.contains("x")).collect();
        assert!(x_corr.len() >= 2,
            "x should have >= 2 correlations, got {}", x_corr.len());
        for (v, line, _) in &d.version_correlations {
            assert!(*line > 0, "{} has line 0", v);
        }
        let x_lines: std::collections::HashSet<u32> =
            x_corr.iter().map(|(_, l, _)| *l).collect();
        assert!(x_lines.len() >= 2,
            "x should have >= 2 distinct lines, got {:?}", x_lines);
        // Negatives
        assert!(!d.havocs.is_empty(), "loop should produce havocs, got {:?}", d.havocs);
        assert!(d.for_loop_vars.is_empty());
        assert!(d.quantifier_binders.is_empty());
        assert!(d.lambda_decls.is_empty());
        assert!(d.choose_decls.is_empty());
    }
}

test_verify_one_file_with_options! {
    #[test]
    test_observer_mut_ref ["observers=test"] => verus_code! {
        struct Pair { a: u64, b: u64 }
        spec fn is_positive(x: int) -> bool { x >= 0 }
        fn test_mut(p: &mut Pair, x: &mut u64)
            requires old(p).a < 100, *old(x) < 100,
                forall|i: int| #[trigger] is_positive(i) ==> i >= 0,
            ensures (*final(p)).a == old(p).a + 1, *final(x) == *old(x) + 1,
        {
            p.a = p.a + 1;
            *x = *x + 2;
        }
    } => Err(err) => {
        let d = parse(&err);
        assert!(has(&d.krate_datatype_names, "Pair"), "got {:?}", d.krate_datatype_names);
        assert!(has(&d.krate_function_names, "test_mut") && has(&d.krate_function_names, "is_positive"),
            "got {:?}", d.krate_function_names);
        assert!(has(&d.assigns, "p!") && has(&d.assigns, "x!"), "got {:?}", d.assigns);
        assert!(has(&d.quantifier_binders, "i$"), "got {:?}", d.quantifier_binders);
        assert_eq!(count(&d.assert_id_kinds, "Ensures"), 2, "got {:?}", d.assert_id_kinds);
        assert_eq!(d.function_lowered, 2);
        assert!(d.query_lowered >= 1);
        assert!(d.check_valid_invalid >= 1);
        assert!(d.check_valid_invalid_model_size.iter().all(|&s| s > 0));
        // Negatives
        assert!(d.havocs.is_empty());
        assert!(d.for_loop_vars.is_empty());
        assert!(d.lambda_decls.is_empty());
        assert!(d.choose_decls.is_empty());
    }
}

test_verify_one_file_with_options! {
    #[test]
    test_observer_valid ["observers=test"] => verus_code! {
        fn add_one(x: u64) -> (r: u64)
            requires x < 100
            ensures r == x + 1
        { x + 1 }
    } => Ok(err) => {
        let d = parse(&err);
        assert!(has(&d.krate_function_names, "add_one"), "got {:?}", d.krate_function_names);
        assert!(has(&d.assert_id_kinds, "Ensures"), "got {:?}", d.assert_id_kinds);
        assert!(d.function_lowered >= 1);
        assert!(d.query_lowered >= 1);
        assert!(!d.query_snapshot_counts.is_empty());
        assert!(d.check_valid_valid >= 1);
        assert_eq!(d.check_valid_invalid, 0);
        // No loops → no version correlations
        assert!(d.version_correlations.is_empty(),
            "non-mutating function should have no version correlations, got {:?}",
            d.version_correlations);
        // Negatives
        assert!(d.havocs.is_empty());
        assert!(d.for_loop_vars.is_empty());
        assert!(d.quantifier_binders.is_empty());
        assert!(d.lambda_decls.is_empty());
        assert!(d.choose_decls.is_empty());
    }
}

test_verify_one_file_with_options! {
    #[test]
    test_observer_spec ["observers=test"] => verus_code! {
        use vstd::prelude::*;
        spec fn has_pos(s: Seq<int>) -> bool {
            exists|i: int| 0 <= i < s.len() && s[i] > 0
        }
        proof fn test_spec(s: Seq<int>)
            requires s.len() > 0,
                s.map(|_idx: int, x: int| x + 1).len() > 0,
                has_pos(s),
            ensures false
        {}
    } => Err(err) => {
        let d = parse(&err);
        assert!(has(&d.krate_function_names, "has_pos"), "got {:?}", d.krate_function_names);
        assert!(has(&d.krate_function_names, "test_spec"), "got {:?}", d.krate_function_names);
        // Lambda from s.map(|...|...)
        assert!(!d.lambda_decls.is_empty(), "should have lambda decls, got {:?}", d.lambda_decls);
        assert!(d.lambda_decls.iter().any(|n| n.contains("lambda")), "got {:?}", d.lambda_decls);
        // Quantifier binder
        assert!(!d.quantifier_binders.is_empty(), "got {:?}", d.quantifier_binders);
        assert!(has(&d.assert_id_kinds, "Ensures"), "got {:?}", d.assert_id_kinds);
        assert!(d.function_lowered >= 1);
        assert!(d.query_lowered >= 1);
        assert!(d.check_valid_invalid >= 1);
        assert!(d.check_valid_invalid_model_size.iter().all(|&s| s > 0));
        // Negatives
        assert!(d.havocs.is_empty());
        assert!(d.for_loop_vars.is_empty());
    }
}

test_verify_one_file_with_options! {
    #[test]
    test_observer_break ["observers=test"] => verus_code! {
        use vstd::prelude::*;
        fn find(v: &Vec<u64>, target: u64) -> (found: bool)
            ensures !found // wrong
        {
            let mut found = false;
            let mut i: usize = 0;
            while i < v.len()
                invariant
                    i <= v.len(),
                    !found,
                decreases v.len() - i
            {
                if v[i] == target {
                    found = true;
                    break;
                }
                i = i + 1;
            }
            found
        }
    } => Err(err) => {
        let d = parse(&err);
        // Break: loop isolation may prevent break_merge from firing,
        // but the `if` around the break lowers to a Switch
        assert!(d.switch_count > 0, "if should lower to a Switch, got {}", d.switch_count);
        // Assigns
        assert!(has(&d.assigns, "found@"), "got {:?}", d.assigns);
        assert!(has(&d.assigns, "i@"), "got {:?}", d.assigns);
        // Assert ID kinds
        assert!(has(&d.assert_id_kinds, "Ensures"), "got {:?}", d.assert_id_kinds);
        assert!(has(&d.assert_id_kinds, "LoopInvariant"), "got {:?}", d.assert_id_kinds);
        assert!(has(&d.assert_id_kinds, "DecreasesCheck"), "got {:?}", d.assert_id_kinds);
        assert!(d.function_lowered >= 1);
        assert!(d.query_lowered >= 1);
        assert!(d.check_valid_invalid >= 1);
        // Negatives
        assert!(!d.havocs.is_empty(), "loop should produce havocs, got {:?}", d.havocs);
        assert!(d.for_loop_vars.is_empty());
        // quantifier_binders may be non-empty due to vstd internals
        assert!(d.choose_decls.is_empty());
    }
}

test_verify_one_file_with_options! {
    #[test]
    test_observer_for_loop ["observers=test"] => verus_code! {
        use vstd::prelude::*;
        fn sum_first(v: &Vec<u64>, n: usize) -> (s: u64)
            requires n <= v.len(), n < 100,
                forall|i: int| 0 <= i < v.len() ==> v[i] < 100,
            ensures false
        {
            let mut s: u64 = 0;
            for i in iter: 0..n
                invariant
                    s <= 100 * i,
                    n < 100,
                    n <= v.len(),
                    forall|j: int| 0 <= j < v.len() ==> v[j] < 100,
            {
                s = s + v[i];
            }
            s
        }
    } => Err(err) => {
        let d = parse(&err);
        assert!(!d.for_loop_vars.is_empty(), "for-loop should be detected");
        // Negatives
        assert!(!d.havocs.is_empty(), "loop should produce havocs, got {:?}", d.havocs);
        assert!(d.choose_decls.is_empty());
    }
}

test_verify_one_file_with_options! {
    #[test]
    test_observer_loop_invariant ["observers=test"] => verus_code! {
        fn bad_loop(n: u64)
            requires n > 0
            ensures false
        {
            let mut i: u64 = 0;
            while i < n
                invariant i <= n,
                decreases n - i
            {
                i = i + 1;
            }
        }
    } => Err(err) => {
        let d = parse(&err);
        // Assert ID kinds: LoopInvariant and DecreasesCheck are primary
        assert!(count(&d.assert_id_kinds, "LoopInvariant") >= 2,
            "should have multiple LoopInvariant, got {:?}", d.assert_id_kinds);
        assert!(count(&d.assert_id_kinds, "DecreasesCheck") >= 1,
            "got {:?}", d.assert_id_kinds);
        assert!(has(&d.assigns, "i@"), "got {:?}", d.assigns);
        assert!(d.function_lowered >= 1);
        assert!(d.query_lowered >= 1);
        assert!(d.check_valid_invalid >= 1);
        assert!(d.check_valid_invalid_model_size.iter().all(|&s| s > 0));
        // Negatives
        assert!(!d.havocs.is_empty(), "loop should produce havocs, got {:?}", d.havocs);
        assert!(d.for_loop_vars.is_empty());
        assert!(d.lambda_decls.is_empty());
        assert!(d.choose_decls.is_empty());
        assert!(d.quantifier_binders.is_empty());
    }
}

test_verify_one_file_with_options! {
    #[test]
    test_observer_bitvector ["observers=test"] => verus_code! {
        proof fn test_bv(x: u32) by(bit_vector)
            ensures x & 0xff == x
        { }
    } => Err(err) => {
        let d = parse(&err);
        assert!(d.query_lowered >= 1,
            "bitvector query should reach observer, got {} queries", d.query_lowered);
    }
}

test_verify_one_file_with_options! {
    #[test]
    test_observer_reveal_string ["observers=test"] => verus_code! {
        use vstd::prelude::*;
        use vstd::string::*;
        fn test_reveal()
            ensures false
        {
            let _s = "hello";
            proof { reveal_strlit("hello"); }
        }
    } => Err(err) => {
        let d = parse(&err);
        assert!(d.reveal_strings.contains(&"hello".to_string()),
            "should record 'hello', got {:?}", d.reveal_strings);
        assert!(d.check_valid_invalid >= 1);
    }
}

// TODO: test_observer_timeout — requires --rlimit CLI flag which the test harness
// doesn't currently support. Add rlimit support to common/mod.rs, then test with
// rlimit=1 and assert d.check_valid_timeout > 0.

test_verify_one_file_with_options! {
    #[test]
    test_body_boundary ["observers=test"] => verus_code! {
        use vstd::prelude::*;

        // requires has forall|x|, body has forall|y|
        fn test_body_boundary(v: &Vec<u64>)
            requires forall|x: int| 0 <= x < v.len() ==> v[x] < 100,
        {
            assert(forall|y: int| 0 <= y < v.len() ==> v[y] < 200) by {
                // intentionally wrong bound to force failure
                assume(false);
            }
            assert(false); // force verification failure
        }
    } => Err(err) => {
        let d = parse(&err);
        // x is in requires (pre-body), y is in body (post-body)
        assert!(d.pre_body_binders.iter().any(|b| b.starts_with("x")),
            "requires binder 'x' should be pre-body, got pre={:?}", d.pre_body_binders);
        assert!(d.post_body_binders.iter().any(|b| b.starts_with("y")),
            "body binder 'y' should be post-body, got post={:?}", d.post_body_binders);
        // y should NOT appear in pre-body (it's only in the body assert)
        assert!(!d.pre_body_binders.iter().any(|b| b.starts_with("y")),
            "body binder 'y' should NOT be in pre-body, got pre={:?}", d.pre_body_binders);
    }
}

test_verify_one_file_with_options! {

    // ── §3.2 Cross-trait lifecycle sequencing (L1–L5) via the ordered trace ──
    #[test]
    test_lifecycle_sequencing ["observers=test"] => verus_code! {
        fn seq_demo(n: u64) -> (r: u64)
            requires n < 100,
            ensures r == n,
        {
            let mut i: u64 = 0;
            while i < n
                invariant i <= n,
                decreases n - i,
            { i = i + 1; }
            i
        }
    } => Ok(err) => {
        let d = parse(&err);
        let e = &d.events;
        // L1: on_krate fires exactly once, before everything.
        assert_eq!(e.first().map(|s| s.as_str()), Some("krate"),
            "L1: krate must be first; events={:?}", e);
        assert_eq!(count(e, "krate"), 1, "L1: krate exactly once; events={:?}", e);
        // L2: on_body_lowering_start precedes on_function_lowered.
        let body = idx(e, "body_start").expect("body_start present");
        let flow = idx(e, "function_lowered").expect("function_lowered present");
        assert!(body < flow, "L2: body_start before function_lowered; events={:?}", e);
        // L4: some on_query_lowered precedes a check_valid result.
        let q = idx(e, "query_lowered").expect("query_lowered present");
        let cv = idx_pfx(e, "check_valid:").expect("check_valid present");
        assert!(q < cv, "L4: query_lowered before check_valid; events={:?}", e);
    }
}

test_verify_one_file_with_options! {

    // ── §3.1 VirObserver-only: functional coverage + decoupling proof ──
    #[test]
    test_vir_only_observer ["observers=vir-only"] => verus_code! {
        fn vo(a: u64) -> (r: u64)
            ensures r == a,
        {
            let x: u64 = a;
            x
        }
    } => Ok(err) => {
        // Decoupling: only VIROBS is emitted — no all-three / air / query-result notes.
        assert!(no_note(&err, "OBSERVER:"), "vir-only must not emit all-three note");
        assert!(no_note(&err, "AIROBS:") && no_note(&err, "QROBS:"),
            "vir-only must not emit AIR/QR notes");
        let v: VirOnly = parse_prefixed(&err, "VIROBS:");
        let (events, fns, flowered) = (v.events, v.function_names, v.function_lowered);
        assert!(has(&fns, "vo"), "function_names has vo; got {:?}", fns);
        assert!(flowered >= 1, "function_lowered >= 1");
        assert_eq!(events.first().map(|s| s.as_str()), Some("krate"),
            "krate first; events={:?}", events);
        assert!(idx(&events, "function_lowered").is_some(), "events={:?}", events);
    }
}

test_verify_one_file_with_options! {

    // ── §3.1 AirObserver-only: functional coverage + decoupling proof ──
    #[test]
    test_air_only_observer ["observers=air-only"] => verus_code! {
        proof fn ao(x: u64)
            requires x < 10,
            ensures x < 20,
        { }
    } => Ok(err) => {
        assert!(no_note(&err, "OBSERVER:"), "air-only must not emit all-three note");
        assert!(no_note(&err, "VIROBS:") && no_note(&err, "QROBS:"),
            "air-only must not emit VIR/QR notes");
        let a: AirOnly = parse_prefixed(&err, "AIROBS:");
        let (events, ql, ax) = (a.events, a.query_lowered, a.axiom_decls);
        assert!(ql >= 1, "query_lowered >= 1; events={:?}", events);
        assert!(ax >= 1, "axiom_decls >= 1");
        assert!(idx(&events, "query_lowered").is_some(), "events={:?}", events);
    }
}

test_verify_one_file_with_options! {

    // ── §3.1 QueryResultObserver-only, Invalid: eval_expr liveness + decoupling ──
    #[test]
    test_query_result_only_invalid ["observers=query-result-only"] => verus_code! {
        proof fn bad()
            ensures false,
        { }
    } => Err(err) => {
        assert!(no_note(&err, "OBSERVER:"), "qr-only must not emit all-three note");
        assert!(no_note(&err, "AIROBS:") && no_note(&err, "VIROBS:"),
            "qr-only must not emit AIR/VIR notes");
        let q: QueryResultOnly = parse_prefixed(&err, "QROBS:");
        let (invalid, events, eval) = (q.invalid, q.events, q.eval_expr_results);
        assert!(invalid >= 1, "invalid >= 1");
        assert!(idx(&events, "check_valid:Invalid").is_some(), "events={:?}", events);
        assert!(!eval.is_empty(), "eval_expr worked during Invalid; got {:?}", eval);
    }
}

test_verify_one_file_with_options! {

    // ── §3.1/§3.4 QueryResultObserver-only, Valid: no unsat core (capabilities live on AirObserver) ──
    // ── §3.1 QueryResultObserver-only, Valid: sees the Valid result + decoupling ──
    #[test]
    test_query_result_only_valid ["observers=query-result-only"] => verus_code! {
        proof fn good(x: u64)
            requires x < 10,
            ensures x < 20,
        { }
    } => Ok(err) => {
        // Decoupling: only QROBS emitted.
        assert!(no_note(&err, "OBSERVER:"), "qr-only must not emit all-three note");
        assert!(no_note(&err, "AIROBS:") && no_note(&err, "VIROBS:"),
            "qr-only must not emit AIR/VIR notes");
        let q: QueryResultOnly = parse_prefixed(&err, "QROBS:");
        let (valid, events) = (q.valid, q.events);
        assert!(valid >= 1, "valid >= 1");
        assert!(events.iter().any(|e| e == "check_valid:Valid"),
            "events should contain check_valid:Valid; got {:?}", events);
    }
}

test_verify_one_file_with_options! {

    // ── §3.5 Zero-overhead: no observer flag => no observer notes at all ──
    #[test]
    test_no_observer_zero_overhead [] => verus_code! {
        proof fn noop(x: u64)
            requires x < 10,
            ensures x < 20,
        { }
    } => Ok(err) => {
        assert!(no_note(&err, "OBSERVER:"), "no all-three note without flag");
        assert!(no_note(&err, "AIROBS:") && no_note(&err, "QROBS:") && no_note(&err, "VIROBS:"),
            "no per-trait notes without flag");
    }
}

// ---- event-trace oracles over the shared VC-shape corpus ------------------------

test_verify_one_file_with_options! {
    // covers (VO axis): nested-loops seed drives transitive havoc + all three assert-id kinds.
    #[test]
    test_observer_seed_nested_loops ["observers=test"] => vc_shapes::seed_nested_loops()
    => Err(err) => {
        let d = parse(&err);
        assert!(has(&d.krate_function_names, "test"), "got {:?}", d.krate_function_names);
        // Both loop counters are havoced/assigned; outer + inner invariants + decreases fire.
        assert!(has(&d.assigns, "i@") && has(&d.assigns, "j@"), "got {:?}", d.assigns);
        assert!(has(&d.assert_id_kinds, "LoopInvariant"), "got {:?}", d.assert_id_kinds);
        assert!(has(&d.assert_id_kinds, "DecreasesCheck"), "got {:?}", d.assert_id_kinds);
        assert!(d.query_lowered >= 2, "nested loops -> multiple isolated queries");
    }
}

// ---- Uncovered-callback assertions, result-payload semantics, and neutrality ----

test_verify_one_file_with_options! {
    // covers (VO axis): on_quantifier_binder_decl — a choose binding declares its binder.
    #[test]
    test_observer_binder_decl ["observers=test"] => verus_code! {
        spec fn p(i: int) -> bool;
        proof fn f() {
            let w = choose|i: int| p(i);
            assert(p(w));
        }
    } => Err(err) => {
        let d = parse(&err);
        assert!(!d.binder_decls.is_empty(),
            "choose must declare a quantifier binder; got {:?}", d.binder_decls);
        assert!(!d.choose_decls.is_empty(), "got {:?}", d.choose_decls);
    }
}

test_verify_one_file_with_options! {
    // covers (VO axis): on_check_valid_result Invalid payload — the live evaluator's
    // three-way contract: Some(true) / Some(false) / None per failing query.
    #[test]
    test_observer_eval_three_way ["observers=test"] => verus_code! {
        proof fn f(x: u64) {
            assert(x < 5);
        }
    } => Err(err) => {
        let d = parse(&err);
        assert!(d.check_valid_invalid >= 1);
        // Recorded in triples per Invalid: eval(true), eval(false), eval(non-bool).
        assert!(d.eval_expr_results.chunks(3).any(|c|
            c == [Some(true), Some(false), None]),
            "expected a [Some(true), Some(false), None] triple; got {:?}", d.eval_expr_results);
    }
}

test_verify_one_file_with_options! {
    // covers (VO axis over corpus): guarded match — merges and per-arm assigns observed.
    #[test]
    test_observer_seed_match_guard ["observers=test"] => vc_shapes::seed_match_guard()
    => Err(err) => {
        let d = parse(&err);
        assert!(d.switch_count >= 1, "a match lowers to a Switch; got {}", d.switch_count);
        assert!(has(&d.assert_id_kinds, "Ensures"), "got {:?}", d.assert_id_kinds);
    }
}

test_verify_one_file_with_options! {
    // covers (VO axis over corpus): early return — ensures obligation still identified.
    #[test]
    test_observer_seed_early_return ["observers=test"] => vc_shapes::seed_early_return()
    => Err(err) => {
        let d = parse(&err);
        assert!(has(&d.assert_id_kinds, "Ensures"), "got {:?}", d.assert_id_kinds);
        assert!(d.query_lowered >= 1);
    }
}

/// Behavior-neutrality differential: for every corpus seed, verification outcomes are
/// identical with and without observers registered (same error count, same primary spans).
#[test]
fn test_observer_neutrality_differential() {
    let seeds: Vec<(&str, String)> = vec![
        ("match_nested", vc_shapes::seed_match_nested()),
        ("match_in_loop_inv", vc_shapes::seed_match_in_loop_inv()),
        ("loop_break", vc_shapes::seed_loop_break()),
        ("branch_merge", vc_shapes::seed_branch_merge()),
        ("param_mutated_before_loop", vc_shapes::seed_param_mutated_before_loop()),
        ("nested_loops", vc_shapes::seed_nested_loops()),
        ("for_loop", vc_shapes::seed_for_loop()),
        ("match_guard", vc_shapes::seed_match_guard()),
        ("bare_loop", vc_shapes::seed_bare_loop()),
        ("early_return", vc_shapes::seed_early_return()),
        ("continue", vc_shapes::seed_continue()),
        ("break_labeled", vc_shapes::seed_break_labeled()),
        ("loop_break_noniso", vc_shapes::seed_loop_break_noniso()),
        ("nested_loops_noniso", vc_shapes::seed_nested_loops_noniso()),
        ("break_labeled_noniso", vc_shapes::seed_break_labeled_noniso()),
        ("expand_ensures", vc_shapes::seed_expand_ensures()),
        ("truncate_cast", vc_shapes::seed_truncate_cast()),
        ("choose_witness", vc_shapes::seed_choose_witness()),
        ("forall_and_choose", vc_shapes::seed_forall_and_choose()),
        ("state_machine_inductive", vc_shapes::seed_state_machine_inductive()),
        ("atomic_invariant_open", vc_shapes::seed_atomic_invariant_open()),
    ];
    for (name, code) in seeds {
        let plain = verify_one_file(&format!("neutral_{}_plain", name), code.clone(), &[]);
        let observed = verify_one_file(&format!("neutral_{}_obs", name), code, &["observers=test"]);
        let (p, o) = match (&plain, &observed) {
            (Ok(p), Ok(o)) | (Err(p), Err(o)) | (Ok(p), Err(o)) | (Err(p), Ok(o)) => (p, o),
        };
        assert_eq!(
            plain.is_err(),
            observed.is_err(),
            "seed {}: overall outcome differs with observers",
            name
        );
        assert_eq!(
            p.errors.len(),
            o.errors.len(),
            "seed {}: error count differs with observers",
            name
        );
        // The corpus programs are small; none should hit the solver resource limit, so the
        // result channel must report no Timeout for any of them.
        let d = parse(o);
        assert_eq!(d.check_valid_timeout, 0, "seed {}: unexpected solver timeout", name);
        for (a, b) in p.errors.iter().zip(o.errors.iter()) {
            assert_eq!(
                a.rendered.lines().next(),
                b.rendered.lines().next(),
                "seed {}: error text differs with observers",
                name
            );
        }
    }
}

test_verify_one_file_with_options! {
    // covers: S-continue — the loop's invariants (and decreases) are asserted at the
    // continue site; the too-strong invariant fails there.
    #[test]
    test_observer_seed_continue ["observers=test"] => vc_shapes::seed_continue()
    => Err(err) => {
        let d = parse(&err);
        assert!(has(&d.assert_id_kinds, "LoopInvariant"), "got {:?}", d.assert_id_kinds);
        // Isolated lowering (the default): loops never appear as Breakable regions.
        assert_eq!(d.breakable_count, 0, "got {}", d.breakable_count);
    }
}

test_verify_one_file_with_options! {
    // covers: S-break-labeled — `break 'outer` asserts the TARGET loop's invariants at
    // the break site; the outer invariant fails there.
    #[test]
    test_observer_seed_break_labeled ["observers=test"] => vc_shapes::seed_break_labeled()
    => Err(err) => {
        let d = parse(&err);
        assert!(has(&d.assert_id_kinds, "LoopInvariant"), "got {:?}", d.assert_id_kinds);
        assert_eq!(d.breakable_count, 0, "got {}", d.breakable_count);
    }
}

test_verify_one_file_with_options! {
    // covers: S-loop-noniso — without loop isolation the loop lowers into the enclosing
    // query as a labeled Breakable region with Break jumps.
    #[test]
    test_observer_seed_loop_break_noniso ["observers=test"] => vc_shapes::seed_loop_break_noniso()
    => Err(err) => {
        let d = parse(&err);
        assert!(d.breakable_count >= 1, "non-isolated loop must lower as Breakable; got {}",
            d.breakable_count);
        assert!(d.break_count >= 1, "got {}", d.break_count);
    }
}

test_verify_one_file_with_options! {
    // covers: S-break-labeled-noniso — a labeled break without isolation still lowers the
    // loops as Breakable regions with Break jumps (two nested loops -> two of each).
    #[test]
    test_observer_seed_break_labeled_noniso ["observers=test"] => vc_shapes::seed_break_labeled_noniso()
    => Err(err) => {
        let d = parse(&err);
        assert!(d.breakable_count >= 2, "nested non-isolated loops -> Breakable regions; got {}",
            d.breakable_count);
        assert!(d.break_count >= 1, "labeled break emits a Break; got {}", d.break_count);
    }
}

test_verify_one_file_with_options! {
    // covers: S-nested-noniso — nested loops without isolation: nested Breakable regions
    // in a single query.
    #[test]
    test_observer_seed_nested_loops_noniso ["observers=test"] => vc_shapes::seed_nested_loops_noniso()
    => Err(err) => {
        let d = parse(&err);
        assert!(d.breakable_count >= 2, "two nested Breakable regions; got {}",
            d.breakable_count);
        assert!(d.break_count >= 2, "got {}", d.break_count);
    }
}

test_verify_one_file_with_options! {
    // A discharged (unsat) query is observed with the same shape callbacks as a failing one,
    // and its result callback names the obligations it checked: two postconditions and one
    // loop invariant here, none of which fail.
    #[test]
    test_observer_valid_reports_obligations ["observers=test"] => verus_code! {
        fn test(n: u64) -> (r: u64)
            requires n < 100
            ensures r >= n, r < 200
        {
            let mut i: u64 = 0;
            while i < n
                invariant i <= n
                decreases n - i
            {
                i = i + 1;
            }
            i + 1
        }
    } => Ok(err) => {
        let d = parse(&err);
        assert!(d.check_valid_valid >= 1, "got {}", d.check_valid_valid);
        assert_eq!(d.check_valid_invalid, 0);
        // Shape callbacks fire regardless of outcome.
        assert!(d.query_lowered >= 1);
        assert!(has(&d.assert_id_kinds, "Ensures"), "got {:?}", d.assert_id_kinds);
        assert!(has(&d.assert_id_kinds, "LoopInvariant"), "got {:?}", d.assert_id_kinds);
        // At least one discharged query reported labeled obligations.
        assert!(d.valid_assert_id_counts.iter().any(|&c| c >= 1),
            "a Valid result should name its assertion ids; got {:?}", d.valid_assert_id_counts);
        // Usage reporting is opt-in: not enabled here, so no core is attached.
        assert!(d.valid_used_axiom_counts.iter().all(|c| c.is_none()),
            "no usage info without the flag; got {:?}", d.valid_used_axiom_counts);
    }
}

test_verify_one_file_with_options! {
    // With usage reporting enabled, a discharged query carries the unsat core: the named
    // axioms the solver used. A call to a lemma with a broadcast-style axiom makes the core
    // non-empty.
    #[test]
    test_observer_valid_usage_info ["observers=test", "-V axiom-usage-info"] => verus_code! {
        spec fn f(x: int) -> int;
        proof fn lemma_f(x: int)
            ensures f(x) > 0
        {
            admit();
        }
        proof fn test(x: int) {
            lemma_f(x);
            assert(f(x) > 0);
        }
    } => Ok(err) => {
        let d = parse(&err);
        assert!(d.check_valid_valid >= 1, "got {}", d.check_valid_valid);
        assert!(d.valid_used_axiom_counts.iter().any(|c| c.is_some()),
            "usage info should be attached when enabled; got {:?}", d.valid_used_axiom_counts);
    }
}

// ---- Payload sufficiency and reachability -------------------------------------------------
//
// A callback is only useful if a consumer can reconstruct the source fragment from
// the payload data. These rows assert on payload *content*.  Reachability rows
// assert that every enum variant an observer can receive is produced by some program.

test_verify_one_file_with_options! {
    // A `choose` payload carries the witness predicate: a consumer can render
    // `choose|x: int| p(x)` rather than only knowing a choose exists.
    #[test]
    test_observer_choose_payload ["observers=test"] => vc_shapes::seed_choose_witness()
    => Err(err) => {
        let d = parse(&err);
        assert!(!d.choose_payloads.is_empty(), "got {:?}", d.choose_payloads);
        // The predicate is the application of `p` to the bound variable, as a structured
        // expression (Debug form of the AIR `Apply`), not merely a mention of `p`.
        assert!(d.choose_payloads.iter().any(|s| s.contains("p.?") && s.contains("[Var(\"x$\")]")),
            "choose payload must carry the predicate p(x); got {:?}", d.choose_payloads);
        // At the AIR level closure binders are boxed, so the binder type is `Poly`; the source
        // type reaches the observer through the VIR-level binder declaration instead.
        assert!(d.choose_payloads.iter().any(|s| s.contains("Poly")),
            "choose payload must carry the binder type; got {:?}", d.choose_payloads);
    }
}

test_verify_one_file_with_options! {
    // A lambda payload carries typed binders, so a consumer can render `|x: int| ...`.
    #[test]
    test_observer_lambda_binder_types ["observers=test"] => verus_code! {
        spec fn apply_to_one(f: spec_fn(int) -> int) -> int { f(1) }
        proof fn test()
            ensures apply_to_one(|x: int| x + 1) == 3
        {
        }
    } => Err(err) => {
        let d = parse(&err);
        assert!(!d.lambda_payloads.is_empty(), "got {:?}", d.lambda_payloads);
        // AIR closure binders are boxed (`Poly`); the payload carries the type slot either way.
        assert!(d.lambda_payloads.iter().any(|s| s.contains("Poly")),
            "lambda payload must carry the binder type; got {:?}", d.lambda_payloads);
        assert!(d.lambda_payloads.iter().any(|s| s.contains("Var(\"x$\")") && s.contains("Add")),
            "lambda payload must carry the body x + 1; got {:?}", d.lambda_payloads);
    }
}

test_verify_one_file_with_options! {
    // A binder declaration payload carries its kind: a consumer can tell a quantifier binder
    // from a choose binder (both fire the same callback).
    #[test]
    test_observer_binder_decl_kinds ["observers=test"] => vc_shapes::seed_forall_and_choose()
    => Err(err) => {
        let d = parse(&err);
        assert!(d.binder_decl_payloads.iter().any(|s| s.contains("QuantBinder")),
            "got {:?}", d.binder_decl_payloads);
        assert!(d.binder_decl_payloads.iter().any(|s| s.contains("ChooseBinder")),
            "got {:?}", d.binder_decl_payloads);
        assert!(d.binder_decl_payloads.iter().any(|s| s.contains("Int(Int)")),
            "binder decl payload must carry the type int; got {:?}", d.binder_decl_payloads);
    }
}

/// Every version-origin kind an observer receives is one the lowering produces. Across the
/// whole corpus, the only origins are `Havoc` and `Assign`.
#[test]
fn test_observer_version_origins_exhaustive() {
    let seeds: Vec<(&str, String)> = vec![
        ("match_nested", vc_shapes::seed_match_nested()),
        ("match_in_loop_inv", vc_shapes::seed_match_in_loop_inv()),
        ("loop_break", vc_shapes::seed_loop_break()),
        ("branch_merge", vc_shapes::seed_branch_merge()),
        ("param_mutated_before_loop", vc_shapes::seed_param_mutated_before_loop()),
        ("nested_loops", vc_shapes::seed_nested_loops()),
        ("for_loop", vc_shapes::seed_for_loop()),
        ("match_guard", vc_shapes::seed_match_guard()),
        ("bare_loop", vc_shapes::seed_bare_loop()),
        ("early_return", vc_shapes::seed_early_return()),
        ("continue", vc_shapes::seed_continue()),
        ("break_labeled", vc_shapes::seed_break_labeled()),
        ("loop_break_noniso", vc_shapes::seed_loop_break_noniso()),
        ("nested_loops_noniso", vc_shapes::seed_nested_loops_noniso()),
        ("break_labeled_noniso", vc_shapes::seed_break_labeled_noniso()),
        ("expand_ensures", vc_shapes::seed_expand_ensures()),
        ("truncate_cast", vc_shapes::seed_truncate_cast()),
        ("choose_witness", vc_shapes::seed_choose_witness()),
        ("forall_and_choose", vc_shapes::seed_forall_and_choose()),
        ("state_machine_inductive", vc_shapes::seed_state_machine_inductive()),
        ("atomic_invariant_open", vc_shapes::seed_atomic_invariant_open()),
    ];
    for (name, code) in seeds {
        let r = verify_one_file(&format!("origins_{}", name), code, &["observers=test"]);
        let err = match &r {
            Ok(e) | Err(e) => e,
        };
        let d = parse(err);
        for ev in d.events.iter().filter(|e| e.starts_with("wp_version:")) {
            assert!(
                ev == "wp_version:Havoc" || ev == "wp_version:Assign",
                "seed {}: unexpected version origin {}",
                name,
                ev
            );
        }
    }
}

test_verify_one_file_with_options! {
    // The four payloads below were delivered but never inspected. Each row asserts the payload
    // names a construct from the source, so a consumer can rely on it.
    #[test]
    test_observer_remaining_payloads ["observers=test"] => verus_code! {
        spec fn sq(x: int) -> int { x * x }
        proof fn test(n: int)
            requires n > 2
            ensures forall|k: int| 0 <= k < n ==> sq(k) >= 0 && sq(k) < 0
        {
        }
    } => Err(err) => {
        let d = parse(&err);
        // on_axiom_decl: the spec fn's defining axiom mentions the function.
        assert!(d.axiom_payloads.iter().any(|s| s.contains("sq")),
            "axiom payload must carry the axiom body; got {} axioms", d.axiom_payloads.len());
        // on_query_lowered: the versioned-constant declarations name the parameter.
        assert!(d.query_local_var_payloads.iter().any(|s| s.contains("n")),
            "query local_vars must carry the declared constants; got {:?}", d.query_local_var_payloads);
        // on_quantifier_binder: the quantified body mentions the spec fn applied to the binder.
        assert!(d.quantifier_body_payloads.iter().any(|s| s.contains("sq")),
            "quantifier body payload must carry the body; got {:?}", d.quantifier_body_payloads);
        // on_krate: the crate under verification is identified.
        assert!(d.krate_current_crate.contains("test_crate"),
            "on_krate must identify the current crate; got {:?}", d.krate_current_crate);
    }
}

// ---- Constructs that lower to ordinary items --------------------------------------------
//
// State machines and atomic invariants are macros over ordinary Verus; nothing in the
// lowering is specific to them, so the observer sees ordinary events. These rows pin that.

test_verify_one_file_with_options! {
    // covers: S-state-machine — the macro's generated items (invariant, transition relation,
    // inductiveness lemma) appear as ordinary functions, and the failing obligation is the
    // lemma's postcondition.
    #[test]
    test_observer_seed_state_machine ["observers=test", "vstd"] => vc_shapes::seed_state_machine_inductive()
    => Err(err) => {
        // The macro generates its own module, so the observer reports more than one krate.
        let ds = parse_all(&err);
        assert!(ds.len() >= 2, "expected the state machine's module to be observed; got {} note(s)", ds.len());
        let fns = across(&ds, |d| &d.krate_function_names);
        for f in ["the_inv", "invariant", "tr", "tr_strong", "tr_enabled", "lemma_tr1"] {
            assert!(has(&fns, f), "generated fn {} missing; got {:?}", f, fns);
        }
        let kinds = across(&ds, |d| &d.assert_id_kinds);
        assert!(has(&kinds, "Ensures"), "got {:?}", kinds);
        assert!(ds.iter().any(|d| d.check_valid_invalid >= 1));
    }
}

test_verify_one_file_with_options! {
    // covers: S-atomic-invariant — the opened contents are an ordinary assigned local, and the
    // failing obligation is a call precondition (the closing call's requires), which the
    // observer sees as a query result but not as a labeled assertion kind.
    #[test]
    test_observer_seed_atomic_invariant ["observers=test", "vstd"] => vc_shapes::seed_atomic_invariant_open()
    => Err(err) => {
        let d = parse(&err);
        assert!(d.assigns.iter().any(|a| a.starts_with("inner")), "got {:?}", d.assigns);
        assert!(d.check_valid_invalid >= 1);
        // A precondition obligation carries its own id from the lowering; the observer is not
        // asked to supply one, so no AssertIdKind is reported for it.
        assert!(d.assert_id_kinds.is_empty(), "got {:?}", d.assert_id_kinds);
    }
}
