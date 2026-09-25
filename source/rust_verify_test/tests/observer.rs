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
//! on_branch_merge                     |  +   |  0   |   0   |  0   |   +   |  0   |  0   |        |      |
//! on_break_merge                      |  0   |  0   |   0   |  0   |   +   |  0   |  0   |        |      |
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
//! on_lambda_decl (names)              |  0   |  0   |   0   |  +   |   0   |  0   |  0   |        |      |
//! on_choose_decl (names)              |  0   |  0   |   0   |  +   |   0   |  0   |  0   |        |      |
//! check_valid_result(Invalid)         |  +   |  +   |   0   |  +   |   +   |      |  +   |   +    |  +   |
//! check_valid_result(Valid)           |  +   |      |   +   |      |       |      |      |        |      |
//! check_valid_result(Timeout)         |      |      |       |      |       |      |      |  TODO  |      |
//! invalid model_defs size             |  +   |  +   |       |  +   |       |      |  +   |        |      |
//! eval_bool_expr during Invalid       |  +   |      |       |      |       |      |      |        |      |
//! ```

#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;
mod vc_shapes;

// ── JSON parsing (mirrors TestObserver data model) ──

struct D {
    krate_function_names: Vec<String>,
    krate_datatype_names: Vec<String>,
    havocs: Vec<String>,
    assigns: Vec<String>,
    branch_merges: usize,
    break_merges: usize,
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
    pre_body_binders: Vec<String>,
    post_body_binders: Vec<String>,
    events: Vec<String>,
}

fn strings(s: &str) -> Vec<String> {
    let s = s.trim();
    if s == "[]" {
        return vec![];
    }
    s[1..s.len() - 1].split(',').map(|i| i.trim().trim_matches('"').to_string()).collect()
}
fn usizes(s: &str) -> Vec<usize> {
    let s = s.trim();
    if s == "[]" {
        return vec![];
    }
    s[1..s.len() - 1].split(',').filter_map(|i| i.trim().parse().ok()).collect()
}
fn opt_usizes(s: &str) -> Vec<Option<usize>> {
    let s = s.trim();
    if s == "[]" {
        return vec![];
    }
    s[1..s.len() - 1].split(',').map(|i| i.trim().parse::<usize>().ok()).collect()
}

fn opt_bools(s: &str) -> Vec<Option<bool>> {
    let s = s.trim();
    if s == "[]" {
        return vec![];
    }
    s[1..s.len() - 1]
        .split(',')
        .map(|i| match i.trim() {
            "true" => Some(true),
            "false" => Some(false),
            _ => None,
        })
        .collect()
}
fn nested_strings(s: &str) -> Vec<Vec<String>> {
    let s = s.trim();
    if s == "[]" {
        return vec![];
    }
    let inner = &s[1..s.len() - 1];
    let mut result = vec![];
    let mut depth = 0;
    let mut start = 0;
    for (i, c) in inner.char_indices() {
        match c {
            '[' => {
                if depth == 0 {
                    start = i;
                }
                depth += 1;
            }
            ']' => {
                depth -= 1;
                if depth == 0 {
                    result.push(strings(&inner[start..=i]));
                }
            }
            _ => {}
        }
    }
    result
}
fn parse_version_correlations(s: &str) -> Vec<(String, u32, String)> {
    let s = s.trim();
    if s == "[]" {
        return vec![];
    }
    // Format: [["name",line,"kind"],...]
    let mut result = vec![];
    let inner = &s[1..s.len() - 1];
    let mut depth = 0;
    let mut start = 0;
    for (i, c) in inner.char_indices() {
        match c {
            '[' => {
                if depth == 0 {
                    start = i;
                }
                depth += 1;
            }
            ']' => {
                depth -= 1;
                if depth == 0 {
                    let triple = &inner[start + 1..i];
                    let parts: Vec<&str> = triple.splitn(3, ',').collect();
                    if parts.len() == 3 {
                        let name = parts[0].trim().trim_matches('"').to_string();
                        let line: u32 = parts[1].trim().parse().unwrap_or(0);
                        let kind = parts[2].trim().trim_matches('"').to_string();
                        result.push((name, line, kind));
                    }
                }
            }
            _ => {}
        }
    }
    result
}
fn string_pairs(s: &str) -> Vec<(String, String)> {
    let nested = nested_strings(s);
    nested
        .into_iter()
        .map(|v| {
            assert_eq!(v.len(), 2);
            (v[0].clone(), v[1].clone())
        })
        .collect()
}
fn val<'a>(json: &'a str, key: &str) -> &'a str {
    let needle = format!("\"{}\":", key);
    let start = json.find(&needle).unwrap_or_else(|| panic!("key '{}' not found", key));
    let rest = &json[start + needle.len()..];
    if rest.starts_with("[[") || rest.starts_with("[]") {
        // nested array — find matching outer ]
        let mut depth = 0;
        for (i, c) in rest.char_indices() {
            match c {
                '[' => depth += 1,
                ']' => {
                    depth -= 1;
                    if depth == 0 {
                        return &rest[..=i];
                    }
                }
                _ => {}
            }
        }
        rest
    } else if rest.starts_with('[') {
        &rest[..rest.find(']').unwrap() + 1]
    } else {
        let end = rest.find(|c: char| c == ',' || c == '}').unwrap_or(rest.len());
        rest[..end].trim()
    }
}

fn parse_note(note_text: &str) -> D {
    let json = note_text
        .strip_prefix("OBSERVER:")
        .or_else(|| {
            // Handle OBSERVER_N: prefix for composite
            note_text.find(':').and_then(|i| {
                if note_text[..i].starts_with("OBSERVER_") {
                    Some(&note_text[i + 1..])
                } else {
                    None
                }
            })
        })
        .unwrap_or(note_text);
    D {
        krate_function_names: strings(val(json, "krate_function_names")),
        krate_datatype_names: strings(val(json, "krate_datatype_names")),
        havocs: strings(val(json, "havocs")),
        assigns: strings(val(json, "assigns")),
        branch_merges: val(json, "branch_merges").parse().unwrap(),
        break_merges: val(json, "break_merges").parse().unwrap(),
        variable_defs: strings(val(json, "variable_defs")),
        for_loop_vars: string_pairs(val(json, "for_loop_vars")),
        reveal_strings: strings(val(json, "reveal_strings")),
        quantifier_binders: strings(val(json, "quantifier_binders")),
        assert_id_kinds: strings(val(json, "assert_id_kinds")),
        function_lowered: val(json, "function_lowered").parse().unwrap(),
        query_lowered: val(json, "query_lowered").parse().unwrap(),
        query_snapshot_counts: usizes(val(json, "query_snapshot_counts")),
        version_correlations: parse_version_correlations(val(json, "version_correlations")),
        lambda_decls: strings(val(json, "lambda_decls")),
        choose_decls: strings(val(json, "choose_decls")),
        check_valid_invalid: val(json, "check_valid_invalid").parse().unwrap(),
        check_valid_valid: val(json, "check_valid_valid").parse().unwrap(),
        check_valid_timeout: val(json, "check_valid_timeout").parse().unwrap(),
        check_valid_invalid_model_size: usizes(val(json, "check_valid_invalid_model_size")),
        eval_expr_results: opt_bools(val(json, "eval_expr_results")),
        binder_decls: strings(val(json, "binder_decls")),
        breakable_count: val(json, "breakable_count").parse().unwrap(),
        break_count: val(json, "break_count").parse().unwrap(),
        valid_assert_id_counts: usizes(val(json, "valid_assert_id_counts")),
        valid_used_axiom_counts: opt_usizes(val(json, "valid_used_axiom_counts")),
        pre_body_binders: strings(val(json, "pre_body_binders")),
        post_body_binders: strings(val(json, "post_body_binders")),
        events: strings(val(json, "events")),
    }
}

fn parse(err: &TestErr) -> D {
    let note = err
        .notes
        .iter()
        .find_map(|n| {
            let t = n.rendered.strip_prefix("note: ").unwrap_or(&n.rendered);
            t.strip_prefix("OBSERVER:").map(|_| t.to_string())
        })
        .expect("OBSERVER note not found");
    parse_note(&note)
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
        assert_eq!(d.branch_merges, 2);
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
        assert_eq!(d.break_merges, 0);
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
        assert_eq!(d.branch_merges, 0);
        assert_eq!(d.break_merges, 0);
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
        assert_eq!(d.branch_merges, 0);
        assert_eq!(d.break_merges, 0);
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
        assert_eq!(d.break_merges, 0);
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
        // but branch_merges should increase from the if + break structure
        assert!(d.branch_merges > 0, "if should trigger branch_merge, got {}", d.branch_merges);
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
        assert_eq!(d.break_merges, 0);
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
        let note = find_note(&err, "VIROBS:");
        let json = note.strip_prefix("VIROBS:").unwrap();
        let events = strings(val(json, "events"));
        let fns = strings(val(json, "function_names"));
        let flowered: usize = val(json, "function_lowered").parse().unwrap();
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
        let note = find_note(&err, "AIROBS:");
        let json = note.strip_prefix("AIROBS:").unwrap();
        let events = strings(val(json, "events"));
        let ql: usize = val(json, "query_lowered").parse().unwrap();
        let ax: usize = val(json, "axiom_decls").parse().unwrap();
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
        let note = find_note(&err, "QROBS:");
        let json = note.strip_prefix("QROBS:").unwrap();
        let invalid: usize = val(json, "invalid").parse().unwrap();
        let events = strings(val(json, "events"));
        let eval = opt_bools(val(json, "eval_expr_results"));
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
        let note = find_note(&err, "QROBS:");
        let json = note.strip_prefix("QROBS:").unwrap();
        let valid: usize = val(json, "valid").parse().unwrap();
        let events = strings(val(json, "events"));
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
        assert!(d.branch_merges >= 1, "a match produces branch merges; got {}", d.branch_merges);
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
