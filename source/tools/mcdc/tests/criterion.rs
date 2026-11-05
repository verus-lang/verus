//! The MC/DC criterion, record encoding and needed-pair computation on hand-made evaluation sets.

use mcdc::analyze::*;
use std::collections::BTreeSet;

/// Builds the recorded vector from a pattern such as "TF-" (atom 0 true, atom 1 false, atom 2
/// not evaluated).
fn v(p: &str) -> u128 {
    let mut x = 0u128;
    for (i, c) in p.chars().enumerate() {
        match c {
            'T' => x |= 3 << (2 * i),
            'F' => x |= 1 << (2 * i),
            _ => {}
        }
    }
    x
}
fn set(rows: &[(&str, bool)]) -> BTreeSet<(bool, u128)> {
    rows.iter().map(|(p, o)| (*o, v(p))).collect()
}
fn ids(xs: &[usize]) -> BTreeSet<usize> {
    xs.iter().copied().collect()
}

#[test]
fn and_full_coverage_with_short_circuit() {
    // a && b: TT=>T, F-=>F, TF=>F. Pair (TT, F-) shows a: b is not evaluated in F-, so it is
    // a don't-care. Pair (TT, TF) shows b.
    let c = analyze(2, &set(&[("TT", true), ("F-", false), ("TF", false)]));
    assert_eq!(c.mcdc, ids(&[0, 1]));
    assert_eq!(c.cond(), ids(&[0, 1]));
    assert_eq!(c.outcomes.len(), 2);
}

#[test]
fn and_missing_short_circuit_pair() {
    // a && b with TT=>T and TF=>F only: a never false, so only b is covered.
    let c = analyze(2, &set(&[("TT", true), ("TF", false)]));
    assert_eq!(c.mcdc, ids(&[1]));
    assert_eq!(c.cond(), ids(&[1]));
}

#[test]
fn or_short_circuit() {
    // a || b: T-=>T, FF=>F shows a; FT=>T, FF=>F shows b.
    let c = analyze(2, &set(&[("T-", true), ("FF", false), ("FT", true)]));
    assert_eq!(c.mcdc, ids(&[0, 1]));
}

#[test]
fn two_atoms_differ_is_not_a_pair() {
    // a && b: TT=>T and FF=>F (a constructed vector where both atoms are evaluated and differ).
    // Unique-cause MC/DC needs exactly one evaluated-in-both atom to differ, so neither is shown.
    // Condition coverage holds for both atoms.
    let c = analyze(2, &set(&[("TT", true), ("FF", false)]));
    assert!(c.mcdc.is_empty());
    assert_eq!(c.cond(), ids(&[0, 1]));
    // (a || b) && c: T-T=>T vs FTF=>F differ in a and c (b is a don't-care): no pair.
    let c = analyze(3, &set(&[("T-T", true), ("FTF", false)]));
    assert!(c.mcdc.is_empty());
}

#[test]
fn masking_pair_is_not_accepted() {
    // (a && b) || c, atom c: TFT=>T vs F-F=>F. In both, (a && b) is false, so masking MC/DC
    // accepts the pair for c. Atom a is evaluated in both with different values, so
    // unique-cause MC/DC (this tool, clang) does not.
    let c = analyze(3, &set(&[("TFT", true), ("F-F", false)]));
    assert!(c.mcdc.is_empty());
    // Adding TFF=>F gives the unique-cause pair TFT/TFF for c.
    let c = analyze(3, &set(&[("TFT", true), ("F-F", false), ("TFF", false)]));
    assert_eq!(c.mcdc, ids(&[2]));
}

#[test]
fn single_outcome_has_no_pair() {
    let c = analyze(3, &set(&[("TTT", false), ("F--", false), ("TF-", false)]));
    assert!(c.mcdc.is_empty());
    assert_eq!(c.outcomes, [false].into_iter().collect());
}

#[test]
fn atom_63_uses_the_top_bits() {
    let n = 64;
    let a = "T".repeat(n);
    let mut b = "T".repeat(n);
    b.replace_range(63..64, "F");
    let c = analyze(n, &set(&[(&a, true), (&b, false)]));
    assert_eq!(c.mcdc, ids(&[63]));
}

#[test]
fn records_round_trip() {
    let r = encode(1234, true, v("TF-T"));
    assert_eq!(decode(&r), (1234, true, v("TF-T")));
}

#[test]
fn tree_parse_and_eval() {
    let t = parse_tree("(!(0&&1)||2)").unwrap();
    let mut e = vec![None; 3];
    assert!(eval_tree(&t, &[false, true, false], &mut e));
    assert_eq!(fmt_vec(&e, true), "F--=>T");
    assert!(parse_tree("(0&&1").is_err());
    assert!(parse_tree("(0&&1))").is_err());
}

#[test]
fn needed_pair_three_way_and() {
    // modes.rs:1434 shape: a && b && c with only F outcomes recorded.
    let t = parse_tree("((0&&1)&&2)").unwrap();
    let seen = set(&[("F--", false), ("TF-", false), ("TTF", false)]);
    let p = needed_pair(&t, 3, &seen, 0).unwrap();
    assert_eq!((p.with_true.as_str(), p.with_false.as_str()), ("TTT=>T", "F--=>F"));
    assert_eq!(p.needed(), "TTT=>T");
    let p = needed_pair(&t, 3, &BTreeSet::new(), 2).unwrap();
    assert_eq!((p.with_true.as_str(), p.with_false.as_str()), ("TTT=>T", "TTF=>F"));
    assert_eq!(p.needed(), "both");
}

#[test]
fn needed_pair_prefers_a_recorded_side() {
    // a || b, atom 1: the only pair is FT=>T vs FF=>F. With FF recorded, FT is needed.
    let t = parse_tree("(0||1)").unwrap();
    let p = needed_pair(&t, 2, &set(&[("FF", false)]), 1).unwrap();
    assert_eq!(p.needed(), "FT=>T");
    // (a && b) || c, atom 2: candidate pairs F-T/F-F (4 atoms evaluated) and TFT/TFF (6).
    // The shorter one wins when nothing is recorded; the recorded one wins otherwise.
    let t = parse_tree("((0&&1)||2)").unwrap();
    let p = needed_pair(&t, 3, &BTreeSet::new(), 2).unwrap();
    assert_eq!((p.with_true.as_str(), p.with_false.as_str()), ("F-T=>T", "F-F=>F"));
    let p = needed_pair(&t, 3, &set(&[("TFF", false)]), 2).unwrap();
    assert_eq!((p.with_true.as_str(), p.needed()), ("TFT=>T", "TFT=>T"));
}

#[test]
fn needed_pair_limits() {
    let t = parse_tree("0").unwrap();
    let p = needed_pair(&t, 1, &BTreeSet::new(), 0).unwrap();
    assert_eq!((p.with_true.as_str(), p.with_false.as_str()), ("T=>T", "F=>F"));
    // n > 18 is not enumerated.
    assert!(needed_pair(&t, 19, &BTreeSet::new(), 0).is_none());
}
