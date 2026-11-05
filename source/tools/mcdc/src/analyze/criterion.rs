//! The coverage criteria, per decision with n atoms, over the set of distinct recorded
//! evaluations:
//! - MC/DC (unique-cause, with short-circuit don't-cares, as clang/LLVM define it): atom i is
//!   covered when two evaluations u, w exist with different outcomes, atom i evaluated in both with
//!   different values, and every other atom either evaluated in both with equal values or not
//!   evaluated in at least one of them.
//! - Condition coverage: atom i was observed both true and false.
//! - Decision coverage: outcomes observed, out of 2.

use std::collections::BTreeSet;

const EVEN: u128 = 0x5555_5555_5555_5555_5555_5555_5555_5555;

#[derive(Default, Debug, PartialEq)]
pub struct Coverage {
    /// Atoms with an independence pair.
    pub mcdc: BTreeSet<usize>,
    /// Atoms observed true.
    pub seen_true: BTreeSet<usize>,
    /// Atoms observed false.
    pub seen_false: BTreeSet<usize>,
    pub outcomes: BTreeSet<bool>,
}

impl Coverage {
    pub fn cond(&self) -> BTreeSet<usize> {
        self.seen_true.intersection(&self.seen_false).copied().collect()
    }
}

/// (evaluated bits, value bits), both at the even positions 2i.
pub fn split(vec: u128) -> (u128, u128) {
    (vec & EVEN, (vec >> 1) & EVEN)
}

/// The criteria of the module comment, for a decision with `n` atoms.
pub fn analyze(n: usize, vecs: &BTreeSet<(bool, u128)>) -> Coverage {
    let mut c = Coverage::default();
    for &(o, v) in vecs {
        c.outcomes.insert(o);
        let (ev, val) = split(v);
        for i in 0..n {
            if (ev >> (2 * i)) & 1 == 1 {
                if (val >> (2 * i)) & 1 == 1 {
                    c.seen_true.insert(i);
                } else {
                    c.seen_false.insert(i);
                }
            }
        }
    }
    let t: Vec<_> = vecs.iter().filter(|x| x.0).map(|x| split(x.1)).collect();
    let f: Vec<_> = vecs.iter().filter(|x| !x.0).map(|x| split(x.1)).collect();
    'outer: for &(eu, vu) in &t {
        for &(ew, vw) in &f {
            // atoms evaluated in both evaluations whose values differ
            let diff = eu & ew & (vu ^ vw);
            if diff != 0 && diff & (diff - 1) == 0 {
                c.mcdc.insert(diff.trailing_zeros() as usize / 2);
                if c.mcdc.len() == n {
                    break 'outer;
                }
            }
        }
    }
    c
}

/// Decision structure over atom indices, parsed from the manifest's `tree` field.
#[derive(Debug, Clone, PartialEq)]
pub enum Tree {
    Atom(usize),
    Not(Box<Tree>),
    And(Box<Tree>, Box<Tree>),
    Or(Box<Tree>, Box<Tree>),
}

pub fn parse_tree(s: &str) -> Result<Tree, String> {
    fn expr(s: &[u8], pos: &mut usize) -> Result<Tree, String> {
        match s.get(*pos) {
            Some(b'!') => {
                *pos += 1;
                Ok(Tree::Not(Box::new(expr(s, pos)?)))
            }
            Some(b'(') => {
                *pos += 1;
                let l = expr(s, pos)?;
                let op = s.get(*pos..*pos + 2).ok_or("truncated tree")?;
                *pos += 2;
                let r = expr(s, pos)?;
                if s.get(*pos) != Some(&b')') {
                    return Err(format!("expected ) at {}", pos));
                }
                *pos += 1;
                match op {
                    b"&&" => Ok(Tree::And(Box::new(l), Box::new(r))),
                    b"||" => Ok(Tree::Or(Box::new(l), Box::new(r))),
                    _ => Err(format!("bad operator at {}", *pos - 2)),
                }
            }
            Some(c) if c.is_ascii_digit() => {
                let st = *pos;
                while s.get(*pos).map_or(false, |c| c.is_ascii_digit()) {
                    *pos += 1;
                }
                Ok(Tree::Atom(std::str::from_utf8(&s[st..*pos]).unwrap().parse().unwrap()))
            }
            _ => Err(format!("unexpected input at {}", pos)),
        }
    }
    let mut pos = 0;
    let t = expr(s.as_bytes(), &mut pos)?;
    if pos != s.len() {
        return Err(format!("trailing input at {}", pos));
    }
    Ok(t)
}

/// Evaluates with short-circuiting; `evd[i]` is set to the value of each evaluated atom.
pub fn eval_tree(t: &Tree, asg: &[bool], evd: &mut [Option<bool>]) -> bool {
    match t {
        Tree::Atom(i) => {
            evd[*i] = Some(asg[*i]);
            asg[*i]
        }
        Tree::Not(x) => !eval_tree(x, asg, evd),
        Tree::And(l, r) => eval_tree(l, asg, evd) && eval_tree(r, asg, evd),
        Tree::Or(l, r) => eval_tree(l, asg, evd) || eval_tree(r, asg, evd),
    }
}

fn vec_of(evd: &[Option<bool>]) -> u128 {
    let mut v = 0u128;
    for (i, b) in evd.iter().enumerate() {
        if let Some(b) = b {
            v |= (if *b { 3 } else { 1 }) << (2 * i);
        }
    }
    v
}

/// `T`/`F` per evaluated atom, `-` per atom not evaluated, then `=>` and the outcome.
pub fn fmt_vec(evd: &[Option<bool>], out: bool) -> String {
    let mut s: String = evd
        .iter()
        .map(|b| match b {
            Some(true) => 'T',
            Some(false) => 'F',
            None => '-',
        })
        .collect();
    s.push_str(if out { "=>T" } else { "=>F" });
    s
}

/// A pair of evaluations that would show the independence of atom `i`.
#[derive(Debug, PartialEq)]
pub struct NeededPair {
    /// The evaluation with atom i true.
    pub with_true: String,
    /// The evaluation with atom i false.
    pub with_false: String,
    pub true_seen: bool,
    pub false_seen: bool,
}

impl NeededPair {
    /// The evaluation(s) a new test has to produce.
    pub fn needed(&self) -> &str {
        match (self.true_seen, self.false_seen) {
            (false, false) => "both",
            (true, _) => &self.with_false,
            (false, true) => &self.with_true,
        }
    }
}

/// For atom `i`: enumerates the assignments of the other atoms (n <= 18), keeps the pairs that
/// differ only in atom i, evaluate it in both, and have different outcomes. Prefers a pair with one
/// side already recorded, then the pair with the fewest evaluated atoms; ties go to the first pair
/// in enumeration order (the other atoms counted in binary, atom 0 most significant, false first).
/// `None` when n > 18 or no such pair exists.
pub fn needed_pair(
    tree: &Tree,
    n: usize,
    seen: &BTreeSet<(bool, u128)>,
    i: usize,
) -> Option<NeededPair> {
    if n > 18 || n == 0 {
        return None;
    }
    let mut best: Option<((bool, i64), NeededPair)> = None;
    let mut tried = BTreeSet::new();
    for k in 0u32..(1u32 << (n - 1)) {
        let mut asg = Vec::with_capacity(n);
        for j in 0..n - 1 {
            asg.push((k >> (n - 2 - j)) & 1 == 1);
        }
        asg.insert(i, true);
        let mut e1 = vec![None; n];
        let o1 = eval_tree(tree, &asg, &mut e1);
        if e1[i].is_none() {
            continue;
        }
        asg[i] = false;
        let mut e2 = vec![None; n];
        let o2 = eval_tree(tree, &asg, &mut e2);
        if o1 == o2 {
            continue;
        }
        let (v1, v2) = (vec_of(&e1), vec_of(&e2));
        if !tried.insert((v1, v2)) {
            continue;
        }
        let s1 = seen.contains(&(o1, v1));
        let s2 = seen.contains(&(o2, v2));
        let count = |e: &[Option<bool>]| e.iter().filter(|x| x.is_some()).count() as i64;
        let score = (s1 || s2, -(count(&e1) + count(&e2)));
        if best.as_ref().map_or(true, |(b, _)| score > *b) {
            best = Some((
                score,
                NeededPair {
                    with_true: fmt_vec(&e1, o1),
                    with_false: fmt_vec(&e2, o2),
                    true_seen: s1,
                    false_seen: s2,
                },
            ));
        }
    }
    best.map(|(_, p)| p)
}
