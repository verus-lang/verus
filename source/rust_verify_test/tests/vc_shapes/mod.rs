//! VC-shape seed corpus, shared by end-to-end suites.
//!
//! Each function returns a small Verus program with a forced verification failure. The
//! `covers:` tags name the shape(s) a seed exercises, using these prefixes:
//!
//! - `S-` statement/control structure (the shapes verification-condition generation composes:
//!   branches, matches, loops, breaks, early returns, ...)
//! - `E-` expression grammar (expression forms reachable from source)
//! - `I-` encoding idioms (naming/encoding conventions of the lowering: temporaries,
//!   variable versions, old/final values, contract functions, ...)
//! - `X-` interactions (idiom x structure combinations that share per-query state,
//!   e.g. temporaries assigned per match arm)
//!
//! Seeds are APPEND-ONLY: once any suite pins an expected-output oracle to a seed, the seed's
//! program text is immutable — behavior changes get a new seed function. This keeps oracles in
//! all consuming suites stable against edits made in any one of them.

// Not every consumer uses every seed.
#![allow(dead_code)]

use rust_verify_test_macros::verus_code;

/// covers: S-match-nested
pub fn seed_match_nested() -> String {
    verus_code! {
        #[allow(unused)]
        enum Outer { A, B }
        #[allow(unused)]
        enum Inner { X, Y }

        proof fn test(o: Outer, i: Inner, v: int)
            requires v > 0
        {
            match o {
                Outer::A => {
                    match i {
                        Inner::X => {
                            assert(v > 1000);
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
    }
}

/// covers: S-match-in-loop, X-switch-in-loop (failing loop invariant, so the match arms are
/// inside the failing query)
pub fn seed_match_in_loop_inv() -> String {
    verus_code! {
        #[allow(unused)]
        enum Op { Add, Nop }
        fn test(op: Op, n: u64)
            requires n > 0
        {
            let mut val: u64 = 0;
            let mut i: u64 = 0;
            while i < n
                invariant i <= n, val == 0
                decreases n - i
            {
                match op {
                    Op::Add => { val = val + 1; }
                    Op::Nop => {}
                }
                i = i + 1;
            }
        }
    }
}

/// covers: S-loop-break (bare break inside while)
pub fn seed_loop_break() -> String {
    verus_code! {
        fn test(n: u64)
            requires n > 10
            ensures false
        {
            let mut i: u64 = 0;
            while i < n
                invariant i <= n
                decreases n - i
            {
                if i == 5 {
                    break;
                }
                i = i + 1;
            }
        }
    }
}

/// covers: I-versions-merge, S-if-noelse
pub fn seed_branch_merge() -> String {
    verus_code! {
        proof fn test(cond: bool, v: int)
            requires v < 100
        {
            let mut x: int = v;
            if cond {
                x = x + 10;
            }
            assert(x > v);
        }
    }
}

/// covers: X-old-loop, I-versions-mutation (param mutated before the loop)
pub fn seed_param_mutated_before_loop() -> String {
    verus_code! {
        fn test(n: u64)
            requires n > 10
            ensures false
        {
            let mut x: u64 = n;
            x = x + 1;
            let mut i: u64 = 0;
            while i < x
                invariant i <= x
                decreases x - i
            {
                i = i + 1;
            }
        }
    }
}

/// covers: S-nested-loops, X-versions-nested-loop (inner invariant fails)
pub fn seed_nested_loops() -> String {
    verus_code! {
        fn test(n: u64)
            requires n > 0
        {
            let mut i: u64 = 0;
            while i < n
                invariant i <= n
                decreases n - i
            {
                let mut j: u64 = 0;
                while j < i
                    invariant j <= i, j < 5
                    decreases i - j
                {
                    j = j + 1;
                }
                i = i + 1;
            }
        }
    }
}

/// covers: S-for (ghost-iterator machinery)
pub fn seed_for_loop() -> String {
    verus_code! {
        use vstd::prelude::*;
        fn test(v: &Vec<u64>) -> (sum: u64)
            ensures sum == 0
        {
            let mut sum: u64 = 0;
            for x in v.iter()
                invariant sum < 1000000u64,
            {
                sum = sum + 1u64;
            }
            sum
        }
    }
}

/// covers: S-match-guard (arm with if-guard)
pub fn seed_match_guard() -> String {
    verus_code! {
        #[allow(unused)]
        enum Kind { A, B }
        proof fn test(k: Kind, v: int) -> (r: int)
            ensures r > 0
        {
            match k {
                Kind::A if v > 10 => 1,
                Kind::A => 0,
                Kind::B => 2,
            }
        }
    }
}

/// covers: S-loop (bare loop with break)
/// (break-with-value is unreachable: Verus rejects "complex break expressions")
pub fn seed_bare_loop() -> String {
    verus_code! {
        fn test() -> (r: u64)
            ensures r > 100
        {
            let mut i: u64 = 0;
            loop
                invariant i <= 10,
                decreases 10 - i,
            {
                if i >= 7 {
                    break;
                }
                i = i + 1;
            }
            i
        }
    }
}

/// covers: S-return (early return before an unprovable postcondition)
pub fn seed_early_return() -> String {
    verus_code! {
        proof fn test(c: bool, v: int) -> (r: int)
            ensures r > 10
        {
            if c {
                return v;
            }
            20
        }
    }
}

/// covers: S-continue (loop invariants + decreases asserted at the continue site)
pub fn seed_continue() -> String {
    verus_code! {
        fn test(n: u64)
            requires n > 0
        {
            let mut i: u64 = 0;
            let mut s: u64 = 0;
            while i < n
                invariant s >= i, i <= n
                decreases n - i
            {
                i = i + 1;
                if i % 2 == 0 {
                    continue;
                }
                s = s + 2;
            }
        }
    }
}

/// covers: S-break-labeled (the labeled target loop's invariants asserted at the break site)
pub fn seed_break_labeled() -> String {
    verus_code! {
        fn test(n: u64)
            requires n > 10
        {
            let mut i: u64 = 0;
            let mut j: u64 = 0;
            'outer: while i < n
                invariant i <= n, j <= 5
                decreases n - i
            {
                j = 0;
                while j < 10
                    invariant j <= 10
                    decreases 10 - j
                {
                    if j == 8 {
                        break 'outer;
                    }
                    j = j + 1;
                }
                i = i + 1;
            }
        }
    }
}

/// covers: S-loop-noniso (same program as seed_loop_break, lowered without loop isolation:
/// the query carries the loop as a labeled `Breakable`/`Break` region with inline
/// assume-false exits instead of a separate loop query)
pub fn seed_loop_break_noniso() -> String {
    verus_code! {
        #[verifier::loop_isolation(false)]
        fn test(n: u64)
            requires n > 10
            ensures false
        {
            let mut i: u64 = 0;
            while i < n
                invariant i <= n
                decreases n - i
            {
                if i == 5 {
                    break;
                }
                i = i + 1;
            }
        }
    }
}

/// covers: S-nested-noniso (nested loops without isolation: nested Breakable regions in
/// one query)
pub fn seed_nested_loops_noniso() -> String {
    verus_code! {
        #[verifier::loop_isolation(false)]
        fn test(n: u64)
            requires n > 0
        {
            let mut i: u64 = 0;
            while i < n
                invariant i <= n
                decreases n - i
            {
                let mut j: u64 = 0;
                while j < i
                    invariant j <= i, j < 5
                    decreases i - j
                {
                    j = j + 1;
                }
                i = i + 1;
            }
        }
    }
}

/// covers: I-expand (an ensures whose failing spec function expands into conjuncts under
/// --expand-errors, introducing expand% temporaries in the second lowering)
pub fn seed_expand_ensures() -> String {
    verus_code! {
        spec fn in_range(x: u64) -> bool {
            x > 0 && x < 100
        }
        fn test() -> (r: u64)
            ensures in_range(r)
        {
            0
        }
    }
}

/// covers: I-truncate (a truncating cast: the VC clips the value to the target width)
pub fn seed_truncate_cast() -> String {
    verus_code! {
        #[verifier::truncate]
        fn test(x: u64) -> (r: u8)
            ensures r as u64 == x
        {
            x as u8
        }
    }
}

/// covers: S-break-labeled-noniso (labeled `break 'outer` without loop isolation: the
/// break targets the outer Breakable region by label, exercising the labeled-break
/// encoding in a single query)
pub fn seed_break_labeled_noniso() -> String {
    verus_code! {
        #[verifier::loop_isolation(false)]
        fn test(n: u64)
            requires n > 10
            ensures false
        {
            let mut i: u64 = 0;
            'outer: while i < n
                invariant i <= n
                decreases n - i
            {
                let mut j: u64 = 0;
                while j < 10
                    invariant j <= 10
                    decreases 10 - j
                {
                    if j == 8 {
                        break 'outer;
                    }
                    j = j + 1;
                }
                i = i + 1;
            }
        }
    }
}
