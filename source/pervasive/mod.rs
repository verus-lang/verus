pub mod map;
pub mod option;
pub mod result;
pub mod vec;
pub mod seq;
pub mod seq_lib;
pub mod set;
pub mod set_lib;
pub mod cell;
pub mod ptr;
pub mod invariant;
pub mod atomic;
pub mod atomic_ghost;
pub mod modes;
pub mod multiset;
pub mod state_machine_internal;
pub mod thread;

#[allow(unused_imports)]
use builtin::*;

#[proof]
pub fn assume(b: bool) {
    ensures(b);

    admit();
}

#[proof]
#[verifier(custom_req_err("assertion failure"))]
pub fn assert(b: bool) {
    requires(b);
    ensures(b);
}

#[proof]
pub fn affirm(b: bool) {
    requires(b);
}

/// A tool to check one's reasoning while writing complex spec functions.
/// Not intended to be used as a mechanism for instantiating quantifiers, `spec_affirm` should
/// be removed from spec functions once they are complete.
///
/// ## Example
///
/// ```rust
/// #[spec(checked)] fn some_predicate(a: nat) -> bool {
///     recommends(a < 100);
///     if (a >= 50) {
///         let _ = spec_affirm(50 <= a && a < 100);
///         a >= 75
///     } else {
///         let _ = spec_affirm(a < 50);
///         // let _ = spec_affirm(a < 40); would raise a recommends note here
///         a < 25
///     }
/// }
/// ```
#[spec] pub fn spec_affirm(b: bool) -> bool {
    recommends(b);
    b
}

/// In spec, all types are inhabited
#[spec]
#[verifier(external_body)]
#[allow(dead_code)]
pub fn arbitrary<A>() -> A {
    unimplemented!()
}

#[proof]
#[verifier(returns(proof))]
#[verifier(external_body)]
#[allow(dead_code)]
pub fn proof_from_false<A>() -> A {
    requires(false);

    unimplemented!()
}

#[verifier(external_body)]
#[allow(dead_code)]
pub fn unreached<A>() -> A {
    requires(false);

    panic!("unreached_external")
}

#[verifier(external_body)]
pub fn print_u64(i: u64) {
    println!("{}", i);
}

/// Allows you to prove a boolean predicate by assuming its negation and proving
/// a contradiction. Equivalent to writing `if !b { /* proof here */; assert(false); }`
/// but is more concise and documents intent.
///
/// ```rust
/// assert_by_contradiction!(b, {
///     // assume !b here
///     // prove `false`
/// });
/// ```

#[macro_export]
macro_rules! assert_by_contradiction_macro {
    ($predicate:expr, $bblock:block) => {
        ::builtin::assert_by($predicate, {
            if !$predicate {
                $bblock
                crate::pervasive::assert(false);
            }
        });
    }
}
#[macro_export]
macro_rules! assert_by_contradiction {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(assert_by_contradiction_macro!($($a)*))
    }
}
