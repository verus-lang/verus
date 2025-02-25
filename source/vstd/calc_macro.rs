//! The [`calc`] macro provides support for reasoning about a structured proof calculation.
#![allow(unused_imports)]
use super::pervasive::*;
use super::prelude::*;

verus! {

/// The `calc!` macro supports structured proofs through calculations.
///
/// In particular, one can show `a_1 R a_n` for some transitive relation `R` by performing a series
/// of steps `a_1 R a_2`, `a_2 R a_3`, ... `a_{n-1} R a_n`. The calc macro provides both convenient
/// syntax sugar to perform such a proof conveniently, without repeating oneself too often, or
/// exposing the internal steps to the outside context.
///
/// The expected usage looks like:
///
/// ```
/// calc! {
///   (R)
///   a_1; { /* proof that a_1 R a_2 */ }
///   a_2; { /* proof that a_2 R a_3 */ }
///    ...
///   a_n;
/// }
/// ```
///
/// Currently, the `calc!` macro supports common transitive relations for `R`, and this set of
/// relations may be extended in the future.
///
/// Note that `calc!` also supports stating intermediate relations, as long as they are consistent
/// with the main relation `R`. If consistency cannot be immediately shown, Verus will give a
/// helpful message about this. Intermediate relations can be specified by placing them right before
/// the proof block of that step.
///
/// A simple example of using intermediate relations looks like:
///
/// ```
/// let x: int = 2;
/// let y: int = 5;
/// calc! {
///   (<=)
///   x; (==) {}
///   5 - 3; (<) {}
///   5; {} // Notice that no intermediate relation is specified here, so `calc!` will consider the top-level relation `R`; here `<=`.
///   y;
/// }
/// ```
#[allow(unused_macros)]
#[macro_export]
macro_rules! calc {
    ($($tt:tt)*) => {
        ::builtin_macros::calc_proc_macro!($($tt)*)
    };
}

pub use calc;

} // verus!
