#![allow(unused_variables)]

use super::prelude::*;

verus! {

/// A "prophecy variable" that predicts some value of type T.
///
/// A prophecy can be allocated by calling [`Prophecy::<T>::new()`] in exec mode.
/// The result is a prophecy variable whose view is an arbitrary value of type T.
///
/// A prophecy can be resolved by calling [`Prophecy::<T>::resolve()`] in exec mode.
/// This call ensures that the view of the prophecy variable is equal to the value
/// passed to `resolve()`.  This call (and in particular, its argument v) must be
/// exec-mode to avoid circular dependency on the value of the prophecy variable.
/// The value cannot have _any_ "ghost content" (not even via `Ghost`);
/// hence the `T: Structural` trait bound.
///
/// We make an informal soundness argument based on the paper
/// [_The Future is Ours: Prophecy Variables in Separation Logic_](https://plv.mpi-sws.org/prophecies/paper.pdf).
/// The argument goes as follows:
/// For any execution of the program, there is some sequence of calls to `resolve()`,
/// whose values do not depend on spec- or proof-mode values.  Those values can be
/// plugged into the arbitrary ghost values chosen by `new()`, for the corresponding
/// prophecy variables, to justify the proof accompanying the program.  Since both
/// `new()` and `resolve()` are exec-mode, there is no ambiguity about which `new()`
/// call corresponds to a particular `resolve()` value.
pub struct Prophecy<T> {
    v: Ghost<T>,
}

impl<T> Prophecy<T> where T: Structural {
    /// The prophecized value.
    pub closed spec fn view(self) -> T {
        self.v@
    }

    /// Allocate a new prophecy variable.
    #[inline(always)]
    pub exec fn new() -> (result: Self) {
        Prophecy::<T> { v: Ghost(arbitrary()) }
    }

    /// Resolve the prophecy variable to a concrete value.
    /// This consumes `self`, so it can only be called once.
    #[inline(always)]
    #[verifier::external_body]
    pub exec fn resolve(self, v: &T)
        ensures
            self@ == v,
    {
    }
}

} // verus!
