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
    ps: ProphecySeq<T>,
}

impl<T> Prophecy<T> where T: Structural {
    /// The prophecized value.
    pub closed spec fn view(self) -> T {
        if self.ps@.len() > 0 {
            self.ps@[0]
        } else {
            arbitrary()
        }
    }

    /// Allocate a new prophecy variable.
    #[inline(always)]
    pub exec fn new() -> (result: Self) {
        Prophecy::<T> { ps: ProphecySeq::<T>::new() }
    }

    /// Resolve the prophecy variable to a concrete value.
    /// This consumes `self`, so it can only be called once.
    #[inline(always)]
    pub exec fn resolve(self, v: &T)
        ensures
            self@ == v,
    {
        broadcast use super::seq::group_seq_axioms;
        let mut mself = self;
        mself.ps.resolve(v);
    }
}

/// [`ProphecySeq::<T>`] represents a sequence of predictions of type T.
/// It can be allocated by calling [`ProphecySeq::<T>::new()`] in exec mode,
/// and it can be resolved iteratively by calling [`ProphecySeq::<T>::resolve()`]
/// in exec mode to resolve the next element of the sequence.  This mirrors
/// the notion of typed sequence prophecies from section 2.3 of the paper
/// [_The Future is Ours: Prophecy Variables in Separation Logic_](https://plv.mpi-sws.org/prophecies/paper.pdf).
pub struct ProphecySeq<T> {
    vs: Ghost<Seq<T>>,
}

impl<T> ProphecySeq<T> where T: Structural {
    /// The prophecized sequence of values.
    pub closed spec fn view(self) -> Seq<T> {
        self.vs@
    }

    /// Allocate a new sequence-prophecy variable.
    #[inline(always)]
    pub exec fn new() -> (result: Self) {
        ProphecySeq::<T> { vs: Ghost(arbitrary()) }
    }

    /// Resolve the next element in the sequence prophecy variable
    /// to a concrete value.  The remaining prophecy variable becomes
    /// the prediction of the subsequent elements of the sequence.
    #[inline(always)]
    #[verifier::external_body]
    pub exec fn resolve(&mut self, v: &T)
        ensures
            old(self)@ == seq![*v] + self@,
    {
    }
}

} // verus!
