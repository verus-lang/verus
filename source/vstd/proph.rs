#![allow(unused_variables)]

use super::prelude::*;
use super::modes::*;

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
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct Prophecy<T> {
    v: Ghost<T>,
}

impl<T> Prophecy<T> where T: Structural {
    /// The prophecized value.
    pub uninterp spec fn view(self) -> T;

    /// Allocate a new prophecy variable.
    #[inline(always)]
    #[verifier::external_body]
    pub exec fn new() -> (proph_var: Self) {
        Prophecy::<T> { v: Ghost::assume_new() }
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

#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub tracked struct ProphecyGhost<T> {
    _t: core::marker::PhantomData<T>
}

impl<T> ProphecyGhost<T> {
    #[verifier::prophetic]
    pub uninterp spec fn value(&self) -> T;

    pub axiom fn new() -> (tracked proph_var: Self);

    pub axiom fn resolve(tracked self, value: T)
        ensures
            self.value() == value;

    pub axiom fn resolve_dependent<U>(tracked self, tracked u: &ProphecyGhost<U>, f: spec_fn(U) -> T)
        ensures
            self.value() == f(u.value());

    pub axiom fn resolve_dependent_2<U, V>(tracked self, tracked u: &ProphecyGhost<U>, tracked v: &ProphecyGhost<V>, f: spec_fn(U, V) -> T)
        ensures
            self.value() == f(u.value(), v.value());
}

pub tracked struct ProphecySeq<T> {
    tracked var: ProphecyGhost<Seq<T>>,
}

impl<T> ProphecySeq<T> {
    #[verifier::prophetic]
    pub closed spec fn seq(&self) -> Seq<T> {
        self.var.value()
    }

    pub proof fn new() -> (tracked proph_var: Self) {
        ProphecySeq { var: ProphecyGhost::new() }
    }

    pub proof fn resolve_cons(tracked &mut self, v: T)
        ensures
            old(self).seq() == seq![v] + self.seq()
    {
        let tracked mut var = ProphecyGhost::new();
        tracked_swap(&mut var, &mut self.var);
        var.resolve_dependent(&self.var, |w| seq![v] + w);
    }

    pub proof fn resolve_nil(tracked self)
        ensures
            self.seq() === seq![]
    {
        let tracked ProphecySeq { var } = self;
        var.resolve(seq![]);
    }
}

} // verus!
