use super::prelude::*;

// This file implements prophecy variables.
//
// A prophecy variable is represented by a Prophecy<T>, and predicts some value
// of type T.
//
// A prophecy can be allocated by calling Prophecy::<T>::alloc() in exec mode.
// The result is a prophecy variable whose view is an arbitrary value of type T.
//
// A prophecy can be resolved by calling Prophecy::<T>::resolve() in exec mode.
// This call ensures that the view of the prophecy variable is equal to the value
// passed to resolve().  This call (and in particular, its argument v) must be
// exec-mode to avoid circular dependency on the value of the prophecy variable.
//
// An informal soundness argument (following the Future-is-ours paper) is that,
// for any execution of the program, there is some sequence of calls to resolve(),
// whose values do not depend on spec- or proof-mode values.  Those values can be
// plugged into the arbitrary ghost values chosen by alloc(), for the corresponding
// prophecy variables, to justify the proof accompanying the program.  Since both
// alloc() and resolve() are exec-mode, there is no ambiguity about which alloc()
// call corresponds to a particular resolve() value.

verus! {

pub struct Prophecy<T> {
    v: Ghost<T>,
}

impl<T> Prophecy<T> where T: Structural {
    pub closed spec fn view(self) -> T {
        self.v@
    }

    #[inline(always)]
    pub exec fn new() -> (result: Self) {
        Prophecy::<T> { v: Ghost(arbitrary()) }
    }

    #[inline(always)]
    #[verifier::external_body]
    pub exec fn resolve(self, v: &T)
        ensures
            self@ == v,
    {
    }
}

} // verus!
