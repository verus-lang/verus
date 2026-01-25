#[cfg(verus_keep_ghost)]
use super::super::modes::tracked_swap;
use super::super::prelude::*;
use super::Loc;
use super::frac::FracGhost;

verus! {

/// See [`GhostVarAuth<T>`] for more information.
pub struct GhostVar<T> {
    frac: FracGhost<T>,
}

impl<T> GhostVar<T> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.frac.frac() == (1 as real) / (2 as real)
    }

    pub closed spec fn id(self) -> Loc {
        self.frac.id()
    }

    pub closed spec fn view(self) -> T {
        self.frac.view()
    }
}

/// `GhostVarAuth<T>` is one half of a pair of tokens—the other being [`GhostVar<T>`].
/// These tokens each track a value, and they can only be allocated or updated together.
/// Thus, the pair of tokens always agree on the value, but they can be owned separately.
///
/// One possible application is to have a library which
/// keeps `GhostVarAuth<T>` and maintains an invariant relating the implementation's
/// abstract state to the value of `GhostVarAuth<T>`.  Both `GhostVarAuth<T>`
/// and [`GhostVar<T>`] are needed together to update the value, but either one alone
/// allows reasoning about the current state.
///
/// These tokens can be implemented using fractional permissions, e.g., [`FracGhost`].
///
/// ### Example
///
/// ```
/// fn example() {
///     let tracked (mut gauth, mut gvar) = GhostVarAuth::<u64>::new(1);
///     assert(gauth@ == 1);
///     assert(gvar@ == 1);
///     proof {
///         gauth.update(&mut gvar, 2);
///     }
///     assert(gauth@ == 2);
///     assert(gvar@ == 2);
/// }
/// ```
pub struct GhostVarAuth<T> {
    frac: FracGhost<T>,
}

impl<T> GhostVarAuth<T> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.frac.frac() == (1 as real) / (2 as real)
    }

    pub closed spec fn id(self) -> Loc {
        self.frac.id()
    }

    pub closed spec fn view(self) -> T {
        self.frac.view()
    }

    /// Allocate a new pair of tokens, each initialized to the given value.
    pub proof fn new(v: T) -> (tracked result: (GhostVarAuth<T>, GhostVar<T>))
        ensures
            result.0.id() == result.1.id(),
            result.0@ == v,
            result.1@ == v,
    {
        let tracked mut f = FracGhost::<T>::new(v);
        let tracked v = GhostVar::<T> { frac: f.split() };
        let tracked a = GhostVarAuth::<T> { frac: f };
        (a, v)
    }

    /// Ensure that both tokens agree on the value.
    pub proof fn agree(tracked &self, tracked v: &GhostVar<T>)
        requires
            self.id() == v.id(),
        ensures
            self@ == v@,
    {
        self.frac.agree(&v.frac)
    }

    /// Update the value on each token.
    pub proof fn update(tracked &mut self, tracked v: &mut GhostVar<T>, new_val: T)
        requires
            old(self).id() == old(v).id(),
        ensures
            self.id() == old(self).id(),
            v.id() == old(v).id(),
            old(self)@ == old(v)@,
            self@ == new_val,
            v@ == new_val,
    {
        let tracked (mut ms, mut mv) = Self::new(new_val);
        tracked_swap(self, &mut ms);
        tracked_swap(v, &mut mv);
        use_type_invariant(&ms);
        use_type_invariant(&mv);
        let tracked mut msfrac = ms.frac;
        msfrac.combine(mv.frac);
        msfrac.update(new_val);
        let tracked mut nv = GhostVar::<T> { frac: msfrac.split() };
        let tracked mut ns = Self { frac: msfrac };
        tracked_swap(self, &mut ns);
        tracked_swap(v, &mut nv);
    }
}

} // verus!
