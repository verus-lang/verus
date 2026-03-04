use super::prelude::*;
use crate::invariant::AtomicInvariant;
use crate::invariant::InvariantPredicate;
use crate::atomic_relaxed::Objective;

verus! {

// "lazy" encoding of objective invariants (convenient for now, i don't think we would want this long-term)
// this allows us to reuse the existing open_atomic_invariant! macro
pub struct ObjectiveAtomicInvariant<K, V, Pred>(pub AtomicInvariant<K, V, Pred>) where
    V: Objective,
    Pred: InvariantPredicate<K, V>,
;

impl<K, V, Pred> ObjectiveAtomicInvariant<K, V, Pred> where
    V: Objective,
    Pred: InvariantPredicate<K, V>,
{
    pub open spec fn constant(&self) -> K {
        self.0.constant()
    }

    pub open spec fn namespace(&self) -> int {
        self.0.namespace()
    }

    pub proof fn new(k: K, tracked v: V, ns: int) -> (tracked i: Self)
        requires
            Pred::inv(k, v),
        ensures
            i.constant() == k,
            i.namespace() == ns
    {
        let tracked at_inv = AtomicInvariant::new(k, v, ns);
        ObjectiveAtomicInvariant(at_inv)
    }
}

} // verus!
