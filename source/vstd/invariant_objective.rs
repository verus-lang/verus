use super::prelude::*;
use crate::invariant::AtomicInvariant;
use crate::invariant::InvariantPredicate;

verus! {

// "lazy" encoding of objective invariants (convenient for now, i don't think we would want this long-term)
// this allows us to reuse the existing open_atomic_invariant! macro
struct ObjectiveAtomicInvariant<K, V, Pred>(pub AtomicInvariant<K, V, Pred>) where
    V: Objective,
    Pred: InvariantPredicate<K, V>,
;

} // verus!
