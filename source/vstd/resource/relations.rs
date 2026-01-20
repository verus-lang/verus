use super::super::prelude::*;
use super::pcm::PCM;

verus! {

/// The preorder relation.
/// `incl(a, b)` (or a ≼ b) means that there is some `c` such that `a · c == b`
pub open spec fn incl<P: PCM>(a: P, b: P) -> bool {
    exists|c| P::op(a, c) == b
}

pub open spec fn conjunct_shared<P: PCM>(a: P, b: P, c: P) -> bool {
    forall|p: P| p.valid() && incl(a, p) && incl(b, p) ==> #[trigger] incl(c, p)
}

/// A frame preserving update is an update of a PCM value from `a --> b` such that every value `c`
/// that could compose with `a` (also called the frame) can still compose with `b`.
pub open spec fn frame_preserving_update<P: PCM>(a: P, b: P) -> bool {
    forall|c| #![trigger P::op(a, c), P::op(b, c)] P::op(a, c).valid() ==> P::op(b, c).valid()
}

/// A nondeterministic version of a [`frame_preserving_update`].
pub open spec fn frame_preserving_update_nondeterministic<P: PCM>(a: P, bs: Set<P>) -> bool {
    forall|c|
        #![trigger P::op(a, c)]
        P::op(a, c).valid() ==> exists|b| #[trigger] bs.contains(b) && P::op(b, c).valid()
}

/// The set of values such that can be created by composing an element of `s` with `t`.
pub open spec fn set_op<P: PCM>(s: Set<P>, t: P) -> Set<P> {
    Set::new(|v| exists|q| s.contains(q) && v == P::op(q, t))
}

} // verus!
