use super::super::prelude::*;
use super::algebra::ResourceAlgebra;

verus! {

/// The preorder relation.
/// `incl(a, b)` (or a ≼ b) means that there is some `c` such that `a · c == b`
pub open spec fn incl<RA: ResourceAlgebra>(a: RA, b: RA) -> bool {
    exists|c| RA::op(a, c) == b
}

pub open spec fn conjunct_shared<RA: ResourceAlgebra>(a: RA, b: RA, c: RA) -> bool {
    forall|p: RA| p.valid() && incl(a, p) && incl(b, p) ==> #[trigger] incl(c, p)
}

/// A frame preserving update is an update of a value from `a --> b` such that every value `c`
/// that could compose with `a` (also called the frame) can still compose with `b`.
pub open spec fn frame_preserving_update<RA: ResourceAlgebra>(a: RA, b: RA) -> bool {
    forall|c| #![trigger RA::op(a, c), RA::op(b, c)] RA::op(a, c).valid() ==> RA::op(b, c).valid()
}

/// A nondeterministic version of a [`frame_preserving_update`].
pub open spec fn frame_preserving_update_nondeterministic<RA: ResourceAlgebra>(a: RA, bs: Set<RA>) -> bool {
    forall|c|
        #![trigger RA::op(a, c)]
        RA::op(a, c).valid() ==> exists|b| #[trigger] bs.contains(b) && RA::op(b, c).valid()
}

/// The set of values such that can be created by composing an element of `s` with `t`.
pub open spec fn set_op<RA: ResourceAlgebra>(s: Set<RA>, t: RA) -> Set<RA> {
    Set::new(|v| exists|q| s.contains(q) && v == RA::op(q, t))
}

} // verus!
