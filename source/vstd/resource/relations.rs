use super::super::prelude::*;
use super::algebra::ResourceAlgebra;
use super::pcm::PCM;

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
pub open spec fn frame_preserving_update<P: PCM>(a: P, b: P) -> bool {
    forall|c| #![trigger P::op(a, c), P::op(b, c)] P::op(a, c).valid() ==> P::op(b, c).valid()
}

/// A nondeterministic version of a [`frame_preserving_update`].
pub open spec fn frame_preserving_update_nondeterministic<P: PCM>(a: P, bs: Set<P>) -> bool {
    forall|c|
        #![trigger P::op(a, c)]
        P::op(a, c).valid() ==> exists|b| #[trigger] bs.contains(b) && P::op(b, c).valid()
}

/// A frame preserving update with support for resource algebras.
/// See [`frame_preserving_update`] for more details.
/// The difference lies in the fact that for [`PCM`]s there is always a unit
///
pub open spec fn frame_preserving_update_opt<RA: ResourceAlgebra>(a: RA, b: RA) -> bool {
    forall|c|
        #![trigger Option::<RA>::op(Some(a), c), Option::<RA>::op(Some(b), c)]
        Option::<RA>::op(Some(a), c).valid() ==> Option::<RA>::op(Some(b), c).valid()
}

/// A nondeterministic version of a [`frame_preserving_update_opt`].
pub open spec fn frame_preserving_update_nondeterministic_opt<RA: ResourceAlgebra>(
    a: RA,
    bs: Set<RA>,
) -> bool {
    forall|c|
        #![trigger Option::<RA>::op(Some(a), c)]
        Option::<RA>::op(Some(a), c).valid() ==> exists|b| #[trigger]
            bs.contains(b) && Option::<RA>::op(Some(b), c).valid()
}

/// The set of values such that can be created by composing an element of `s` with `t`.
pub open spec fn set_op<RA: ResourceAlgebra>(s: Set<RA>, t: RA) -> Set<RA> {
    Set::new(|v| exists|q| s.contains(q) && v == RA::op(q, t))
}

pub proof fn lemma_incl_transitive<RA: ResourceAlgebra>(a: RA, b: RA, c: RA)
    requires
        incl(a, b),
        incl(b, c),
    ensures
        incl(a, c),
{
    let ax = choose|ax| RA::op(a, ax) == b;
    let bx = choose|bx| RA::op(b, bx) == c;
    assert(RA::op(RA::op(a, ax), bx) == c);
    RA::associative(a, ax, bx);
    assert(RA::op(a, RA::op(ax, bx)) == c);
}

pub proof fn lemma_frame_preserving_opt<RA: ResourceAlgebra>(a: RA, b: RA)
    requires
        frame_preserving_update_opt::<RA>(a, b),
    ensures
        frame_preserving_update::<Option<RA>>(Some(a), Some(b)),
{
}

pub proof fn lemma_frame_preserving_update_nondeterministic_opt<RA: ResourceAlgebra>(
    a: RA,
    bs: Set<RA>,
)
    requires
        frame_preserving_update_nondeterministic_opt::<RA>(a, bs),
    ensures
        frame_preserving_update_nondeterministic::<Option<RA>>(Some(a), bs.map(|b| Some(b))),
{
    broadcast use super::super::set::group_set_axioms;

    let bs_mapped = bs.map(|b| Some(b));
    assert forall|c|
        #![trigger Option::<RA>::op(Some(a), c)]
        Option::<RA>::op(Some(a), c).valid() implies exists|b| #[trigger]
        bs_mapped.contains(b) && Option::<RA>::op(b, c).valid() by {
        let b = choose|b| #[trigger] bs.contains(b) && Option::<RA>::op(Some(b), c).valid();
        assert(bs_mapped.contains(Some(b)));
    }
}

} // verus!
