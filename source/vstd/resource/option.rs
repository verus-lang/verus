use super::super::prelude::*;
use super::algebra::ResourceAlgebra;
use super::pcm::PCM;
use super::relations::*;

verus! {

impl<RA: ResourceAlgebra> ResourceAlgebra for Option<RA> {
    /// Whether an element is valid
    open spec fn valid(self) -> bool {
        match self {
            Some(v) => v.valid(),
            None => true,
        }
    }

    /// Compose two elements
    open spec fn op(a: Self, b: Self) -> Self {
        match (a, b) {
            (Some(a), Some(b)) => Some(RA::op(a, b)),
            (None, _) => b,
            (_, None) => a,
        }
    }

    /// The operation is associative
    proof fn associative(a: Self, b: Self, c: Self) {
        match (a, b, c) {
            (Some(a), Some(b), Some(c)) => RA::associative(a, b, c),
            (_, _, _) => {},
        }
    }

    /// The operation is commutative
    proof fn commutative(a: Self, b: Self) {
        match (a, b) {
            (Some(a), Some(b)) => RA::commutative(a, b),
            (_, _) => {},
        }
    }

    /// The operation is closed under inclusion
    /// (i.e., if the result of the operation is valid then its parts are also valid)
    proof fn valid_op(a: Self, b: Self) {
        match (a, b) {
            (Some(a), Some(b)) => RA::valid_op(a, b),
            (_, _) => {},
        }
    }
}

impl<RA: ResourceAlgebra> PCM for Option<RA> {
    open spec fn unit() -> Self {
        None
    }

    /// The core of an element `a` is, by definition, some other element `x`
    /// such that `a op x = a`
    proof fn op_unit(self) {
    }

    /// The unit is always a valid element
    proof fn unit_valid() {
    }
}

pub proof fn lemma_incl_opt<RA: ResourceAlgebra>(a: RA, b: RA)
    requires
        incl::<RA>(a, b),
    ensures
        incl::<Option<RA>>(Some(a), Some(b)),
{
    let c = choose|x| RA::op(a, x) == b;
    assert(Option::<RA>::op(Some(a), Some(c)) == Some(b));
}

pub proof fn lemma_incl_opt_rev<RA: ResourceAlgebra>(a: RA, b: RA)
    requires
        incl::<Option<RA>>(Some(a), Some(b)),
    ensures
        incl::<RA>(a, b) || a == b,
{
    let c = choose|x| Option::<RA>::op(Some(a), x) == Some(b);
    if c is None {
        Some(a).op_unit();
    }
}

pub proof fn lemma_set_op_opt<RA: ResourceAlgebra>(s: Set<RA>, t: RA)
    ensures
        set_op(s, t).map(|b| Some(b)) == set_op(s.map(|x| Some(x)), Some(t)),
{
    broadcast use super::super::set::group_set_axioms;

    let s_mapped = s.map(|x| Some(x));
    let original = set_op(s, t);
    let map_after = original.map(|b| Some(b));
    let map_before = set_op(s_mapped, Some(t));

    assert forall|v| map_after.contains(v) implies map_before.contains(v) by {
        let q = choose|q| #[trigger] s.contains(q) && v->Some_0 == RA::op(q, t);
        assert(s_mapped.contains(Some(q)));
    }

    assert forall|v| map_before.contains(v) implies map_after.contains(v) by {
        let q = choose|q| #[trigger] s_mapped.contains(q) && v == Option::<RA>::op(q, Some(t));
        assert(original.contains(v->Some_0));
    }
}

} // verus!
