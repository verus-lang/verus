use super::prelude::*;
use core::ops::Range;

verus! {

/// Simplify proofs-by-computation for ranges of values
pub trait RangeAll where Self: Sized {
    spec fn all_spec(self, p: spec_fn(int) -> bool) -> bool;
}

pub open spec fn range_all_spec_rec(r: Range<int>, p: spec_fn(int) -> bool) -> bool
    decreases r.end - r.start,
{
    if r.start >= r.end {
        true
    } else {
        p(r.start) && range_all_spec_rec(r.start + 1..r.end, p)
    }
}

impl RangeAll for Range<int> {
    open spec fn all_spec(self, p: spec_fn(int) -> bool) -> bool {
        range_all_spec_rec(self, p)
    }
}

pub broadcast proof fn all_spec_implies(r: Range<int>, p: spec_fn(int) -> bool)
    ensures
        #[trigger] r.all_spec(p) ==> (forall|i| r.start <= i < r.end ==> #[trigger] p(i)),
    decreases r.end - r.start,
{
    if r.start >= r.end {
    } else {
        all_spec_implies(r.start + 1..r.end, p);
    }
}

} // verus!
