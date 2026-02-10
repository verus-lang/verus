use super::super::prelude::*;
use super::super::view::View;
use super::cmp::{PartialOrdIs, PartialOrdSpec};
use crate::std_specs::iter::IteratorSpec;
use core::ops::{Range, RangeInclusive};

verus! {

#[verifier::external_type_specification]
#[verifier::reject_recursive_types_in_ground_variants(Idx)]
pub struct ExRange<Idx>(Range<Idx>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types_in_ground_variants(Idx)]
pub struct ExRangeInclusive<Idx>(RangeInclusive<Idx>);

pub struct RangeInclusiveView<Idx> {
    pub start: Idx,
    pub end: Idx,
    pub exhausted: bool,
}

pub trait ContainsSpec<Idx, U> where Idx: PartialOrd<U>, U: ?Sized + PartialOrd<Idx> {
    spec fn obeys_contains() -> bool;

    spec fn contains_spec(&self, i: &U) -> bool;
}

impl<Idx, U> ContainsSpec<Idx, U> for RangeInclusive<Idx> where
    Idx: PartialOrd<U>,
    U: ?Sized + PartialOrd<Idx>,
 {
    open spec fn obeys_contains() -> bool {
        (U::obeys_partial_cmp_spec() && <Idx as PartialOrdSpec<U>>::obeys_partial_cmp_spec())
    }

    open spec fn contains_spec(&self, i: &U) -> bool {
        self@.start.is_le(&i) && if self@.exhausted {
            i.is_lt(&self@.end)
        } else {
            i.is_le(&self@.end)
        }
    }
}

impl<Idx, U> ContainsSpec<Idx, U> for Range<Idx> where
    Idx: PartialOrd<U>,
    U: ?Sized + PartialOrd<Idx>,
 {
    open spec fn obeys_contains() -> bool {
        (U::obeys_partial_cmp_spec() && <Idx as PartialOrdSpec<U>>::obeys_partial_cmp_spec())
    }

    open spec fn contains_spec(&self, i: &U) -> bool {
        self.start.is_le(&i) && i.is_lt(&self.end)
    }
}

impl<Idx> View for RangeInclusive<Idx> {
    type V = RangeInclusiveView<Idx>;

    uninterp spec fn view(&self) -> Self::V;
}

pub trait StepSpec where Self: Sized {
    // REVIEW: it would be nice to be able to use SpecOrd::spec_lt (not yet supported)
    // TODO: We should now be able to use cmp_spec or partial_cmp_spec here.
    spec fn spec_is_lt(self, other: Self) -> bool;

    spec fn spec_steps_between(self, end: Self) -> Option<usize>;

    spec fn spec_steps_between_int(self, end: Self) -> int;

    spec fn spec_forward_checked(self, count: usize) -> Option<Self>;

    spec fn spec_forward_checked_int(self, count: int) -> Option<Self>;

    spec fn spec_backward_checked(self, count: usize) -> Option<Self>;

    spec fn spec_backward_checked_int(self, count: int) -> Option<Self>;
}

pub uninterp spec fn spec_range_next<A>(a: Range<A>) -> (Range<A>, Option<A>);

/// Range::contains method is valid and safe to use only when cmp operations are implemented to satisfy
/// obeys_partial_cmp_spec. Specifically, the comparison must be deterministic, and `lt` (less than)
/// and `le` (less than or equal to) must define total orders.
/// If using Range::contains with types that do not satisfy obeys_partial_cmp_spec, no spec is provided.
pub assume_specification<Idx: PartialOrd<Idx>, U>[ Range::<Idx>::contains ](
    r: &Range<Idx>,
    i: &U,
) -> (ret: bool) where Idx: PartialOrd<U>, U: ?Sized + PartialOrd<Idx>
    ensures
        <Range::<Idx> as ContainsSpec<Idx, U>>::obeys_contains() ==> ret == r.contains_spec(i),
;

pub assume_specification<Idx: PartialOrd<Idx>, U>[ RangeInclusive::<Idx>::contains ](
    r: &RangeInclusive<Idx>,
    i: &U,
) -> (ret: bool) where Idx: PartialOrd<U>, U: ?Sized + PartialOrd<Idx>
    ensures
        <RangeInclusive::<Idx> as ContainsSpec<Idx, U>>::obeys_contains() ==> ret
            == r.contains_spec(i),
;

pub assume_specification<Idx>[ RangeInclusive::<Idx>::new ](start: Idx, end: Idx) -> (ret:
    core::ops::RangeInclusive<Idx>)
    ensures
        ret@.start == start,
        ret@.end == end,
        ret@.exhausted == false,
;

impl<A: core::iter::Step + StepSpec> crate::std_specs::iter::IteratorSpecImpl for Range<A> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    open spec fn seq(&self) -> Seq<Self::Item> {
        Seq::new(
            self.start.spec_steps_between_int(self.end) as nat,
            |i: int| self.start.spec_forward_checked_int(i).unwrap(),
        )
    }

    uninterp spec fn completes(&self) -> bool;

    #[verifier::prophetic]
    open spec fn initial_value_inv(&self, init: Option<&Self>) -> bool {
        &&& IteratorSpec::seq(self) == Seq::new(
            self.start.spec_steps_between_int(self.end) as nat,
            |i: int| self.start.spec_forward_checked_int(i).unwrap(),
        )
        &&& init matches Some(v) ==> {
            &&& self.start == v.start
            &&& self.end == v.end
            &&& IteratorSpec::seq(self) == Seq::new(
                v.start.spec_steps_between_int(v.end) as nat,
                |i: int| v.start.spec_forward_checked_int(i).unwrap(),
            )
        }
    }

    open spec fn decrease(&self) -> Option<nat> {
        Some(self.start.spec_steps_between_int(self.end) as nat)
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        //Some(self.start.spec_forward_checked_int(index).unwrap())
        if 0 <= index <= self.start.spec_steps_between_int(self.end) {
            Some(self.start.spec_forward_checked_int(index).unwrap())
        } else {
            None
        }
    }
}

pub assume_specification<A: std::iter::Step>[ <Range<A> as Iterator>::next ](
    range: &mut Range<A>,
) -> (r: Option<A>)
    ensures
        (*range, r) == spec_range_next(*old(range)),
;

} // verus!
macro_rules! step_specs {
    ($t: ty, $axiom: ident) => {
        verus! {
        impl StepSpec for $t {
            open spec fn spec_is_lt(self, other: Self) -> bool {
                self < other
            }
            open spec fn spec_steps_between(self, end: Self) -> Option<usize> {
                let n = end - self;
                if usize::MIN <= n <= usize::MAX {
                    Some(n as usize)
                } else {
                    None
                }
            }
            open spec fn spec_steps_between_int(self, end: Self) -> int {
                end - self
            }
            open spec fn spec_forward_checked(self, count: usize) -> Option<Self> {
                self.spec_forward_checked_int(count as int)
            }
            open spec fn spec_forward_checked_int(self, count: int) -> Option<Self> {
                if self + count <= $t::MAX {
                    Some((self + count) as $t)
                } else {
                    None
                }
            }
            open spec fn spec_backward_checked(self, count: usize) -> Option<Self> {
                self.spec_backward_checked_int(count as int)
            }
            open spec fn spec_backward_checked_int(self, count: int) -> Option<Self> {
                if self - count >= $t::MIN {
                    Some((self - count) as $t)
                } else {
                    None
                }
            }
        }
        // TODO: we might be able to make this generic over A: StepSpec
        // once we settle on a way to connect std traits like Step with spec traits like StepSpec.
        pub broadcast proof fn $axiom(range: Range<$t>)
            ensures
                range.start.spec_is_lt(range.end) ==>
                    // TODO (not important): use new "matches ==>" syntax here
                    (if let Some(n) = range.start.spec_forward_checked(1) {
                        spec_range_next(range) == (Range { start: n, ..range }, Some(range.start))
                    } else {
                        true
                    }),
                !range.start.spec_is_lt(range.end) ==>
                    #[trigger] spec_range_next(range) == (range, None::<$t>),
        {
            admit();
        }
        } // verus!
    };
}

step_specs!(u8, axiom_spec_range_next_u8);
step_specs!(u16, axiom_spec_range_next_u16);
step_specs!(u32, axiom_spec_range_next_u32);
step_specs!(u64, axiom_spec_range_next_u64);
step_specs!(u128, axiom_spec_range_next_u128);
step_specs!(usize, axiom_spec_range_next_usize);
step_specs!(i8, axiom_spec_range_next_i8);
step_specs!(i16, axiom_spec_range_next_i16);
step_specs!(i32, axiom_spec_range_next_i32);
step_specs!(i64, axiom_spec_range_next_i64);
step_specs!(i128, axiom_spec_range_next_i128);
step_specs!(isize, axiom_spec_range_next_isize);

verus! {

pub broadcast group group_range_axioms {
    axiom_spec_range_next_u8,
    axiom_spec_range_next_u16,
    axiom_spec_range_next_u32,
    axiom_spec_range_next_u64,
    axiom_spec_range_next_u128,
    axiom_spec_range_next_usize,
    axiom_spec_range_next_i8,
    axiom_spec_range_next_i16,
    axiom_spec_range_next_i32,
    axiom_spec_range_next_i64,
    axiom_spec_range_next_i128,
    axiom_spec_range_next_isize,
    //    axiom_spec_into_iter,
}

} // verus!
