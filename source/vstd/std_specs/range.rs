use super::super::prelude::*;
use super::super::view::View;
use super::cmp::{PartialOrdIs, PartialOrdSpec};
use super::iter::{IteratorSpec, StepSpec, StepSpecImpl};
use core::ops::{
    Bound, Range, RangeBounds, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
};

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

// To allow reasoning about the returned range when the executable
// function `RangeInclusive::new()` is invoked in a `for` loop header
// (e.g., in `for x in it: start..=end { ... }`), we need to specify the
// behavior of the constructed range in spec mode. To do that, we add
// `#[verifier::when_used_as_spec(spec_range_inclusive_new)]` to the
// specification for the executable `RangeInclusive::new` method and define
// that spec function here.
pub uninterp spec fn spec_range_inclusive_new<Idx>(
    start: Idx,
    end: Idx,
) -> core::ops::RangeInclusive<Idx>;

pub broadcast axiom fn axiom_spec_range_inclusive_new<Idx>(start: Idx, end: Idx)
    ensures
        (#[trigger] spec_range_inclusive_new(start, end))@ == {
            RangeInclusiveView { start, end, exhausted: false }
        },
;

#[verifier::when_used_as_spec(spec_range_inclusive_new)]
pub assume_specification<Idx>[ RangeInclusive::<Idx>::new ](start: Idx, end: Idx) -> (ret:
    core::ops::RangeInclusive<Idx>)
    ensures
        ret == spec_range_inclusive_new(start, end),
;

impl<A: core::iter::Step> super::iter::IteratorSpecImpl for Range<A> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    open spec fn remaining(&self) -> Seq<Self::Item> {
        Seq::new(
            self.start.spec_steps_between_int(self.end) as nat,
            |i: int| self.start.spec_forward_checked_int(i).unwrap(),
        )
    }

    uninterp spec fn will_return_none(&self) -> bool;

    #[verifier::prophetic]
    open spec fn initial_value_relation(&self, init: &Self) -> bool {
        // Standard invariant for the iterator itself:
        //   If there are no steps between start and end, then remaining is empty;
        //   otherwise it contains all of the steps in between start and end
        &&& (self.start.spec_steps_between_int(self.end) <= 0 && IteratorSpec::remaining(self).len()
            == 0) || (self.start.spec_steps_between_int(self.end) == IteratorSpec::remaining(
            self,
        ).len() as int)
        &&& forall|i: int|
            0 <= i < IteratorSpec::remaining(self).len() ==> #[trigger] IteratorSpec::remaining(
                self,
            )[i] == self.start.spec_forward_checked_int(
                i,
            ).unwrap()
        // Connections to init
        &&& self.start == init.start
        &&& self.end == init.end
        &&& (init.start.spec_steps_between_int(init.end) <= 0 && IteratorSpec::remaining(self).len()
            == 0) || (init.start.spec_steps_between_int(self.end) == IteratorSpec::remaining(
            self,
        ).len() as int)
        &&& forall|i: int|
            0 <= i < IteratorSpec::remaining(self).len() ==> #[trigger] IteratorSpec::remaining(
                self,
            )[i] == init.start.spec_forward_checked_int(i).unwrap()
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

impl<A: core::iter::Step> super::iter::IteratorSpecImpl for RangeInclusive<A> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    open spec fn remaining(&self) -> Seq<Self::Item> {
        Seq::new(
            (self@.start.spec_steps_between_int(self@.end) + 1) as nat,
            |i: int| self@.start.spec_forward_checked_int(i).unwrap(),
        )
    }

    uninterp spec fn will_return_none(&self) -> bool;

    #[verifier::prophetic]
    open spec fn initial_value_relation(&self, init: &Self) -> bool {
        // Standard invariant for the iterator itself:
        //   If there are no steps between start and end, then remaining is empty;
        //   otherwise it contains all of the steps in between start and end
        &&& (self@.start.spec_steps_between_int(self@.end) + 1 <= 0 && IteratorSpec::remaining(
            self,
        ).len() == 0) || (self@.start.spec_steps_between_int(self@.end) + 1
            == IteratorSpec::remaining(self).len() as int)
        &&& forall|i: int|
            0 <= i < IteratorSpec::remaining(self).len() ==> #[trigger] IteratorSpec::remaining(
                self,
            )[i] == self@.start.spec_forward_checked_int(
                i,
            ).unwrap()
        // Connections to init
        &&& self@.start == init@.start
        &&& self@.end == init@.end
        &&& (init@.start.spec_steps_between_int(init@.end) + 1 <= 0 && IteratorSpec::remaining(
            self,
        ).len() == 0) || (init@.start.spec_steps_between_int(self@.end) + 1
            == IteratorSpec::remaining(self).len() as int)
        &&& forall|i: int|
            0 <= i < IteratorSpec::remaining(self).len() ==> #[trigger] IteratorSpec::remaining(
                self,
            )[i] == init@.start.spec_forward_checked_int(i).unwrap()
    }

    open spec fn decrease(&self) -> Option<nat> {
        Some((self@.start.spec_steps_between_int(self@.end) + 1) as nat)
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index <= self@.start.spec_steps_between_int(self@.end) + 1 {
            Some(self@.start.spec_forward_checked_int(index).unwrap())
        } else {
            None
        }
    }
}

pub assume_specification<A: core::iter::Step>[ <Range<A> as Iterator>::next ](
    range: &mut Range<A>,
) -> (r: Option<A>)
    ensures
        (*final(range), r) == spec_range_next(*old(range)),
;

/// Spec model of [`core::ops::Bound`], used by [`RangeBoundsSpec`] to describe
/// the start and end bounds of a range. See [`spec_bound`] for the connection
/// to `Bound` values.
pub enum SpecBound<T> {
    Included(T),
    Excluded(T),
    Unbounded,
}

impl<'a, T> SpecBound<T> {
    /// Borrow the contents of a `SpecBound<T>` as a `SpecBound<&T>`, mirroring
    /// [`core::ops::Bound::as_ref`].
    pub open spec fn as_ref(self) -> SpecBound<&'a T> {
        match self {
            SpecBound::Included(value) => SpecBound::Included(&value),
            SpecBound::Excluded(value) => SpecBound::Excluded(&value),
            SpecBound::Unbounded => SpecBound::Unbounded,
        }
    }
}

/// Spec model of a [`core::ops::Bound`] value as a [`SpecBound`].
pub open spec fn spec_bound<T>(bound: Bound<T>) -> SpecBound<T> {
    match bound {
        Bound::Included(value) => SpecBound::Included(value),
        Bound::Excluded(value) => SpecBound::Excluded(value),
        Bound::Unbounded => SpecBound::Unbounded,
    }
}

#[verifier::external_type_specification]
pub struct ExBound<T>(Bound<T>);

#[verifier::external_type_specification]
pub struct ExRangeFull(RangeFull);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(Idx)]
pub struct ExRangeFrom<Idx>(RangeFrom<Idx>);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(Idx)]
pub struct ExRangeTo<Idx>(RangeTo<Idx>);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(Idx)]
pub struct ExRangeToInclusive<Idx>(RangeToInclusive<Idx>);

// Per-type specifications for `RangeBounds::start_bound`/`end_bound`, so these
// methods can also be called directly in exec code (not just via the spec-mode
// models above). Each spec agrees with the corresponding `RangeBoundsSpecImpl`.
pub assume_specification<'s, T>[ <Range<T> as RangeBounds<T>>::start_bound ](
    range: &'s Range<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Included(&range.start),
;

pub assume_specification<'s, T>[ <Range<T> as RangeBounds<T>>::end_bound ](
    range: &'s Range<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Excluded(&range.end),
;

pub assume_specification<'s, T: ?Sized>[ <RangeFull as RangeBounds<T>>::start_bound ](
    range: &'s RangeFull,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Unbounded,
;

pub assume_specification<'s, T: ?Sized>[ <RangeFull as RangeBounds<T>>::end_bound ](
    range: &'s RangeFull,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Unbounded,
;

pub assume_specification<'s, T>[ <RangeFrom<T> as RangeBounds<T>>::start_bound ](
    range: &'s RangeFrom<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Included(&range.start),
;

pub assume_specification<'s, T>[ <RangeFrom<T> as RangeBounds<T>>::end_bound ](
    range: &'s RangeFrom<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Unbounded,
;

pub assume_specification<'s, T>[ <RangeTo<T> as RangeBounds<T>>::start_bound ](
    range: &'s RangeTo<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Unbounded,
;

pub assume_specification<'s, T>[ <RangeTo<T> as RangeBounds<T>>::end_bound ](
    range: &'s RangeTo<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Excluded(&range.end),
;

pub assume_specification<'s, T>[ <RangeInclusive<T> as RangeBounds<T>>::start_bound ](
    range: &'s RangeInclusive<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Included(&range@.start),
;

pub assume_specification<'s, T>[ <RangeInclusive<T> as RangeBounds<T>>::end_bound ](
    range: &'s RangeInclusive<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Included(&range@.end),
;

pub assume_specification<'s, T>[ <RangeToInclusive<T> as RangeBounds<T>>::start_bound ](
    range: &'s RangeToInclusive<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Unbounded,
;

pub assume_specification<'s, T>[ <RangeToInclusive<T> as RangeBounds<T>>::end_bound ](
    range: &'s RangeToInclusive<T>,
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == SpecBound::Included(&range.end),
;

pub assume_specification<'s, T>[ <(Bound<T>, Bound<T>) as RangeBounds<T>>::start_bound ](
    range: &'s (Bound<T>, Bound<T>),
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == spec_bound(range.0).as_ref(),
;

pub assume_specification<'s, T>[ <(Bound<T>, Bound<T>) as RangeBounds<T>>::end_bound ](
    range: &'s (Bound<T>, Bound<T>),
) -> (result: Bound<&'s T>)
    ensures
        spec_bound(result) == spec_bound(range.1).as_ref(),
;

/// Specification for [`core::ops::RangeBounds`], exposing spec-mode models
/// [`spec_start_bound`](RangeBoundsSpec::spec_start_bound) and
/// [`spec_end_bound`](RangeBoundsSpec::spec_end_bound) of the trait's
/// `start_bound`/`end_bound` methods. This mirrors std's normalization of an
/// arbitrary range into a pair of bounds and is the model used by
/// `<[T]>::copy_within` (see `vstd::std_specs::slice`).
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(RangeBoundsSpec via RangeBoundsSpecImpl)]
pub trait ExRangeBounds<T: ?Sized> {
    type ExternalTraitSpecificationFor: RangeBounds<T>;

    spec fn spec_start_bound(&self) -> SpecBound<&T>;

    spec fn spec_end_bound(&self) -> SpecBound<&T>;

    fn start_bound(&self) -> Bound<&T>;

    fn end_bound(&self) -> Bound<&T>;
}

impl<T> RangeBoundsSpecImpl<T> for Range<T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(&self.start)
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Excluded(&self.end)
    }
}

impl<T: ?Sized> RangeBoundsSpecImpl<T> for RangeFull {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Unbounded
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeFrom<T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(&self.start)
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Unbounded
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeTo<T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Excluded(&self.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeInclusive<T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(&self@.start)
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(&self@.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeToInclusive<T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(&self.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for (Bound<T>, Bound<T>) {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        spec_bound(self.0).as_ref()
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        spec_bound(self.1).as_ref()
    }
}

impl<'a, T: ?Sized + 'a> RangeBoundsSpecImpl<T> for (Bound<&'a T>, Bound<&'a T>) {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        match self.0 {
            Bound::Included(start) => SpecBound::Included(start),
            Bound::Excluded(start) => SpecBound::Excluded(start),
            Bound::Unbounded => SpecBound::Unbounded,
        }
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        match self.1 {
            Bound::Included(end) => SpecBound::Included(end),
            Bound::Excluded(end) => SpecBound::Excluded(end),
            Bound::Unbounded => SpecBound::Unbounded,
        }
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeFrom<&T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(self.start)
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Unbounded
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeTo<&T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Excluded(self.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for Range<&T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(self.start)
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Excluded(self.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeInclusive<&T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(self@.start)
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(self@.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeToInclusive<&T> {
    open spec fn spec_start_bound(&self) -> SpecBound<&T> {
        SpecBound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> SpecBound<&T> {
        SpecBound::Included(self.end)
    }
}

} // verus!
macro_rules! step_specs {
    ($t: ty, $axiom: ident) => {
        verus! {
        impl StepSpecImpl for $t {
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
                StepSpec::spec_forward_checked_int(self, count as int)
            }
            open spec fn spec_forward_checked_int(self, count: int) -> Option<Self> {
                if self + count <= $t::MAX {
                    Some((self + count) as $t)
                } else {
                    None
                }
            }
            open spec fn spec_backward_checked(self, count: usize) -> Option<Self> {
                StepSpec::spec_backward_checked_int(self, count as int)
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
                StepSpec::spec_is_lt(range.start, range.end) ==>
                    // TODO (not important): use new "matches ==>" syntax here
                    (if let Some(n) = StepSpec::spec_forward_checked(range.start, 1) {
                        spec_range_next(range) == (Range { start: n, ..range }, Some(range.start))
                    } else {
                        true
                    }),
                !StepSpec::spec_is_lt(range.start, range.end) ==>
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
    axiom_spec_range_inclusive_new,
}

} // verus!
