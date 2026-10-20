use super::super::prelude::*;
use super::super::view::View;
use super::cmp::{PartialEqSpec, PartialOrdIs, PartialOrdSpec};
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

/// The wrapping value used by Rust's integer Step implementations.
#[verifier::opaque]
pub open spec fn step_spec_wrapping_value(value: int, count: int, lower: int, upper: int) -> int {
    lower + (value - lower + count) % (upper - lower + 1)
}

pub broadcast proof fn lemma_step_spec_wrapping_value(
    value: int,
    count: int,
    lower: int,
    upper: int,
)
    requires
        lower <= value <= upper,
    ensures
        lower <= #[trigger] step_spec_wrapping_value(value, count, lower, upper) <= upper,
        lower <= value + count <= upper ==> step_spec_wrapping_value(value, count, lower, upper)
            == value + count,
{
    reveal(step_spec_wrapping_value);
    let width = upper - lower + 1;
    let offset = value - lower + count;
    crate::arithmetic::div_mod::lemma_mod_bound(offset, width);
    if lower <= value + count <= upper {
        crate::arithmetic::div_mod::lemma_small_mod(offset as nat, width as nat);
    }
}

pub broadcast proof fn lemma_step_spec_wrapping_composition(
    value: int,
    count: int,
    next: int,
    lower: int,
    upper: int,
)
    requires
        lower <= value <= upper,
    ensures
        #[trigger] step_spec_wrapping_value(
            step_spec_wrapping_value(value, count, lower, upper),
            next,
            lower,
            upper,
        ) == step_spec_wrapping_value(value, count + next, lower, upper),
{
    reveal(step_spec_wrapping_value);
    crate::arithmetic::div_mod::lemma_add_mod_noop_right(
        next,
        value - lower + count,
        upper - lower + 1,
    );
}

/// Clones preserve values, and comparisons agree with the signed step distance.
/// Rust's Step invariants require agreement with forward_checked
/// and backward_checked, ordering of reachable endpoints, and zero distance
/// exactly for equal endpoints. See:
/// <https://doc.rust-lang.org/nightly/std/iter/trait.Step.html#tymethod.steps_between>.
#[verifier::opaque]
pub open spec fn step_spec_order_is_well_formed<A: core::iter::Step>() -> bool {
    &&& A::obeys_eq_spec()
    &&& A::obeys_partial_cmp_spec()
    &&& forall|a: A, b: A| #[trigger] cloned(a, b) ==> a == b
    &&& forall|a: A, b: A|
        #![trigger a.spec_steps_between_int(b)]
        {
            let n = a.spec_steps_between_int(b);
            // Step's successor/predecessor order, and steps_between's a <= b law.
            &&& a.eq_spec(&b) == (a == b)
            &&& a.partial_cmp_spec(&b) == Some(
                if n > 0 {
                    core::cmp::Ordering::Less
                } else if n < 0 {
                    core::cmp::Ordering::Greater
                } else {
                    core::cmp::Ordering::Equal
                },
            )
            &&& (n == 0 <==> a
                == b)
            // Signed-distance extension used by the range model.
            &&& n == -b.spec_steps_between_int(a)
            &&& a.spec_steps_between(b) == if 0 <= n <= usize::MAX {
                Some(n as usize)
            } else {
                None
            }
            // steps_between's equivalences with both checked operations.
            &&& n >= 0 ==> a.spec_forward_checked_int(n) == Some(b)
            &&& n >= 0 ==> b.spec_backward_checked_int(n) == Some(
                a,
            )
            // *_unchecked Invariants: any prefix up to a reachable endpoint is
            // safe. A greater/lesser endpoint also gives safety for one step.
            &&& n >= 0 ==> forall|k: int|
                #![trigger a.spec_forward_checked_int(k)]
                0 <= k <= n ==> a.spec_forward_checked_int(k).is_some()
            &&& n >= 0 ==> forall|k: int|
                #![trigger b.spec_backward_checked_int(k)]
                0 <= k <= n ==> b.spec_backward_checked_int(k).is_some()
        }
}

/// The usize and mathematical-count models agree, including zero steps.
#[verifier::opaque]
pub open spec fn step_spec_checked_is_well_formed<A: core::iter::Step>() -> bool {
    &&& forall|a: A, n: usize|
        #![auto]
        {
            // Bridge executable counts to the mathematical range model.
            &&& a.spec_forward_checked(n) == a.spec_forward_checked_int(n as int)
            &&& a.spec_backward_checked(n) == a.spec_backward_checked_int(n as int)
        }
    &&& forall|a: A|
        #![auto]
        {
            // forward_checked/backward_checked Invariants: zero steps are identity.
            &&& a.spec_forward_checked_int(0) == Some(a)
            &&& a.spec_backward_checked_int(0) == Some(a)
        }
}

/// Composition and repeated stepping from the checked methods' invariants:
/// <https://doc.rust-lang.org/nightly/std/iter/trait.Step.html#tymethod.forward_checked>
/// and the corresponding backward_checked section.
///
/// Counts are mathematical integers. For n + m <= usize::MAX this is exactly
/// the docs' checked_add formula; above that limit the literal formula disagrees
/// with Rust's implementation for types wider than usize (e.g. u128). The
/// mathematical extension correctly models those successful composed steps.
#[verifier::opaque]
pub open spec fn step_spec_composition_is_well_formed<A: core::iter::Step>() -> bool {
    &&& forall|a: A, n: int, m: int|
        #![trigger a.spec_forward_checked_int(n), a.spec_forward_checked_int(n + m)]
        n >= 0 && m >= 0 ==> (match a.spec_forward_checked_int(n) {
            Some(b) => b.spec_forward_checked_int(m),
            None => None,
        }) == a.spec_forward_checked_int(n + m)
    &&& forall|a: A, n: int, m: int|
        #![trigger a.spec_backward_checked_int(n), a.spec_backward_checked_int(n + m)]
        n >= 0 && m >= 0 ==> (match a.spec_backward_checked_int(n) {
            Some(b) => b.spec_backward_checked_int(m),
            None => None,
        }) == a.spec_backward_checked_int(
            n + m,
        )
    // Swapping n and m gives the documented commutativity equation.
    // Taking m = 1, together with zero-step identity, is the try_fold law.
}

/// The overflowing methods' checked-result and fold Invariants, including
/// their values after overflow:
/// <https://doc.rust-lang.org/nightly/std/iter/trait.Step.html#tymethod.forward_overflowing>
/// and the corresponding backward_overflowing section.
#[verifier::opaque]
pub open spec fn step_spec_overflowing_is_well_formed<A: core::iter::Step>() -> bool {
    &&& forall|a: A, n: usize|
        #![trigger a.spec_forward_overflowing(n)]
        {
            let (b, overflow) = a.spec_forward_overflowing(n);
            // Checked-result invariant and the documented overflow flag.
            &&& overflow == a.spec_forward_checked(n).is_none()
            &&& !overflow ==> a.spec_forward_checked(n) == Some(
                b,
            )
            // fold(..., (a, false), ...): expand its final iteration.
            &&& n < usize::MAX ==> {
                let (c, next_overflow) = b.spec_forward_overflowing(1);
                a.spec_forward_overflowing((n + 1) as usize) == (c, overflow || next_overflow)
            }
        }
    &&& forall|a: A, n: usize|
        #![trigger a.spec_backward_overflowing(n)]
        {
            let (b, overflow) = a.spec_backward_overflowing(n);
            &&& overflow == a.spec_backward_checked(n).is_none()
            &&& !overflow ==> a.spec_backward_checked(n) == Some(b)
            &&& n < usize::MAX ==> {
                let (c, next_overflow) = b.spec_backward_overflowing(1);
                a.spec_backward_overflowing((n + 1) as usize) == (c, overflow || next_overflow)
            }
        }
    &&& forall|a: A|
        #![auto]
        {
            // The fold's initial value and the documented zero-step corollary.
            &&& a.spec_forward_overflowing(0) == (a, false)
            &&& a.spec_backward_overflowing(0) == (a, false)
        }
        // The composition law when no overflow occurs follows from these
        // checked-result equations and checked composition.

}

/// Successful forward steps preserve distance and compose. These are the
/// forward Invariants (composition, repeated steps, increasing order, and
/// backward(forward(a, n), n) == a), combined with steps_between's equivalences.
#[verifier::opaque]
pub open spec fn step_spec_forward_is_well_formed<A: core::iter::Step>() -> bool {
    &&& forall|a: A, n: int|
        #![trigger a.spec_forward_checked_int(n)]
        n >= 0 ==> (a.spec_forward_checked_int(n) matches Some(b) ==> {
            // steps_between's equivalence with forward_checked.
            &&& a.spec_steps_between_int(b)
                == n
            // Mathematical distance translation used by remaining and decrease.
            &&& forall|end: A|
                #![auto]
                b.spec_steps_between_int(end) == a.spec_steps_between_int(end) - n
            &&& forall|m: int|
                #![auto]
                m >= 0 ==> b.spec_forward_checked_int(m) == a.spec_forward_checked_int(n + m)
        })
}

/// Backward counterparts of the forward Invariants: composition, repeated
/// steps, decreasing order, and forward(backward(a, n), n) == a.
#[verifier::opaque]
pub open spec fn step_spec_backward_is_well_formed<A: core::iter::Step>() -> bool {
    &&& forall|a: A, n: int|
        #![trigger a.spec_backward_checked_int(n)]
        n >= 0 ==> (a.spec_backward_checked_int(n) matches Some(b) ==> {
            // steps_between's equivalence with backward_checked.
            &&& b.spec_steps_between_int(a)
                == n
            // Mathematical distance translation used by reversed ranges.
            &&& forall|start: A|
                #![auto]
                start.spec_steps_between_int(b) == start.spec_steps_between_int(a) - n
            &&& forall|m: int|
                #![auto]
                m >= 0 ==> b.spec_backward_checked_int(m) == a.spec_backward_checked_int(n + m)
        })
}

/// The mathematical laws needed to use a Step model as a finite range.
///
/// Executable Step methods are checked against their models by `StepSpec`.
/// These separate laws also check that the models describe a coherent sequence,
/// and that cloning and comparisons agree with that sequence.
#[verifier::opaque]
pub open spec fn step_spec_is_well_formed<A: core::iter::Step>() -> bool {
    &&& step_spec_order_is_well_formed::<A>()
    &&& step_spec_checked_is_well_formed::<A>()
    &&& step_spec_composition_is_well_formed::<A>()
    &&& step_spec_overflowing_is_well_formed::<A>()
    &&& step_spec_forward_is_well_formed::<A>()
    &&& step_spec_backward_is_well_formed::<A>()
}

pub open spec fn spec_range_next<A: core::iter::Step>(a: Range<A>) -> (Range<A>, Option<A>) {
    if a.start.is_lt(&a.end) {
        match a.start.spec_forward_checked(1) {
            Some(n) => (Range { start: n, ..a }, Some(a.start)),
            None => (a, None),
        }
    } else {
        (a, None)
    }
}

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

// A range is empty once its iterator is exhausted, or if it was never valid
// to begin with (start > end).
pub open spec fn spec_range_inclusive_is_empty<Idx: PartialOrd<Idx>>(
    r: &RangeInclusive<Idx>,
) -> bool {
    !r@.start.is_le(&r@.end) || r@.exhausted
}

pub assume_specification<Idx: PartialOrd<Idx>>[ RangeInclusive::<Idx>::is_empty ](
    r: &RangeInclusive<Idx>,
) -> (res: bool) where Idx: PartialOrd<Idx>
    ensures
        <Idx as PartialOrdSpec<Idx>>::obeys_partial_cmp_spec() ==> res
            == spec_range_inclusive_is_empty(r),
;

pub assume_specification<Idx>[ RangeInclusive::<Idx>::new ](start: Idx, end: Idx) -> (ret:
    core::ops::RangeInclusive<Idx>)
    ensures
        ret@ == (RangeInclusiveView { start, end, exhausted: false }),
;

impl<A: core::iter::Step> super::iter::IteratorSpecImpl for Range<A> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        A::obeys_step_spec() && step_spec_is_well_formed::<A>()
    }

    open spec fn remaining(&self) -> Seq<Self::Item> {
        let steps = self.start.spec_steps_between_int(self.end);
        let len = if steps > 0 {
            steps
        } else {
            0
        };
        Seq::new(len as nat, |i: int| self.start.spec_forward_checked_int(i).unwrap())
    }

    uninterp spec fn will_return_none(&self) -> bool;

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

/// Number of elements left in an inclusive range: zero once it is exhausted or if `start > end`.
pub open spec fn spec_range_inclusive_len<A: core::iter::Step>(r: &RangeInclusive<A>) -> nat {
    let steps = r@.start.spec_steps_between_int(r@.end);
    if steps >= 0 && !r@.exhausted {
        (steps + 1) as nat
    } else {
        0
    }
}

impl<A: core::iter::Step> super::iter::IteratorSpecImpl for RangeInclusive<A> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        A::obeys_step_spec() && step_spec_is_well_formed::<A>()
    }

    open spec fn remaining(&self) -> Seq<Self::Item> {
        Seq::new(
            spec_range_inclusive_len(self),
            |i: int| self@.start.spec_forward_checked_int(i).unwrap(),
        )
    }

    uninterp spec fn will_return_none(&self) -> bool;

    open spec fn decrease(&self) -> Option<nat> {
        Some(spec_range_inclusive_len(self))
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index <= spec_range_inclusive_len(self) {
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
        A::obeys_step_spec() && step_spec_is_well_formed::<A>() ==> (*final(range), r)
            == spec_range_next(*old(range)),
;

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

pub open spec fn bound_as_ref<T>(b: &Bound<T>) -> Bound<&T> {
    match b {
        Bound::Included(start) => Bound::Included(start),
        Bound::Excluded(start) => Bound::Excluded(start),
        Bound::Unbounded => Bound::Unbounded,
    }
}

// Per-type specifications for `RangeBounds::start_bound`/`end_bound`, so these
// methods can also be called directly in exec code (not just via the spec-mode
// models above). Each spec agrees with the corresponding `RangeBoundsSpecImpl`.
pub assume_specification<'s, T>[ <Range<T> as RangeBounds<T>>::start_bound ](
    range: &'s Range<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Included(&range.start),
;

pub assume_specification<'s, T>[ <Range<T> as RangeBounds<T>>::end_bound ](
    range: &'s Range<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Excluded(&range.end),
;

pub assume_specification<'s, T: ?Sized>[ <RangeFull as RangeBounds<T>>::start_bound ](
    range: &'s RangeFull,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Unbounded,
;

pub assume_specification<'s, T: ?Sized>[ <RangeFull as RangeBounds<T>>::end_bound ](
    range: &'s RangeFull,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Unbounded,
;

pub assume_specification<'s, T>[ <RangeFrom<T> as RangeBounds<T>>::start_bound ](
    range: &'s RangeFrom<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Included(&range.start),
;

pub assume_specification<'s, T>[ <RangeFrom<T> as RangeBounds<T>>::end_bound ](
    range: &'s RangeFrom<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Unbounded,
;

pub assume_specification<'s, T>[ <RangeTo<T> as RangeBounds<T>>::start_bound ](
    range: &'s RangeTo<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Unbounded,
;

pub assume_specification<'s, T>[ <RangeTo<T> as RangeBounds<T>>::end_bound ](
    range: &'s RangeTo<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Excluded(&range.end),
;

pub assume_specification<'s, T>[ <RangeInclusive<T> as RangeBounds<T>>::start_bound ](
    range: &'s RangeInclusive<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Included(&range@.start),
;

// Shared with `RangeBoundsSpecImpl::spec_end_bound` below, so the two can't
// drift apart: `end_bound()` returns `Included` while the range is not
// exhausted and `Excluded` after it is exhausted.
pub open spec fn spec_range_inclusive_end_bound<T>(r: &RangeInclusive<T>) -> Bound<&T> {
    if r@.exhausted {
        Bound::Excluded(&r@.end)
    } else {
        Bound::Included(&r@.end)
    }
}

pub assume_specification<'s, T>[ <RangeInclusive<T> as RangeBounds<T>>::end_bound ](
    range: &'s RangeInclusive<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == spec_range_inclusive_end_bound(range),
;

pub assume_specification<'s, T>[ <RangeToInclusive<T> as RangeBounds<T>>::start_bound ](
    range: &'s RangeToInclusive<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Unbounded,
;

pub assume_specification<'s, T>[ <RangeToInclusive<T> as RangeBounds<T>>::end_bound ](
    range: &'s RangeToInclusive<T>,
) -> (result: Bound<&'s T>)
    ensures
        result == Bound::Included(&range.end),
;

pub assume_specification<'s, T>[ <(Bound<T>, Bound<T>) as RangeBounds<T>>::start_bound ](
    range: &'s (Bound<T>, Bound<T>),
) -> (result: Bound<&'s T>)
    ensures
        result == bound_as_ref(&range.0),
;

pub assume_specification<'s, T>[ <(Bound<T>, Bound<T>) as RangeBounds<T>>::end_bound ](
    range: &'s (Bound<T>, Bound<T>),
) -> (result: Bound<&'s T>)
    ensures
        result == bound_as_ref(&range.1),
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

    spec fn spec_start_bound(&self) -> Bound<&T>;

    spec fn spec_end_bound(&self) -> Bound<&T>;

    fn start_bound(&self) -> Bound<&T>;

    fn end_bound(&self) -> Bound<&T>;
}

impl<T> RangeBoundsSpecImpl<T> for Range<T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Included(&self.start)
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Excluded(&self.end)
    }
}

impl<T: ?Sized> RangeBoundsSpecImpl<T> for RangeFull {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Unbounded
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeFrom<T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Included(&self.start)
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Unbounded
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeTo<T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Excluded(&self.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeInclusive<T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Included(&self@.start)
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        spec_range_inclusive_end_bound(self)
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeToInclusive<T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Included(&self.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for (Bound<T>, Bound<T>) {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        bound_as_ref(&self.0)
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        bound_as_ref(&self.1)
    }
}

impl<'a, T: ?Sized + 'a> RangeBoundsSpecImpl<T> for (Bound<&'a T>, Bound<&'a T>) {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        self.0
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        self.1
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeFrom<&T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Included(self.start)
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Unbounded
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeTo<&T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Excluded(self.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for Range<&T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Included(self.start)
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Excluded(self.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeInclusive<&T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Included(self@.start)
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        // In contrast to RangeBounds<T> for RangeInclusive<T>,
        // Rust's RangeBounds<T> for RangeInclusive<&T> always returns Included,
        // regardless of exhausted.
        Bound::Included(self@.end)
    }
}

impl<T> RangeBoundsSpecImpl<T> for RangeToInclusive<&T> {
    open spec fn spec_start_bound(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    open spec fn spec_end_bound(&self) -> Bound<&T> {
        Bound::Included(self.end)
    }
}

/// Normalized (inclusive) start index of `range`, matching std's
/// `core::slice::range`: an inclusive bound `i` stays `i`, an exclusive bound
/// `i` becomes `i + 1`, and an unbounded start is `0`.
pub open spec fn slice_range_start<R: RangeBoundsSpec<usize>>(range: &R) -> int {
    match range.spec_start_bound() {
        Bound::Included(i) => *i as int,
        Bound::Excluded(i) => (*i as int) + 1,
        Bound::Unbounded => 0,
    }
}

/// Normalized (exclusive) end index of a range over a sequence of length `len`,
/// matching std's `core::slice::range`: an inclusive bound `i` becomes `i + 1`,
/// an exclusive bound `i` stays `i`, and an unbounded end is `len`.
pub open spec fn slice_range_end<R: RangeBoundsSpec<usize>>(range: &R, len: nat) -> int {
    match range.spec_end_bound() {
        Bound::Included(i) => (*i as int) + 1,
        Bound::Excluded(i) => *i as int,
        Bound::Unbounded => len as int,
    }
}

/// The bounds with which std's `SliceIndex` impls for `RangeInclusive<usize>` index:
/// `start..end + 1`, or the empty range `end + 1..end + 1` if the range is exhausted
/// (unlike `end_bound()`, which reports `Excluded(end)` for an exhausted range).
pub open spec fn spec_range_inclusive_slice_bounds(r: &RangeInclusive<usize>) -> (
    Bound<usize>,
    Bound<usize>,
) {
    (
        if r@.exhausted {
            Bound::Excluded(r@.end)
        } else {
            Bound::Included(r@.start)
        },
        Bound::Included(r@.end),
    )
}

/// Whether a range normalizes to `start <= end <= len`, i.e. the condition
/// under which std's `core::slice::range` does not panic.
pub open spec fn slice_range_valid<R: RangeBoundsSpec<usize>>(range: &R, len: nat) -> bool {
    slice_range_start(range) <= slice_range_end(range, len) <= len
}

} // verus!
macro_rules! step_specs {
    ($t: ty, $axiom: ident, $laws: ident) => {
        verus! {
        impl StepSpecImpl for $t {
            open spec fn obeys_step_spec() -> bool {
                true
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
            open spec fn spec_forward_overflowing(self, count: usize) -> (Self, bool) {
                (
                    step_spec_wrapping_value(self as int, count as int, $t::MIN as int, $t::MAX as int) as $t,
                    StepSpec::spec_forward_checked(self, count).is_none(),
                )
            }
            open spec fn spec_backward_overflowing(self, count: usize) -> (Self, bool) {
                (
                    step_spec_wrapping_value(self as int, -(count as int), $t::MIN as int, $t::MAX as int) as $t,
                    StepSpec::spec_backward_checked(self, count).is_none(),
                )
            }
        }
        pub broadcast proof fn $laws()
            ensures
                #[trigger] step_spec_is_well_formed::<$t>(),
        {
            assert(step_spec_order_is_well_formed::<$t>()) by {
                reveal(step_spec_order_is_well_formed);
            }
            assert(step_spec_checked_is_well_formed::<$t>()) by {
                reveal(step_spec_checked_is_well_formed);
            }
            assert(step_spec_composition_is_well_formed::<$t>()) by {
                reveal(step_spec_composition_is_well_formed);
            }
            assert(step_spec_overflowing_is_well_formed::<$t>()) by {
                broadcast use
                    lemma_step_spec_wrapping_value,
                    lemma_step_spec_wrapping_composition;
                reveal(step_spec_overflowing_is_well_formed);
            }
            assert(step_spec_forward_is_well_formed::<$t>()) by {
                reveal(step_spec_forward_is_well_formed);
            }
            assert(step_spec_backward_is_well_formed::<$t>()) by {
                reveal(step_spec_backward_is_well_formed);
            }
            reveal(step_spec_is_well_formed);
        }

        pub broadcast proof fn $axiom(range: Range<$t>)
            ensures
                range.start.is_lt(&range.end) ==>
                    // TODO (not important): use new "matches ==>" syntax here
                    (if let Some(n) = StepSpec::spec_forward_checked(range.start, 1) {
                        spec_range_next(range) == (Range { start: n, ..range }, Some(range.start))
                    } else {
                        true
                    }),
                !range.start.is_lt(&range.end) ==>
                    #[trigger] spec_range_next(range) == (range, None::<$t>),
        {
        }
        } // verus!
    };
}

step_specs!(u8, axiom_spec_range_next_u8, lemma_step_spec_u8);
step_specs!(u16, axiom_spec_range_next_u16, lemma_step_spec_u16);
step_specs!(u32, axiom_spec_range_next_u32, lemma_step_spec_u32);
step_specs!(u64, axiom_spec_range_next_u64, lemma_step_spec_u64);
step_specs!(u128, axiom_spec_range_next_u128, lemma_step_spec_u128);
step_specs!(usize, axiom_spec_range_next_usize, lemma_step_spec_usize);
step_specs!(i8, axiom_spec_range_next_i8, lemma_step_spec_i8);
step_specs!(i16, axiom_spec_range_next_i16, lemma_step_spec_i16);
step_specs!(i32, axiom_spec_range_next_i32, lemma_step_spec_i32);
step_specs!(i64, axiom_spec_range_next_i64, lemma_step_spec_i64);
step_specs!(i128, axiom_spec_range_next_i128, lemma_step_spec_i128);
step_specs!(isize, axiom_spec_range_next_isize, lemma_step_spec_isize);

verus! {

pub broadcast group group_range_axioms {
    lemma_step_spec_u8,
    lemma_step_spec_u16,
    lemma_step_spec_u32,
    lemma_step_spec_u64,
    lemma_step_spec_u128,
    lemma_step_spec_usize,
    lemma_step_spec_i8,
    lemma_step_spec_i16,
    lemma_step_spec_i32,
    lemma_step_spec_i64,
    lemma_step_spec_i128,
    lemma_step_spec_isize,
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
}

} // verus!
