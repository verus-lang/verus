//! This file implements monotonic counters using a custom resource
//! algebra.
//!
//! To use it, use MonotonicCounterResource::alloc(), which will
//! create a fresh monotonic counter and return a resource granting
//! full access to it. You can increment it the counter by calling
//! `increment` on a resource. For example:
//!
//! ```
//! let tracked full = MonotonicCounterResource::alloc();
//! proof { full.increment(); }
//! assert(full@.n() == 1);
//! ```
//!
//! To split a full right to advance into two half rights to advance,
//! use `split`. This is useful, for instance, to stash half inside an
//! invariant and pass the other half to the thread having the right
//! to advance. Both halves will have the same `id()` value,
//! indicating they correspond to the same monotonic counter. For
//! example:
//!
//! ```
//! let tracked full = MonotonicCounterResource::alloc();
//! let tracked (mut half1, mut half2) = full.split();
//! assert(half1.id() == half2.id());
//! assert(half1@.n() == 0);
//! assert(half2@.n() == 0);
//! ```
//!
//! You can use two half authorities together to increment the
//! associated counter, as in this example:
//!
//! ```
//! let ghost v1 == half1@.n();
//! proof { half1.increment_using_two_halves(&mut half2); }
//! assert(half1.id() == half2.id());
//! assert(half1@ == half2@);
//! assert(half1@.n() == half2@.n() == v1 + 1);
//! ```
//!
//! From any `MonotonicCounterResource`, one can use
//! `extract_lower_bound()` to extract a `MonotonicCounterResource`
//! that represents knowledge of a lower bound on the current value of
//! the monotonic counter. You can also duplicate a
//! `MonotonicCounterResource` using this function. Here are examples:
//!
//! ```
//! let tracked mut lower_bound = half1.extract_lower_bound();
//! assert(lower_bound@.n() == 1);
//! let tracked lower_bound_duplicate = lower_bound.extract_lower_bound();
//! assert(lower_bound_duplicate@.n() == 1);
//! ```
#![allow(unused_imports)]
use std::result::*;
use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::prelude::*;
use vstd::resource::copy_duplicable_part;
use vstd::resource::pcm::PCM;
use vstd::resource::update_and_redistribute;
use vstd::resource::update_mut;
use vstd::resource::Loc;
use vstd::resource::Resource;

verus! {

// A monotonic counter permission represents a resource with one of
// the following three values:
//
// `LowerBound{ lower_bound }` -- knowledge that the monotonic counter
// is at least `lower_bound`
//
// `FullRightToAdvance{ value }` -- knowledge that the monotonic counter is
// exactly `value` and the authority to advance it past that value
//
// `HalfRightToAdvance{ value }` -- knowledge that the monotonic
// counter is exactly `value` and half the authority to advance it
// past that value. Can be combined with another half authority to
// make a full authority.
pub enum MonotonicCounterResourceValue {
    LowerBound { lower_bound: nat },
    HalfRightToAdvance { value: nat },
    FullRightToAdvance { value: nat },
    Invalid,
}

// To use `MonotonicCounterResourceValue` as a resource, we have to implement
// `PCM`, showing how to use it in a resource algebra.
impl PCM for MonotonicCounterResourceValue {
    open spec fn pcm_valid(self) -> bool {
        !(self is Invalid)
    }

    open spec fn pcm_op(a: Self, b: Self) -> Self {
        match (a, b) {
            // Two lower bounds can be combined into a lower bound
            // that's the maximum of the two lower bounds.
            (
                MonotonicCounterResourceValue::LowerBound { lower_bound: lower_bound1 },
                MonotonicCounterResourceValue::LowerBound { lower_bound: lower_bound2 },
            ) => {
                let max_lower_bound = if lower_bound1 > lower_bound2 {
                    lower_bound1
                } else {
                    lower_bound2
                };
                MonotonicCounterResourceValue::LowerBound { lower_bound: max_lower_bound }
            },
            // A lower bound can be combined with a right to
            // advance as long as the lower bound doesn't exceed
            // the value in the right to advance.
            (
                MonotonicCounterResourceValue::LowerBound { lower_bound },
                MonotonicCounterResourceValue::FullRightToAdvance { value },
            ) => if lower_bound <= value {
                MonotonicCounterResourceValue::FullRightToAdvance { value }
            } else {
                MonotonicCounterResourceValue::Invalid {  }
            },
            (
                MonotonicCounterResourceValue::FullRightToAdvance { value },
                MonotonicCounterResourceValue::LowerBound { lower_bound },
            ) => if lower_bound <= value {
                MonotonicCounterResourceValue::FullRightToAdvance { value }
            } else {
                MonotonicCounterResourceValue::Invalid {  }
            },
            // A lower bound can be combined with a half right to
            // advance as long as the lower bound doesn't exceed
            // the value in the half right to advance.
            (
                MonotonicCounterResourceValue::LowerBound { lower_bound },
                MonotonicCounterResourceValue::HalfRightToAdvance { value },
            ) => if lower_bound <= value {
                MonotonicCounterResourceValue::HalfRightToAdvance { value }
            } else {
                MonotonicCounterResourceValue::Invalid {  }
            },
            (
                MonotonicCounterResourceValue::HalfRightToAdvance { value },
                MonotonicCounterResourceValue::LowerBound { lower_bound },
            ) => if lower_bound <= value {
                MonotonicCounterResourceValue::HalfRightToAdvance { value }
            } else {
                MonotonicCounterResourceValue::Invalid {  }
            },
            // Two half rights to advance can be combined to make
            // a whole right to advance, as long as the two values
            // agree with each other.
            (
                MonotonicCounterResourceValue::HalfRightToAdvance { value: value1 },
                MonotonicCounterResourceValue::HalfRightToAdvance { value: value2 },
            ) => if value1 == value2 {
                MonotonicCounterResourceValue::FullRightToAdvance { value: value1 }
            } else {
                MonotonicCounterResourceValue::Invalid {  }
            },
            // Any other combination is invalid
            (_, _) => MonotonicCounterResourceValue::Invalid {  },
        }
    }

    open spec fn unit() -> Self {
        MonotonicCounterResourceValue::LowerBound { lower_bound: 0 }
    }

    proof fn pcm_valid_op(a: Self, b: Self) {
    }

    proof fn pcm_commutative(a: Self, b: Self) {
    }

    proof fn pcm_associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(self) {
    }

    proof fn unit_valid() {
    }
}

impl MonotonicCounterResourceValue {
    pub open spec fn n(self) -> nat {
        match self {
            MonotonicCounterResourceValue::LowerBound { lower_bound } => lower_bound,
            MonotonicCounterResourceValue::HalfRightToAdvance { value } => value,
            MonotonicCounterResourceValue::FullRightToAdvance { value } => value,
            MonotonicCounterResourceValue::Invalid => 0,
        }
    }
}

pub struct MonotonicCounterResource {
    r: Resource<MonotonicCounterResourceValue>,
}

impl MonotonicCounterResource {
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> MonotonicCounterResourceValue {
        self.r.value()
    }

    // This function creates a monotonic counter and returns a
    // resource granting full authority to advance it and giving
    // knowledge that the current value is 0.
    pub proof fn alloc() -> (tracked result: Self)
        ensures
            result@ == (MonotonicCounterResourceValue::FullRightToAdvance { value: 0 }),
    {
        let v = MonotonicCounterResourceValue::FullRightToAdvance { value: 0 };
        let tracked mut r = Resource::<MonotonicCounterResourceValue>::alloc(v);
        Self { r }
    }

    // Join two resources
    pub proof fn join(tracked self: Self, tracked other: Self) -> (tracked r: Self)
        requires
            self.id() == other.id(),
            self@.n() == other@.n(),
        ensures
            r.id() == self.id(),
            r@.n() == MonotonicCounterResourceValue::pcm_op(self@, other@).n(),
    {
        let tracked mut r = self.r.join(other.r);
        Self { r }
    }

    // This function splits a resource granting full authority to
    // advance a monotonic counter into two resources each granting
    // half authority to advance it. They both have the same `id()`,
    // meaning they correspond to the same monotonic counter.
    pub proof fn split(tracked self) -> (tracked return_value: (Self, Self))
        requires
            self@ is FullRightToAdvance,
        ensures
            ({
                let (r1, r2) = return_value;
                let value = self@->FullRightToAdvance_value;
                &&& r1.id() == self.id()
                &&& r2.id() == self.id()
                &&& r1@ == (MonotonicCounterResourceValue::HalfRightToAdvance { value })
                &&& r2@ == r1@
            }),
    {
        let value = self@->FullRightToAdvance_value;
        let v_half = MonotonicCounterResourceValue::HalfRightToAdvance { value };
        let tracked (r1, r2) = self.r.split(v_half, v_half);
        (Self { r: r1 }, Self { r: r2 })
    }

    // This function uses a resource granting full authority to
    // advance a monotonic counter to increment the counter.
    pub proof fn increment(tracked &mut self)
        requires
            old(self)@ is FullRightToAdvance,
        ensures
            self.id() == old(self).id(),
            self@ == (MonotonicCounterResourceValue::FullRightToAdvance {
                value: old(self)@->FullRightToAdvance_value + 1,
            }),
    {
        let v = self@->FullRightToAdvance_value;
        let r = MonotonicCounterResourceValue::FullRightToAdvance { value: v + 1 };
        update_mut(&mut self.r, r);
    }

    // This function uses two tracked resources, each granting half
    // authority to advance a monotonic counter, to increment the
    // counter. The two permissions must have the same `id()` values.
    //
    // It's not a requirement that the two halves match in value; this
    // function can figure out that they match just from the fact that
    // they co-exist.
    pub proof fn increment_using_two_halves(tracked &mut self, tracked other: &mut Self)
        requires
            old(self).id() == old(other).id(),
            old(self)@ is HalfRightToAdvance,
            old(other)@ is HalfRightToAdvance,
        ensures
            old(self)@ == old(other)@,
            self.id() == old(self).id(),
            other.id() == old(self).id(),
            other@ == self@,
            self@ == (MonotonicCounterResourceValue::HalfRightToAdvance {
                value: old(self)@->HalfRightToAdvance_value + 1,
            }),
    {
        self.r.validate_2(&other.r);
        let v = self@->HalfRightToAdvance_value;
        let r = MonotonicCounterResourceValue::HalfRightToAdvance { value: v + 1 };
        update_and_redistribute(&mut self.r, &mut other.r, r, r);
    }

    pub proof fn extract_lower_bound(tracked &self) -> (tracked out: Self)
        ensures
            out@ is LowerBound,
            out.id() == self.id(),
            out@ == (MonotonicCounterResourceValue::LowerBound { lower_bound: self@.n() }),
    {
        self.r.validate();
        let v = MonotonicCounterResourceValue::LowerBound { lower_bound: self@.n() };
        let tracked r = copy_duplicable_part(&self.r, v);
        Self { r }
    }

    pub proof fn lemma_lower_bound(tracked &mut self, tracked other: &Self)
        requires
            old(self).id() == other.id(),
        ensures
            self@ == old(self)@,
            self@ is LowerBound && other@ is FullRightToAdvance ==> self@.n() <= other@.n(),
            other@ is LowerBound && self@ is FullRightToAdvance ==> other@.n() <= self@.n(),
            self@ is LowerBound && other@ is HalfRightToAdvance ==> self@.n() <= other@.n(),
            other@ is LowerBound && self@ is HalfRightToAdvance ==> other@.n() <= self@.n(),
    {
        self.r.validate_2(&other.r)
    }
}

// This example illustrates some uses of the monotonic counter.
fn main() {
    let tracked full = MonotonicCounterResource::alloc();
    proof {
        full.increment();
    }
    assert(full@.n() == 1);
    let tracked full = MonotonicCounterResource::alloc();
    let tracked zero_lower_bound = full.extract_lower_bound();
    let tracked (mut half1, mut half2) = full.split();
    assert(half1.id() == half2.id());
    assert(half1@.n() == 0);
    assert(half2@.n() == 0);
    let ghost id = half1.id();
    let ghost v1 = half1@.n();
    let ghost v2 = half2@.n();
    assert(v1 == v2);
    proof {
        half1.increment_using_two_halves(&mut half2);
    }
    assert(half1.id() == id);
    assert(half2.id() == id);
    assert(half1@.n() == half2@.n() == v1 + 1);
    assert(half1@.n() == 1);
    let tracked mut lower_bound = half1.extract_lower_bound();
    assert(lower_bound@.n() == 1);
    let tracked lower_bound_duplicate = lower_bound.extract_lower_bound();
    assert(lower_bound_duplicate@.n() == 1);

    proof {
        let tracked reconstructed_full = half1.join(half2);
        zero_lower_bound.lemma_lower_bound(&reconstructed_full);
        assert(zero_lower_bound@.n() <= reconstructed_full@.n());
    }
}

} // verus!
