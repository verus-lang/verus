//! This file implements one-shot permissions using a custom resource
//! algebra.
//!
//! A one-shot allows an operation to be performed exactly once. If
//! you have two resources each granting half authority to perform it,
//! you can combine them and perform the one-shot. Performing it
//! grants duplicable knowledge that it has been performed.
//!
//! To create a one-shot, call `OneShotResource::alloc()`. This will
//! return a resource granting full authority to perform the created
//! one-shot. You can then call `perform` to perform that one-shot.
//! Here's an example:
//!
//! ```
//! let tracked full = OneShotResource::alloc();
//! proof { full.perform(); }
//! assert(full@ is Complete);
//! ```
//!
//! Often, you will first split the full authority into two halves,
//! each granting half the authority to perform the created one-shot.
//! This way, you can stash one in an invariant. Both halves will have
//! the same `id()`, meaning they belong to the same one-shot
//! instance. For example:
//!
//! ```
//! let tracked full = OneShotResource::alloc();
//! let tracked (mut half1, mut half2) = full.split();
//! assert(half1.id() == half2.id());
//! assert(half1@ is HalfRightToComplete);
//! assert(half2@ is HalfRightToComplete);
//! ```
//!
//! To perform a one-shot using two halves, use
//! `perform_using_two_halves`. This function takes two resources, the
//! first of which must provide half authority to perform the
//! one-shot. On return, the passed-in resources will have both been
//! changed to `Complete`, i.e., knowledge that the one-shot has
//! complete.
//!
//! ```
//! let ghost id = half1.id();
//! proof { half1.perform_using_two_halves(&mut half2); }
//! assert(half1.id() == half2.id() == id);
//! assert(half1@ is Complete);
//! assert(half2@ is Complete);
//! ```
//!
//! Note that only *one* of the two parameters to `perform` has to be
//! `HalfRightToComplete`. This is useful so you can stash half the
//! authority in an invariant and call `perform` even if the invariant
//! predicate allows the stashed permission to change later.
//!
//! Knowledge that the one-shot has completed is freely duplicable
//! because that's the nature of one-shots. If you want to duplicate
//! it, you can call `duplicate`, but you can only call this if you
//! know the permission passed in is `Complete`. Here's an example of
//! its usage:
//!
//! ```
//! let tracked knowledge = half1.duplicate();
//! assert(knowledge.id() == half1.id());
//! assert(knowledge@ is Complete);
//! ```
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use std::result::*;
use vstd::pcm::*;
use vstd::pcm_lib::*;
use vstd::prelude::*;

verus! {

// A one-shot resource represents one of the following four resources:
//
// `FullRightToComplete` -- the authority to complete the one-shot;
//
// `HalfRightToComplete` -- half of the authority to complete the
// one-shot, which can be combined with another half to make a full
// authority; or
//
// `Complete` -- knowledge that the one-shot has completed.
//
// `Empty` - no permission at all.
pub enum OneShotResourceValue {
    FullRightToComplete,
    HalfRightToComplete,
    Complete,
    Empty,
    Invalid,
}

// To use `OneShotResourceValue` as a resource, we have to implement
// `PCM`, showing how to use it in a resource algebra.
impl PCM for OneShotResourceValue {
    open spec fn valid(self) -> bool {
        !(self is Invalid)
    }

    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (OneShotResourceValue::Empty, _) => other,
            (_, OneShotResourceValue::Empty) => self,
            (
                OneShotResourceValue::HalfRightToComplete,
                OneShotResourceValue::HalfRightToComplete,
            ) => OneShotResourceValue::FullRightToComplete {  },
            (
                OneShotResourceValue::Complete,
                OneShotResourceValue::Complete,
            ) => OneShotResourceValue::Complete {  },
            (_, _) => OneShotResourceValue::Invalid {  },
        }
    }

    open spec fn unit() -> Self {
        OneShotResourceValue::Empty {  }
    }

    proof fn closed_under_incl(a: Self, b: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn op_unit(a: Self) {
    }

    proof fn unit_valid() {
    }
}

pub struct OneShotResource {
    r: Resource<OneShotResourceValue>,
}

impl OneShotResource {
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> OneShotResourceValue {
        self.r.value()
    }

    // This function creates a one-shot and returns a resource
    // granting the full authority to perform the created
    // one-shot.
    pub proof fn alloc() -> (tracked resource: Self)
        ensures
            resource@ is FullRightToComplete,
    {
        let v = OneShotResourceValue::FullRightToComplete {  };
        let tracked mut r = Resource::<OneShotResourceValue>::alloc(v);
        OneShotResource { r }
    }

    // This function splits full authority to perform a one-shot
    // into two half authorities to perform it.
    pub proof fn split(tracked self) -> (tracked return_value: (Self, Self))
        requires
            self@ is FullRightToComplete,
        ensures
            ({
                let (half1, half2) = return_value;
                &&& half1@ is HalfRightToComplete
                &&& half2@ is HalfRightToComplete
                &&& half2.id() == half1.id() == self.id()
            }),
    {
        let half = OneShotResourceValue::HalfRightToComplete {  };
        let tracked (r1, r2) = self.r.split(half, half);
        (OneShotResource { r: r1 }, OneShotResource { r: r2 })
    }

    // This function performs a one-shot given a resource representing
    // full authority to complete the one-shot.
    //
    // Upon return, the passed-in resource will have been transformed
    // into knowledge that the one-shot has been performed.
    pub proof fn perform(tracked &mut self)
        requires
            old(self)@ is FullRightToComplete,
        ensures
            self@ is Complete,
    {
        let v = OneShotResourceValue::Complete {  };
        update_mut(&mut self.r, v);
    }

    // This function performs a one-shot given two resources, the
    // first of which represents an incomplete one-shot (and half the
    // authority needed to perform it). The resources must have the
    // same `id()`, meaning they're talking about the same one-shot.
    //
    // Upon return, the passed-in resources will have both been
    // transformed into knowledge that the one-shot has been
    // performed.
    //
    // The caller of this function only needs to know that `self`
    // provides half authority and that `other` isn't `Empty`. Upon
    // return the caller will learn that *both* the resources had
    // provided half authority at call time. However, those resources
    // were transformed so they don't provide that authority anymore.
    pub proof fn perform_using_two_halves(tracked &mut self, tracked other: &mut Self)
        requires
            old(other).id() == old(self).id(),
            old(self)@ is HalfRightToComplete,
            !(old(other)@ is Empty),
        ensures
            old(other)@ is HalfRightToComplete,
            self@ is Complete,
            other@ is Complete,
            other.id() == self.id() == old(self).id(),
    {
        self.r.validate();
        other.r.validate();
        // A `HalfRightToComplete` doesn't combine validly with a
        // `Complete`, so validating them together proves that
        // `other.r.value()` is `HalfRightToComplete`.
        self.r.validate_2(&other.r);
        assert(other@ is HalfRightToComplete);
        // Knowing they're both `HalfRightToComplete` allows them to
        // be combined and transformed into `Complete` resources.
        let v = OneShotResourceValue::Complete {  };
        update_and_redistribute(&mut self.r, &mut other.r, v, v);
    }

    // This function duplicates a one-shot resource representing
    // knowledge of completion.
    pub proof fn duplicate(tracked &self) -> (tracked other: Self)
        requires
            self@ is Complete,
        ensures
            other.id() == self.id(),
            other@ is Complete,
    {
        let tracked r = duplicate(&self.r);
        Self { r }
    }

    pub proof fn lemma_is_complete_if_other_is(tracked &mut self, tracked other: &Self)
        requires
            other.id() == old(self).id(),
            other@ is Complete,
            !(old(self)@ is Empty),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self@ is Complete,
    {
        self.r.validate_2(&other.r);
    }
}

// This example illustrates some uses of the one-shot functions.
fn main() {
    let tracked full = OneShotResource::alloc();
    proof {
        full.perform();
    }
    assert(full@ is Complete);
    let tracked different_oneshot = OneShotResource::alloc();
    let tracked (mut half1, mut half2) = different_oneshot.split();
    let ghost id = half1.id();
    assert(half1.id() == half2.id());
    assert(half1@ is HalfRightToComplete);
    assert(half2@ is HalfRightToComplete);
    proof {
        half1.perform_using_two_halves(&mut half2);
    }
    assert(half1.id() == half2.id() == id);
    assert(half1@ is Complete);
    assert(half2@ is Complete);
    let tracked knowledge = half1.duplicate();
    assert(knowledge.id() == half1.id() == id);
    assert(knowledge@ is Complete);
}

} // verus!
