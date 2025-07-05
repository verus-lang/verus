//! This file implements agreement on a constant value using a custom
//! resource algebra.
//!
//! An agreement resource constitutes knowledge of a constant value.
//! To create an instance of a constant value of type `T`, use
//! `AgreementResource::<T>::alloc()` as in the following example:
//!
//! ```
//! let tracked r1 = AgreementResource::<int>::alloc(72);
//! assert(r1@ == 72);
//! ```
//!
//! Knowledge of a constant value can be duplicated with `duplicate`,
//! which creates another agreement resource with the same constant
//! value and the same ID. Here's an example:
//!
//! ```
//! let tracked r2 = r1.duplicate();
//! assert(r2.id() == r1.id());
//! assert(r2@ == r1@);
//! ```
//!
//! Any two agreement resources with the same `id()` are guaranteed to
//! have equal values. You can establish this by calling
//! `lemma_agreement`, as in the following example:
//!
//! ```
//! assert(r2.id() == r1.id());
//! proof { r1.lemma_agreement(&mut r2); }
//! assert(r2@ == r1@);
//! ```
#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use std::result::*;
use vstd::pcm::*;
use vstd::pcm_lib::*;
use vstd::prelude::*;

verus! {

pub enum AgreementResourceValue<T> {
    Empty,
    Chosen { c: T },
    Invalid,
}

impl<T> AgreementResourceValue<T> {
    pub open spec fn new(c: T) -> Self {
        AgreementResourceValue::<T>::Chosen { c }
    }
}

impl<T> PCM for AgreementResourceValue<T> {
    open spec fn valid(self) -> bool {
        !(self is Invalid)
    }

    open spec fn op(self, other: Self) -> Self {
        match (self, other) {
            (AgreementResourceValue::<T>::Empty, _) => other,
            (_, AgreementResourceValue::<T>::Empty) => self,
            (AgreementResourceValue::<T>::Invalid, _) => AgreementResourceValue::<T>::Invalid {  },
            (_, AgreementResourceValue::<T>::Invalid) => AgreementResourceValue::<T>::Invalid {  },
            (
                AgreementResourceValue::<T>::Chosen { c: c1 },
                AgreementResourceValue::<T>::Chosen { c: c2 },
            ) => if c1 == c2 {
                self
            } else {
                AgreementResourceValue::<T>::Invalid {  }
            },
        }
    }

    open spec fn unit() -> Self {
        AgreementResourceValue::<T>::Empty {  }
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

pub struct AgreementResource<T> {
    r: Resource<AgreementResourceValue<T>>,
}

impl<T> AgreementResource<T> {
    pub closed spec fn inv(self) -> bool {
        self.r.value() is Chosen
    }

    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> T
        recommends
            self.inv(),
    {
        self.r.value()->c
    }

    pub proof fn alloc(c: T) -> (tracked result: AgreementResource<T>)
        ensures
            result.inv(),
            result@ == c,
    {
        let r_value = AgreementResourceValue::<T>::new(c);
        let tracked r = Resource::<AgreementResourceValue::<T>>::alloc(r_value);
        AgreementResource::<T> { r }
    }

    pub proof fn duplicate(tracked self: &mut AgreementResource<T>) -> (tracked result:
        AgreementResource<T>)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            result.inv(),
            self.id() == result.id() == old(self).id(),
            self@ == result@,
            self@ == old(self)@,
    {
        let tracked r = duplicate(&self.r);
        AgreementResource::<T> { r }
    }

    pub proof fn lemma_agreement(
        tracked self: &mut AgreementResource<T>,
        tracked other: &AgreementResource<T>,
    )
        requires
            old(self).inv(),
            other.inv(),
            old(self).id() == other.id(),
        ensures
            self.id() == old(self).id(),
            self@ == old(self)@,
            self@ == other@,
    {
        self.r.validate_2(&other.r);
    }
}

pub fn main() {
    let tracked r1 = AgreementResource::<int>::alloc(72);
    assert(r1@ == 72);
    let tracked r2 = r1.duplicate();
    assert(r2@ == r1@);
    proof {
        r1.lemma_agreement(&mut r2);
    }
}

} // verus!
