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
//! assert(r2.loc() == r1.loc());
//! assert(r2@ == r1@);
//! ```
//!
//! Any two agreement resources with the same `loc()` are guaranteed to
//! have equal values. You can establish this by calling
//! `lemma_agreement`, as in the following example:
//!
//! ```
//! assert(r2.loc() == r1.loc());
//! proof { r1.lemma_agreement(&mut r2); }
//! assert(r2@ == r1@);
//! ```
#![allow(unused_imports)]
use std::result::*;
use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::prelude::*;
use vstd::resource;
use vstd::resource::agree::lemma_agree;
use vstd::resource::agree::AgreementRA;
use vstd::resource::algebra::Resource;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::Loc;

verus! {

pub struct AgreementResource<T> {
    r: Resource<AgreementRA<T>>,
}

impl<T> AgreementResource<T> {
    pub closed spec fn loc(self) -> Loc {
        self.r.loc()
    }

    pub closed spec fn view(self) -> T
    {
        self.r.value()@
    }

    pub proof fn alloc(c: T) -> (tracked result: AgreementResource<T>)
        ensures
            result@ == c,
    {
        let carrier = AgreementRA::Agree(c);
        let tracked r = Resource::alloc(carrier);
        AgreementResource::<T> { r }
    }

    pub proof fn duplicate(tracked self: &AgreementResource<T>) -> (tracked result: AgreementResource<T>)
        ensures
            result.loc() == self.loc(),
            self@ == result@,
    {
        let tracked r = self.r.as_ref().duplicate_previous(self.r.value());
        AgreementResource::<T> { r }
    }

    pub proof fn lemma_agreement(
        tracked self: &AgreementResource<T>,
        tracked other: &AgreementResource<T>,
    )
        requires
            self.loc() == other.loc(),
        ensures
            self@ == other@,
    {
        lemma_agree(&self.r, &other.r);
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
