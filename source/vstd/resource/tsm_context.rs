//! Duplicable metadata for a checked protocol's instance descriptor.
//!
//! This resource records an immutable value. It proves no machine invariant,
//! compatible state, storage ownership, or permission. Generated private
//! instance constructors must obtain their metadata from checked initialization;
//! field tokens retain the actual protocol resources and constant observations.
use super::super::prelude::*;
use super::Loc;
use super::agree::AgreementRA;
use super::algebra::ResourceAlgebra;
use super::pcm::Resource;

verus! {

#[verifier::accept_recursive_types(T)]
pub tracked struct Descriptor<T> {
    resource: Resource<Option<AgreementRA<T>>>,
}

impl<T> Descriptor<T> {
    #[verifier::type_invariant]
    spec fn invariant(self) -> bool {
        self.resource.value() is Some && self.resource.value()->Some_0 is Agree
    }

    pub closed spec fn value(self) -> T {
        self.resource.value()->Some_0->Agree_0
    }

    /// Identity of the metadata resource, distinct from any stored protocol location.
    pub closed spec fn id(self) -> Loc {
        self.resource.loc()
    }

    /// Allocate immutable metadata, not a capability for a machine or its storage.
    pub proof fn alloc(value: T) -> (tracked out: Self)
        ensures
            out.value() == value,
    {
        let tracked resource = Resource::alloc(Some(AgreementRA::Agree(value)));
        Self { resource }
    }

    pub proof fn clone(tracked &self) -> (tracked out: Self)
        ensures
            out.value() == self.value(),
            out.id() == self.id(),
    {
        use_type_invariant(self);
        let tracked resource = super::duplicate(&self.resource);
        Self { resource }
    }

    pub proof fn agrees(tracked &self, tracked other: &Self)
        requires
            self.id() == other.id(),
        ensures
            self.value() == other.value(),
    {
        use_type_invariant(self);
        use_type_invariant(other);
        let tracked upper = self.resource.join_shared(&other.resource);
        upper.validate();
        let left = choose|frame: Option<AgreementRA<T>>|
            Option::<AgreementRA<T>>::op(self.resource.value(), frame) == upper.value();
        let right = choose|frame: Option<AgreementRA<T>>|
            Option::<AgreementRA<T>>::op(other.resource.value(), frame) == upper.value();
        assert(upper.value() == self.resource.value());
        assert(upper.value() == other.resource.value());
    }
}

} // verus!
