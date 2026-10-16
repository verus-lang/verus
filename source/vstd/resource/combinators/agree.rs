use super::super::super::prelude::*;
use super::super::algebra::Resource;
use super::super::algebra::ResourceAlgebra;

verus! {

/// The Agreement resource algebra
///
/// This resource algebra allows one to express that multiple parties can _agree_ on a chosen value
/// This is mainly useful to show that if two resources are `Agree` then they must point to the
/// same value (see [`lemma_agree`]):
/// ```
pub enum AgreementRA<T> {
    Agree(T),
    Invalid,
}

impl<T> ResourceAlgebra for AgreementRA<T> {
    open spec fn valid(self) -> bool {
        match self {
            AgreementRA::Invalid => false,
            _ => true,
        }
    }

    open spec fn op(a: Self, b: Self) -> Self {
        // Avoid matching on `(a, b)`: each unfolding would build a tuple term.
        if a is Agree && b is Agree && a->Agree_0 == b->Agree_0 {
            a
        } else {
            AgreementRA::Invalid
        }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
    }

    proof fn commutative(a: Self, b: Self) {
    }

    proof fn valid_op(a: Self, b: Self) {
    }
}

impl<T> AgreementRA<T> {
    pub open spec fn view(self) -> T {
        self->Agree_0
    }
}

pub proof fn lemma_agree<T>(
    tracked a: &Resource<AgreementRA<T>>,
    tracked b: &Resource<AgreementRA<T>>,
)
    requires
        a.loc() == b.loc(),
    ensures
        a.value()@ == b.value()@,
{
    a.join_shared(b).validate();
}

} // verus!
