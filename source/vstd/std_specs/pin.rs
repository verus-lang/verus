use super::super::mut_ref::MutRef;
use super::super::prelude::*;
use core::pin::Pin;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(P)]
pub struct ExPin<P>(Pin<P>);

pub trait PinAdditionalSpecFns<'a, T: ?Sized> {
    /// The mutable reference behind this `Pin`, with its current and prophesied values.
    spec fn mut_ref(&self) -> MutRef<'a, T>;
}

impl<'a, T: ?Sized> PinAdditionalSpecFns<'a, T> for Pin<&'a mut T> {
    uninterp spec fn mut_ref(&self) -> MutRef<'a, T>;
}

pub assume_specification<'a, T: Unpin + ?Sized>[ Pin::<&'a mut T>::get_mut ](
    pin: Pin<&'a mut T>,
) -> (r: &'a mut T)
    ensures
        MutRef::unpack(r) == pin.mut_ref(),
        &*r == pin.mut_ref().current,
        &*final(r) == pin.mut_ref().future.value(),
;

pub broadcast axiom fn axiom_pin_has_resolved<'a, T: ?Sized>(pin: Pin<&'a mut T>)
    ensures
        has_resolved::<Pin<&'a mut T>>(pin) ==> (#[trigger] pin.mut_ref()).future.value()
            == pin.mut_ref().current,
;

pub broadcast group group_pin_axioms {
    axiom_pin_has_resolved,
}

} // verus!
