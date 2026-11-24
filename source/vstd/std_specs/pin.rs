use super::super::mut_ref::MutRef;
use super::super::prelude::*;
use core::pin::Pin;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(P)]
pub struct ExPin<P>(Pin<P>);

pub trait PinAdditionalSpecFns<'a, T: ?Sized> {
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

// `Pin<P>` for `P::Target: Unpin` is a transparent wrapper around the pointer: `Pin::new`,
// `into_inner` and `get_ref` are identities on it. The `!Unpin` operations are not
// specified: their correctness depends on the aliasing discipline, which this model does not
// capture.
pub trait PinAdditionalFns<P> {
    /// The wrapped pointer.
    spec fn pointer(&self) -> P;
}

impl<P> PinAdditionalFns<P> for Pin<P> {
    uninterp spec fn pointer(&self) -> P;
}

impl<P> View for Pin<P> {
    type V = P;

    open spec fn view(&self) -> Self::V {
        self.pointer()
    }
}

pub assume_specification<P: core::ops::Deref>[ Pin::<P>::new ](pointer: P) -> (res: Pin<P>) where
    P::Target: Unpin,

    ensures
        res.pointer() == pointer,
;

// `Pin::new_unchecked` has the same spec as `Pin::new`, but without the `Unpin` bound.
// Its safety contract (that the pointee is never moved again) is not captured by this spec;
// instead, Verus enforces it by restricting how calls to `Pin::new_unchecked` may appear:
// the argument must be `&mut x` for a local `x` of the enclosing function, `x` cannot be
// moved from anywhere in the function, and `x` cannot be captured by a closure.
pub assume_specification<P: core::ops::Deref>[ Pin::<P>::new_unchecked ](pointer: P) -> (res:
    Pin<P>)
    ensures
        res.pointer() == pointer,
;

pub assume_specification<P: core::ops::Deref>[ Pin::<P>::into_inner ](pin: Pin<P>) -> (res:
    P) where P::Target: Unpin
    ensures
        res == pin.pointer(),
;

pub assume_specification<'a, T: ?Sized>[ Pin::<&'a T>::get_ref ](pin: Pin<&'a T>) -> (res: &'a T)
    ensures
        res == pin.pointer(),
;

/// For `Pin<&mut T>`, the reference `mut_ref` describes is the wrapped pointer.
pub broadcast axiom fn axiom_pin_mut_ref_pointer<'a, T: ?Sized>(pin: Pin<&'a mut T>)
    ensures
        #[trigger] pin.mut_ref() == MutRef::unpack(pin.pointer()),
;

pub broadcast axiom fn axiom_pin_has_resolved<'a, T: ?Sized>(pin: Pin<&'a mut T>)
    ensures
        has_resolved::<Pin<&'a mut T>>(pin) ==> (#[trigger] pin.mut_ref()).future.value()
            == pin.mut_ref().current,
;

pub broadcast group group_pin_axioms {
    axiom_pin_has_resolved,
    axiom_pin_mut_ref_pointer,
}

} // verus!
