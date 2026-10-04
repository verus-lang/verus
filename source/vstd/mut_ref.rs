#![allow(unused_imports)]

use super::pervasive::*;
use super::prelude::*;
use super::proph::*;

verus! {

pub ghost struct MutRef<'a, T: ?Sized> {
    pub ptr: *mut T,
    pub current: &'a T,
    pub future: ProphecyGhost<&'a T>,
}

impl<'a, T: ?Sized> MutRef<'a, T> {
    pub uninterp spec fn pack(self) -> &'a mut T;

    pub uninterp spec fn unpack(r: &'a mut T) -> Self;
}

pub broadcast axiom fn axiom_unpack_mut_ref_current<T>(a: &mut T)
    ensures
        mut_ref_current(a) == (#[trigger] MutRef::unpack(a)).current,
;

pub broadcast axiom fn axiom_unpack_mut_ref_future<T>(a: &mut T)
    ensures
        mut_ref_future(a) == (#[trigger] MutRef::unpack(a)).future.value(),
;

pub broadcast axiom fn axiom_unpack_pack<T: ?Sized>(data: MutRef<T>)
    ensures
        MutRef::unpack(#[trigger] data.pack()) == data,
;

pub uninterp spec fn pack2<'a, T: ?Sized>(data: MutRef<'a, T>) -> &'a mut T;

pub broadcast axiom fn axiom_pack2_unpack<T: ?Sized>(a: &mut T)
    ensures
        pack2(#[trigger] MutRef::unpack(a)) == a,
;

pub axiom fn borrow_prophecy_var<'a, 'b, T: ?Sized>(tracked m: &'a &'b mut T) -> (tracked t:
    &'a ProphecyGhost<&'b T>)
    ensures
        t.value() == &*final(*m),
;

pub broadcast group group_mut_ref_axioms {
    axiom_unpack_mut_ref_current,
    axiom_unpack_mut_ref_future,
    axiom_unpack_pack,
    axiom_pack2_unpack,
}

} // verus!
