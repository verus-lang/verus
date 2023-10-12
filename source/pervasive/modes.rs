#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
//use core::marker::PhantomData;

verus! {

#[verifier(external_body)]
pub proof fn tracked_swap<V>(tracked a: &mut V, tracked b: &mut V)
    ensures
        a == old(b),
        b == old(a)
{
    unimplemented!();
}

#[verifier(external_body)]
pub proof fn tracked_static_ref<V>(tracked v: V) -> (tracked res: &'static V)
    ensures res == v,
{
    unimplemented!();
}




} // verus
