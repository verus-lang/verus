#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
//use core::marker::PhantomData;

verus! {

// REVIEW: consider moving these into builtin and erasing them from the VIR
pub struct Gho<A>(pub ghost A);
pub struct Trk<A>(pub tracked A);

#[inline(always)]
#[verifier(external_body)]
pub fn ghost_unwrap_gho<A>(a: Ghost<Gho<A>>) -> (ret: Ghost<A>)
    ensures a@.0 == ret@
{
    Ghost::assume_new()
}

#[inline(always)]
#[verifier(external_body)]
pub fn tracked_unwrap_gho<A>(a: Tracked<Gho<A>>) -> (ret: Tracked<A>)
    ensures a@.0 == ret@
{
    Tracked::assume_new()
}

#[inline(always)]
#[verifier(external_body)]
pub fn tracked_unwrap_trk<A>(a: Tracked<Trk<A>>) -> (ret: Tracked<A>)
    ensures a@.0 == ret@
{
    Tracked::assume_new()
}

#[verifier(external_body)]
pub proof fn tracked_swap<V>(tracked a: &mut V, tracked b: &mut V)
    ensures
        a == old(b),
        b == old(a)
{
    unimplemented!();
}

} // verus
