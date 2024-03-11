use crate::prelude::*;
use core::clone::Clone;

verus!{

// external_fn_specification doesn't generally support specifying generic functions
// like this; it is special-cased for Clone for now
#[verifier(external_fn_specification)]
pub fn ex_clone_clone<T: Clone>(a: &T) -> T
{
    a.clone()
}

/*
#[verifier(external_fn_specification)]
pub fn ex_clone_clone_from<T: Clone>(a: &mut T, b: &T)
{
    a.clone_from(b)
}
*/

#[verifier::external_fn_specification]
pub fn ex_bool_clone(b: &bool) -> (res: bool)
    ensures res == b,
{
    b.clone()
}


#[allow(suspicious_double_ref_op)]
#[verifier::external_fn_specification]
pub fn ex_ref_clone<'b, T: ?Sized, 'a>(b: &'a &'b T) -> (res: &'b T)
    ensures res == b,
{
    b.clone()
}

/*
#[verifier::external_fn_specification]
pub fn ex_bool_clone_from(dest: &mut bool, source: &bool)
    ensures *dest == source,
{
    dest.clone_from(source)
}
*/

// Cloning a Tracked copies the underlying ghost T
#[verifier::external_fn_specification]
pub fn ex_tracked_clone<A: Copy>(b: &Tracked<A>) -> (res: Tracked<A>)
    ensures res == b,
{
    b.clone()
}

#[verifier::external_fn_specification]
pub fn ex_ghost_clone<A>(b: &Ghost<A>) -> (res: Ghost<A>)
    ensures res == b,
{
    b.clone()
}



}
