use super::super::prelude::*;
use core::clone::Clone;

verus! {

#[verifier::external_trait_specification]
pub trait ExClone: Sized {
    type ExternalTraitSpecificationFor: core::clone::Clone;

    fn clone(&self) -> Self;
}

/*
#[verifier::external_fn_specification]
pub fn ex_clone_clone_from<T: Clone>(a: &mut T, b: &T)
{
    a.clone_from(b)
}
*/

#[verifier::external_fn_specification]
pub fn ex_bool_clone(b: &bool) -> (res: bool)
    ensures
        res == b,
{
    b.clone()
}

#[verifier::external_fn_specification]
pub fn ex_char_clone(c: &char) -> (res: char)
    ensures
        res == c,
{
    c.clone()
}

#[allow(suspicious_double_ref_op)]
#[verifier::external_fn_specification]
pub fn ex_ref_clone<'b, T: ?Sized, 'a>(b: &'a &'b T) -> (res: &'b T)
    ensures
        res == b,
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
pub fn ex_tracked_clone<T: Copy>(b: &Tracked<T>) -> (res: Tracked<T>)
    ensures
        res == b,
{
    b.clone()
}

#[verifier::external_fn_specification]
pub fn ex_ghost_clone<T>(b: &Ghost<T>) -> (res: Ghost<T>)
    ensures
        res == b,
{
    b.clone()
}

} // verus!
