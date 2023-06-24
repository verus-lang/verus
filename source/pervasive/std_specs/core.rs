use crate::prelude::*;

verus!{

#[verifier(external_fn_specification)]
pub fn ex_swap<T>(a: &mut T, b: &mut T)
    ensures *a == *old(b), *b == *old(a),
{
    core::mem::swap(a, b)
}

#[verifier(external_type_specification)]
#[verifier::accept_recursive_types(V)]
pub struct ExOption<V>(core::option::Option<V>);

#[verifier(external_type_specification)]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types_in_ground_variants(E)]
pub struct ExResult<T, E>(core::result::Result<T, E>);

#[verifier(external_type_specification)]
#[verifier::reject_recursive_types_in_ground_variants(Idx)]
pub struct ExRange<Idx>(core::ops::Range<Idx>);

// I don't really expect this to be particularly useful;
// this is mostly here because I wanted an easy way to test
// the combination of external_type_specification & external_body
// in a cross-crate context.

#[verifier(external_type_specification)]
#[verifier(external_body)]
pub struct ExDuration(core::time::Duration);

#[verifier(external_type_specification)]
#[verifier(external_body)]
#[verifier::reject_recursive_types_in_ground_variants(V)]
pub struct ExPhantomData<V: ?Sized>(core::marker::PhantomData<V>);


}
