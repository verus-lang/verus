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
#[verifier::ext_equal]
pub struct ExOption<V>(core::option::Option<V>);

#[verifier(external_type_specification)]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types_in_ground_variants(E)]
pub struct ExResult<T, E>(core::result::Result<T, E>);

pub open spec fn iter_into_iter_spec<I: Iterator>(i: I) -> I {
    i
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(iter_into_iter_spec)]
pub fn ex_iter_into_iter<I: Iterator>(i: I) -> (r: I)
    ensures r == i
{
    i.into_iter()
}

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

#[verifier::external_fn_specification]
pub fn ex_intrinsics_likely(b: bool) -> (c: bool)
    ensures c == b
{
    core::intrinsics::likely(b)
}

#[verifier::external_fn_specification]
pub fn ex_intrinsics_unlikely(b: bool) -> (c: bool)
    ensures c == b
{
    core::intrinsics::unlikely(b)
}

}
