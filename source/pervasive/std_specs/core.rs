use crate::prelude::*;

verus!{

#[verifier(external_fn_specification)]
pub fn ex_swap<T>(a: &mut T, b: &mut T)
    ensures *a == *old(b), *b == *old(a),
{
    core::mem::swap(a, b)
}

#[verifier(external_type_specification)]
pub struct ExOption<V>(core::option::Option<V>);

#[verifier(external_type_specification)]
pub struct ExResult<T, E>(core::result::Result<T, E>);

#[verifier(external_type_specification)]
pub struct ExRange<Idx>(core::ops::Range<Idx>);

#[verifier(external_type_specification)]
#[verifier(external_body)]
pub struct ExDuration(core::time::Duration);

}
