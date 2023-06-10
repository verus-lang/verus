use crate::prelude::*;

verus!{

#[verifier(external_fn_specification)]
pub fn ex_swap<T>(a: &mut T, b: &mut T)
    ensures *a == *old(b), *b == *old(a),
{
    core::mem::swap(a, b)
}

}
