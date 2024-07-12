use super::super::prelude::*;

use core::alloc::Allocator;

verus!{

#[verifier::external_fn_specification]
pub fn box_into_vec<T, A: Allocator>(b: Box<[T], A>) -> (v: Vec<T, A>)
    ensures v@ == b@
{
    b.into_vec()
}

}
