#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;

verus! {

#[verifier::external_body]
pub proof fn tracked_swap<V>(tracked a: &mut V, tracked b: &mut V)
    ensures
        a == old(b),
        b == old(a),
{
    unimplemented!();
}

/// Make any tracked object permanently shared and get a reference to it.
///
/// Tip: If you try to use this and run into problems relating to the introduction
/// of a lifetime variable, you want to try [`Shared`](crate::shared::Shared) instead.
#[verifier::external_body]
pub proof fn tracked_static_ref<V>(tracked v: V) -> (tracked res: &'static V)
    ensures
        res == v,
{
    unimplemented!();
}

} // verus!
