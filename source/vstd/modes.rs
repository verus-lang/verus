#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;

verus! {

#[verifier::tracked_swap_primitive]
pub axiom fn tracked_swap<V>(tracked a: &mut V, tracked b: &mut V)
    ensures
        *final(a) == *old(b),
        *final(b) == *old(a),
;

/// Converts a borrowed value to a borrowed `Tracked` of that value.
pub axiom fn tracked_ref<'a, T: ?Sized>(tracked t: &'a T) -> (tracked out: &'a Tracked<T>)
    ensures
        &**out == t,
;

/// Make any tracked object permanently shared and get a reference to it.
///
/// Tip: If you try to use this and run into problems relating to the introduction
/// of a lifetime variable, you want to try [`Shared`](crate::shared::Shared) instead.
pub proof fn tracked_static_ref<V>(tracked v: V) -> (tracked res: &'static V)
    ensures
        res == v,
{
    tracked_static_mut_ref(v)
}

/// Make any tracked object permanently mutably borrowed.
pub axiom fn tracked_static_mut_ref<V>(tracked v: V) -> (tracked res: &'static mut V)
    ensures
        *res == v,
;

} // verus!
