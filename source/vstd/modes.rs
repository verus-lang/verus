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

/// Types whose values own no resources (no permissions, tokens or other tracked data),
/// so any spec value can be used as a tracked one.
pub unsafe trait TrivialOwnership {
    /// Any type invariants on `self`.
    /// Specs marked with `#[verifier::type_invariant]` should be included here.
    spec fn type_inv(&self) -> bool;
}

/// Makes a spec value tracked, for any type that owns no resources.
pub axiom fn tracked_from_spec<T: TrivialOwnership>(v: T) -> (tracked out: T)
    requires
        v.type_inv(),
    ensures
        out == v,
;

/// Makes a spec value a tracked reference, for any type that owns no resources.
pub axiom fn tracked_from_spec_ref<'a, T: ?Sized + TrivialOwnership>(v: &T) -> (tracked out: &'a T)
    requires
        v.type_inv(),
    ensures
        out == v,
;

/// Implements `TrivialOwnership` with a trivial type invariant for a given type.
/// The type must own no resources (no permissions, tokens or other tracked data)
/// and must not have a `#[verifier::type_invariant]`.
macro_rules! impl_trivial_ownership {
    ($($t:ty),* $(,)?) => {$(
        verus! {
            unsafe impl TrivialOwnership for $t {
                open spec fn type_inv(&self) -> bool {
                    true
                }
            }
        }
    )*};
}

impl_trivial_ownership!(
    u8,
    u16,
    u32,
    u64,
    u128,
    usize,
    i8,
    i16,
    i32,
    i64,
    i128,
    isize,
    bool,
    (),
    char,
    str,
);

unsafe impl<T> TrivialOwnership for *const T {
    open spec fn type_inv(&self) -> bool {
        true
    }
}

unsafe impl<T> TrivialOwnership for *mut T {
    open spec fn type_inv(&self) -> bool {
        true
    }
}

unsafe impl<T: TrivialOwnership> TrivialOwnership for [T] {
    open spec fn type_inv(&self) -> bool {
        forall|i| 0 <= i < self@.len() ==> #[trigger] self@[i].type_inv()
    }
}

} // verus!
