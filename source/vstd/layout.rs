#![allow(unused_imports)]

use super::prelude::*;

verus! {

// TODO add some means for Verus to calculate the size & alignment of types
// TODO use a definition from a math library, once we have one.
pub open spec fn is_power_2(n: int) -> bool
    decreases n,
{
    if n <= 0 {
        false
    } else if n == 1 {
        true
    } else {
        n % 2 == 0 && is_power_2(n / 2)
    }
}

/// Matches the conditions here: <https://doc.rust-lang.org/stable/std/alloc/struct.Layout.html>
pub open spec fn valid_layout(size: usize, align: usize) -> bool {
    is_power_2(align as int) && size <= isize::MAX as int - (isize::MAX as int % align as int)
}

// Keep in mind that the `V: Sized` trait bound is COMPLETELY ignored in the
// VIR encoding. It is not possible to write an axiom like
// "If `V: Sized`, then `size_of::<&V>() == size_of::<usize>()`.
// If you tried, it wouldn't work the way you expect.
// The ONLY thing that checks Sized marker bounds is rustc, but it is possible
// to get around rustc's checks with broadcast_forall.
// Therefore, in spec-land, we must use the `is_sized` predicate instead.
//
// Note: for exec functions, and for proof functions that take tracked arguments,
// we CAN rely on rustc's checking. So in those cases it's okay for us to assume
// a `V: Sized` type is sized.
pub spec fn is_sized<V: ?Sized>() -> bool;

pub spec fn size_of<V>() -> nat;

pub spec fn align_of<V>() -> nat;

// Naturally, the size of any executable type is going to fit into a `usize`.
// What I'm not sure of is whether it will be possible to "reason about" arbitrarily
// big types _in ghost code_ without tripping one of rustc's checks.
//
// I think it could go like this:
//   - Have some polymorphic code that constructs a giant tuple and proves false
//   - Make sure the code doesn't get monomorphized by rustc
//   - To export the 'false' fact from the polymorphic code without monomorphizing,
//     use broadcast_forall.
//
// Therefore, we are NOT creating an axiom that `size_of` fits in usize.
// However, we still give the guarantee that if you call `core::mem::size_of`
// at runtime, then the resulting usize is correct.
#[verifier::inline]
pub open spec fn size_of_as_usize<V>() -> usize
    recommends
        size_of::<V>() as usize as int == size_of::<V>(),
{
    size_of::<V>() as usize
}

#[verifier::inline]
pub open spec fn align_of_as_usize<V>() -> usize
    recommends
        align_of::<V>() as usize as int == align_of::<V>(),
{
    align_of::<V>() as usize
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(size_of_as_usize)]
pub fn ex_size_of<V>() -> (u: usize)
    ensures
        is_sized::<V>(),
        u as nat == size_of::<V>(),
    opens_invariants none
    no_unwind
{
    core::mem::size_of::<V>()
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(align_of_as_usize)]
pub fn ex_align_of<V>() -> (u: usize)
    ensures
        is_sized::<V>(),
        u as nat == align_of::<V>(),
    opens_invariants none
    no_unwind
{
    core::mem::align_of::<V>()
}

// This is marked as exec, again, in order to force `V` to be a real exec type.
// Of course, it's still a no-op.
#[verifier::external_body]
#[inline(always)]
pub exec fn layout_for_type_is_valid<V>()
    ensures
        valid_layout(size_of::<V>() as usize, align_of::<V>() as usize),
        is_sized::<V>(),
        size_of::<V>() as usize as nat == size_of::<V>(),
        align_of::<V>() as usize as nat == align_of::<V>(),
    opens_invariants none
    no_unwind
{
}

} // verus!
