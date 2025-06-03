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

#[cfg_attr(not(verus_verify_core), deprecated = "is_sized is now defunct; lemmas that require V to be sized should now use the trait bound `V: Sized` instead of is_sized<V>")]
pub uninterp spec fn is_sized<V: ?Sized>() -> bool;

pub uninterp spec fn size_of<V>() -> nat;

pub uninterp spec fn align_of<V>() -> nat;

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

#[verifier::when_used_as_spec(size_of_as_usize)]
pub assume_specification<V>[ core::mem::size_of::<V> ]() -> (u: usize)
    ensures
        u as nat == size_of::<V>(),
    opens_invariants none
    no_unwind
;

#[verifier::when_used_as_spec(align_of_as_usize)]
pub assume_specification<V>[ core::mem::align_of::<V> ]() -> (u: usize)
    ensures
        u as nat == align_of::<V>(),
    opens_invariants none
    no_unwind
;

// This is marked as exec, again, in order to force `V` to be a real exec type.
// Of course, it's still a no-op.
#[verifier::external_body]
#[inline(always)]
pub exec fn layout_for_type_is_valid<V>()
    ensures
        valid_layout(size_of::<V>() as usize, align_of::<V>() as usize),
        size_of::<V>() as usize as nat == size_of::<V>(),
        align_of::<V>() as usize as nat == align_of::<V>(),
    opens_invariants none
    no_unwind
{
}

/// Size of primitives ([Reference](https://doc.rust-lang.org/reference/type-layout.html#r-layout.primitive)).
///
/// Note that alignment may be platform specific; if you need to use alignment, use
/// [Verus's global directive](https://verus-lang.github.io/verus/guide/reference-global.html).
pub broadcast axiom fn layout_of_primitives()
    ensures
        #![trigger size_of::<bool>()]
        #![trigger size_of::<char>()]
        #![trigger size_of::<u8>()]
        #![trigger size_of::<i8>()]
        #![trigger size_of::<u16>()]
        #![trigger size_of::<i16>()]
        #![trigger size_of::<u32>()]
        #![trigger size_of::<i32>()]
        #![trigger size_of::<u64>()]
        #![trigger size_of::<i64>()]
        #![trigger size_of::<usize>()]
        #![trigger size_of::<isize>()]
        size_of::<bool>() == 1,
        size_of::<char>() == 4,
        size_of::<u8>() == size_of::<i8>() == 1,
        size_of::<u16>() == size_of::<i16>() == 2,
        size_of::<u32>() == size_of::<i32>() == 4,
        size_of::<u64>() == size_of::<i64>() == 8,
        size_of::<u128>() == size_of::<i128>() == 16,
        size_of::<usize>() == size_of::<isize>(),
        size_of::<usize>() * 8 == usize::BITS,
;

/// Size and alignment of the unit tuple ([Reference](https://doc.rust-lang.org/reference/type-layout.html#r-layout.tuple.unit)).
pub broadcast axiom fn layout_of_unit_tuple()
    ensures
        #![trigger size_of::<()>()]
        #![trigger align_of::<()>()]
        size_of::<()>() == 0,
        align_of::<()>() == 1,
;

/// Pointers and references have the same layout. Mutability of the pointer or reference does not change the layout. ([Reference](https://doc.rust-lang.org/reference/type-layout.html#r-layout.pointer.intro).)
pub broadcast axiom fn layout_of_references_and_pointers<T: ?Sized>()
    ensures
        #![trigger size_of::<*mut T>()]
        #![trigger size_of::<*const T>()]
        #![trigger size_of::<&T>()]
        #![trigger align_of::<*mut T>()]
        #![trigger align_of::<*const T>()]
        #![trigger align_of::<&T>()]
        size_of::<*mut T>() == size_of::<*const T>() == size_of::<&T>(),
        align_of::<*mut T>() == align_of::<*const T>() == align_of::<&T>(),
;

/// Pointers to sized types have the same size and alignment as usize
/// ([Reference](https://doc.rust-lang.org/reference/type-layout.html#r-layout.pointer.intro)).
pub broadcast axiom fn layout_of_references_and_pointers_for_sized_types<T: Sized>()
    ensures
        #![trigger size_of::<*mut T>()]
        #![trigger align_of::<*mut T>()]
        size_of::<*mut T>() == size_of::<usize>(),
        align_of::<*mut T>() == align_of::<usize>(),
;

pub broadcast group group_layout_axioms {
    layout_of_primitives,
    layout_of_unit_tuple,
    layout_of_references_and_pointers,
    layout_of_references_and_pointers_for_sized_types,
}

} // verus!
