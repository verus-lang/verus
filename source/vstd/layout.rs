#![allow(unused_imports)]

use super::arithmetic::power::*;
use super::arithmetic::power2::*;
use super::bits::*;
use super::math::*;
use super::prelude::*;
use core::mem::MaybeUninit;

verus! {

/// Matches the conditions here: <https://doc.rust-lang.org/stable/std/alloc/struct.Layout.html>
pub open spec fn valid_layout(size: usize, align: usize) -> bool {
    is_pow2(align as int) && size <= isize::MAX as int - (isize::MAX as int % align as int)
}

#[cfg_attr(not(verus_verify_core), deprecated = "is_sized is now defunct; lemmas that require V to be sized should now use the trait bound `V: Sized` instead of is_sized<V>")]
pub uninterp spec fn is_sized<V: ?Sized>() -> bool;

pub uninterp spec fn size_of<V>() -> nat;

pub uninterp spec fn align_of<V>() -> nat;

// compiler wants &V instead of V -- complains about V not being Sized
/// Spec for `size_of_val`: <https://doc.rust-lang.org/std/mem/fn.size_of_val.html>.
pub uninterp spec fn spec_size_of_val<V: ?Sized>(val: &V) -> nat;

/// Spec for `align_of_val`: <https://doc.rust-lang.org/std/mem/fn.align_of_val.html>.
pub uninterp spec fn spec_align_of_val<V: ?Sized>(val: &V) -> nat;

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

#[verifier::inline]
pub open spec fn size_of_val_as_usize<V: ?Sized>(val: &V) -> usize
    recommends
        spec_size_of_val::<V>(val) as usize as int == spec_size_of_val::<V>(val),
{
    spec_size_of_val::<V>(val) as usize
}

#[verifier::inline]
pub open spec fn align_of_val_as_usize<V: ?Sized>(val: &V) -> usize
    recommends
        spec_align_of_val::<V>(val) as usize as int == spec_align_of_val::<V>(val),
{
    spec_align_of_val::<V>(val) as usize
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

#[verifier::when_used_as_spec(size_of_val_as_usize)]
pub assume_specification<V: ?Sized>[ core::mem::size_of_val::<V> ](val: &V) -> (u: usize)
    ensures
        u as nat == spec_size_of_val::<V>(val),
    opens_invariants none
    no_unwind
;

#[verifier::when_used_as_spec(align_of_val_as_usize)]
pub assume_specification<V: ?Sized>[ core::mem::align_of_val::<V> ](val: &V) -> (u: usize)
    ensures
        u as nat == spec_align_of_val::<V>(val),
    opens_invariants none
    no_unwind
;

/// Lemma to learn that the (size, alignment) of a type is a valid "layout".
/// See [`valid_layout`] for the exact conditions.
///
/// Also exports that size is a multiple of alignment ([Reference](https://doc.rust-lang.org/reference/type-layout.html#r-layout.properties.size)).
///
/// Note that, unusually for a lemma, this is an `exec`-mode function. (This is necessary to
/// ensure that the types are really compilable, as ghost code can reason about "virtual" types
/// that exceed these bounds.) Despite being `exec`-mode, it is a no-op.
#[verifier::external_body]
#[inline(always)]
pub const exec fn layout_for_type_is_valid<V>()
    ensures
        valid_layout(size_of::<V>() as usize, align_of::<V>() as usize),
        size_of::<V>() as usize as nat == size_of::<V>(),
        align_of::<V>() as usize as nat == align_of::<V>(),
        align_of::<V>() != 0,
        size_of::<V>() % align_of::<V>() == 0,
    opens_invariants none
    no_unwind
{
}

/// Lemma to learn that the (size, alignment) of a (possibly not Sized) value is a valid "layout".
/// See [`valid_layout`] for the exact conditions.
///
/// Also exports that size is a multiple of alignment ([Reference](https://doc.rust-lang.org/reference/type-layout.html#r-layout.properties.size)).
///
/// Note that, unusually for a lemma, this is an `exec`-mode function. (This is necessary to
/// ensure that the types are really compilable, as ghost code can reason about "virtual" types
/// that exceed these bounds.) Despite being `exec`-mode, it is a no-op.
#[verifier::external_body]
#[inline(always)]
pub const exec fn layout_for_val_is_valid<V: ?Sized>(val: Tracked<&V>)
    ensures
        valid_layout(spec_size_of_val::<V>(val@) as usize, spec_align_of_val::<V>(val@) as usize),
        spec_size_of_val::<V>(val@) as usize as nat == spec_size_of_val::<V>(val@),
        spec_align_of_val::<V>(val@) as usize as nat == spec_align_of_val::<V>(val@),
        spec_align_of_val::<V>(val@) != 0,
        spec_size_of_val::<V>(val@) % spec_align_of_val::<V>(val@) == 0,
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

/// Pointers and references have the same layout. Mutability of the pointer or reference does not change the layout ([Reference](https://doc.rust-lang.org/reference/type-layout.html#r-layout.pointer.intro)).
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

/// Pointers to sized types have the same size and alignment as `usize`
/// ([Reference](https://doc.rust-lang.org/reference/type-layout.html#r-layout.pointer.intro)).
pub broadcast axiom fn layout_of_references_and_pointers_for_sized_types<T: Sized>()
    ensures
        #![trigger size_of::<*mut T>()]
        #![trigger align_of::<*mut T>()]
        size_of::<*mut T>() == size_of::<usize>(),
        align_of::<*mut T>() == align_of::<usize>(),
;

/// Pointers to unsized types have at least the size and alignment as pointers to sized types
/// ([Reference](https://doc.rust-lang.org/reference/type-layout.html#r-layout.pointer.unsized)).
pub broadcast axiom fn layout_of_references_and_pointers_for_unsized_types<T: ?Sized>()
    ensures
        #![trigger size_of::<*mut T>()]
        #![trigger align_of::<*mut T>()]
        size_of::<*mut T>() >= size_of::<usize>(),
        align_of::<*mut T>() >= align_of::<usize>(),
;

/// Slices have the same layout as the underlying type.
/// ([Reference](https://doc.rust-lang.org/reference/type-layout.html#slice-layout)).
pub broadcast axiom fn layout_of_slices<T>(x: &[T])
    ensures
        #![trigger spec_size_of_val::<[T]>(x)]
        #![trigger spec_align_of_val::<[T]>(x)]
        spec_align_of_val::<[T]>(x) == align_of::<T>(),
        spec_size_of_val::<[T]>(x) == x@.len() * size_of::<T>(),
;

/// `str` has the same layout as `[u8]`, which has the same layout as `u8`.
/// ([Reference](https://doc.rust-lang.org/reference/type-layout.html#str-layout)).
pub broadcast axiom fn layout_of_str(x: &str)
    ensures
        #![trigger spec_align_of_val::<str>(x)]
        #![trigger spec_size_of_val::<str>(x)]
        // todo - how to specify spec_size_of_val::<str>(x) in terms of the byte representation of x?
        spec_align_of_val::<str>(x) == align_of::<u8>(),
;

/// The size is a multiple of alignment and alignment is always a power of 2
/// ([reference](https://doc.rust-lang.org/reference/type-layout.html#r-layout.properties.size)).
pub broadcast axiom fn align_properties<T>()
    ensures
        #![trigger align_of::<T>()]
        size_of::<T>() % align_of::<T>() == 0,
        is_pow2(align_of::<T>() as int),
;

/// The alignment is at least 1
/// ([reference](https://doc.rust-lang.org/reference/type-layout.html#r-layout.properties.size)).
pub broadcast proof fn align_nonzero<T>()
    ensures
        #![trigger align_of::<T>()]
        align_of::<T>() > 0,
{
    broadcast use crate::vstd::arithmetic::power::lemma_pow_positive, align_properties;
    broadcast use crate::vstd::arithmetic::power2::is_pow2_equiv;

}

/// The alignment of `u8` is 1, per [type layout rules](https://doc.rust-lang.org/reference/type-layout.html).
/// Note: This is not part of the alignment broadcast group due to proof time-out,
/// so it must be imported directly as needed.
pub broadcast proof fn align_of_u8()
    ensures
        #![trigger size_of::<u8>()]
        align_of::<u8>() == 1,
{
    broadcast use {
        layout_of_primitives,
        align_properties,
        align_nonzero,
        crate::vstd::arithmetic::div_mod::lemma_mod_is_zero,
    };

}

/// The size of a usize will always be a power of 2,
/// since Verus assumes 32 or 64-bit architecture.
pub proof fn usize_size_pow2()
    ensures
        is_pow2(size_of::<usize>() as int),
{
    broadcast use super::group_vstd_default;

    reveal(is_pow2);

    assert(is_pow2(4)) by (compute);
    assert(is_pow2(8)) by (compute);
}

/// Relates the unsigned integer max values to their sizes and bits.
pub proof fn unsigned_int_max_values()
    ensures
        (usize::MAX as nat) == pow2(usize::BITS as nat) - 1,
        (usize::MAX as nat) == pow(256, size_of::<usize>()) - 1,
        (u8::MAX as nat) == pow2(u8::BITS as nat) - 1,
        (u8::MAX as nat) == pow(256, size_of::<u8>()) - 1,
        (u16::MAX as nat) == pow2(u16::BITS as nat) - 1,
        (u16::MAX as nat) == pow(256, size_of::<u16>()) - 1,
        (u32::MAX as nat) == pow2(u32::BITS as nat) - 1,
        (u32::MAX as nat) == pow(256, size_of::<u32>()) - 1,
        (u64::MAX as nat) == pow2(u64::BITS as nat) - 1,
        (u64::MAX as nat) == pow(256, size_of::<u64>()) - 1,
        (u128::MAX as nat) == pow2(u128::BITS as nat) - 1,
        (u128::MAX as nat) == pow(256, size_of::<u128>()) - 1,
{
    broadcast use layout_of_primitives;

    reveal(pow);
    assert(0x100 == pow2(8)) by (compute);
    assert(0x1_0000 == pow2(16)) by (compute);
    assert(0x1_0000_0000 == pow2(32)) by (compute);
    assert(0x1_0000_0000_0000_0000 == pow2(64)) by (compute);
    assert(0x1_0000_0000_0000_0000_0000_0000_0000_0000 == pow2(128)) by (compute);
    assert(pow(256, 1) == pow2(8)) by (compute);
    assert(pow(256, 2) == pow2(16)) by (compute);
    assert(pow(256, 4) == pow2(32)) by (compute);
    assert(pow(256, 8) == pow2(64)) by (compute);
    assert(pow(256, 16) == pow2(128)) by (compute);
}

/// Relates the signed integer min and max values to their sizes and bits.
pub proof fn signed_int_min_max_values()
    ensures
        (isize::MAX as nat) == pow2((isize::BITS - 1) as nat) - 1,
        abs(isize::MIN as int) == pow2((isize::BITS - 1) as nat),
        (isize::MAX as nat) * 2 == pow(256, size_of::<isize>()) - 2,
        abs(isize::MIN as int) * 2 == pow(256, size_of::<isize>()),
        (i8::MAX as nat) == pow2((i8::BITS - 1) as nat) - 1,
        abs(i8::MIN as int) == pow2((i8::BITS - 1) as nat),
        (i8::MAX as nat) * 2 == pow(256, size_of::<i8>()) - 2,
        abs(i8::MIN as int) * 2 == pow(256, size_of::<i8>()),
        (i16::MAX as nat) == pow2((i16::BITS - 1) as nat) - 1,
        abs(i16::MIN as int) == pow2((i16::BITS - 1) as nat),
        (i16::MAX as nat) * 2 == pow(256, size_of::<i16>()) - 2,
        abs(i16::MIN as int) * 2 == pow(256, size_of::<i16>()),
        (i32::MAX as nat) == pow2((i32::BITS - 1) as nat) - 1,
        abs(i32::MIN as int) == pow2((i32::BITS - 1) as nat),
        (i32::MAX as nat) * 2 == pow(256, size_of::<i32>()) - 2,
        abs(i32::MIN as int) * 2 == pow(256, size_of::<i32>()),
        (i64::MAX as nat) == pow2((i64::BITS - 1) as nat) - 1,
        abs(i64::MIN as int) == pow2((i64::BITS - 1) as nat),
        (i64::MAX as nat) * 2 == pow(256, size_of::<i64>()) - 2,
        abs(i64::MIN as int) * 2 == pow(256, size_of::<i64>()),
        (i128::MAX as nat) == pow2((i128::BITS - 1) as nat) - 1,
        abs(i128::MIN as int) == pow2((i128::BITS - 1) as nat),
        (i128::MAX as nat) * 2 == pow(256, size_of::<i128>()) - 2,
        abs(i128::MIN as int) * 2 == pow(256, size_of::<i128>()),
{
    broadcast use layout_of_primitives;

    reveal(pow);
    assert(0x80 == pow2(7)) by (compute);
    assert(0x8_000 == pow2(15)) by (compute);
    assert(0x80_000_000 == pow2(31)) by (compute);
    assert(0x8_000_000_000_000_000 == pow2(63)) by (compute);
    assert(0x80_000_000_000_000_000_000_000_000_000_000 == pow2(127)) by (compute);
    assert(pow(256, 1) == pow2(7) * 2) by (compute);
    assert(pow(256, 2) == pow2(15) * 2) by (compute);
    assert(pow(256, 4) == pow2(31) * 2) by (compute);
    assert(pow(256, 8) == pow2(63) * 2) by (compute);
    assert(pow(256, 16) == pow2(127) * 2) by (compute);
}

pub broadcast group group_align_properties {
    align_properties,
    align_nonzero,
}

/// [`MaybeUninit<T>`](core::mem::MaybeUninit) has the same size and aligment as `T`
/// ([Reference](https://doc.rust-lang.org/stable/std/mem/union.MaybeUninit.html#layout-1)).
pub broadcast axiom fn layout_of_maybe_uninit<T: Sized>()
    ensures
        #![trigger size_of::<MaybeUninit<T>>()]
        #![trigger align_of::<MaybeUninit<T>>()]
        size_of::<MaybeUninit<T>>() == size_of::<T>(),
        align_of::<MaybeUninit<T>>() == align_of::<T>(),
;

pub broadcast group group_layout_axioms {
    layout_of_primitives,
    layout_of_unit_tuple,
    layout_of_references_and_pointers,
    layout_of_references_and_pointers_for_sized_types,
    layout_of_references_and_pointers_for_unsized_types,
    layout_of_slices,
    layout_of_str,
    layout_of_maybe_uninit,
    group_align_properties,
}

} // verus!
