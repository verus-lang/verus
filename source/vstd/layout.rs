#![allow(unused_imports)]

use super::group_vstd_default;
use super::math::*;
use super::prelude::*;
use crate::vstd::arithmetic::power::*;
use crate::vstd::arithmetic::power2::*;
use crate::vstd::bits::*;

verus! {

// TODO add some means for Verus to calculate the size & alignment of types
// TODO use a definition from a math library, once we have one.
#[verifier::opaque]
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

pub open spec fn is_power_2_exists(m: int) -> bool {
    exists|i: nat| pow(2, i) == m
}

pub broadcast proof fn is_power_2_equiv(n: int)
    ensures
        #![trigger is_power_2(n)]
        #![trigger is_power_2_exists(n)]
        is_power_2(n) <==> is_power_2_exists(n),
{
    if is_power_2(n) {
        assert(is_power_2_exists(n)) by {
            is_power_2_equiv_forward(n);
        }
    }
    if is_power_2_exists(n) {
        assert(is_power_2(n)) by {
            broadcast use lemma_pow_positive;

            is_power_2_equiv_reverse(n);
        }
    }
}

proof fn is_power_2_equiv_forward(n: int)
    requires
        is_power_2(n),
    ensures
        is_power_2_exists(n),
    decreases n,
{
    reveal(is_power_2);
    reveal(pow);

    if n == 1 {
        broadcast use lemma_pow0;

        assert(pow(2, 0) == n);
    } else {
        is_power_2_equiv_forward(n / 2);
        let exp = choose|i: nat| pow(2, i) == n / 2;
        assert(pow(2, exp + 1) == 2 * pow(2, exp));
    }
}

proof fn is_power_2_equiv_reverse(n: int)
    requires
        n > 0,
        is_power_2_exists(n),
    ensures
        is_power_2(n),
    decreases n,
{
    reveal(is_power_2);
    reveal(pow);

    let exp = choose|i: nat| pow(2, i) == n;

    if exp == 0 {
        broadcast use lemma_pow0;

    } else {
        assert(pow(2, (exp - 1) as nat) == n / 2);
        is_power_2_equiv_reverse(n / 2);
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

// compiler wants &V instead of V -- complains about V not being Sized
/// Spec for: https://doc.rust-lang.org/std/mem/fn.size_of_val.html
pub uninterp spec fn spec_size_of_val<V: ?Sized>(val: &V) -> nat;

/// Spec for: https://doc.rust-lang.org/std/mem/fn.align_of_val.html
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

/// The alignment of `u8` is 1, per [type layout rules](https://doc.rust-lang.org/reference/type-layout.html).
/// Note: This is not part of the alignment broadcast group due to proof time-out,
/// so it must be imported directly as needed.
pub broadcast proof fn align_of_u8()
    ensures
        #![trigger align_of::<u8>()]
        align_of::<u8>() == 1,
{
    broadcast use {
        layout_of_primitives,
        align_properties,
        align_nonzero,
        crate::vstd::arithmetic::div_mod::lemma_mod_is_zero,
    };

}

// The size is a multiple of alignment and alignment is always a power of 2 by
// https://doc.rust-lang.org/reference/type-layout.html#r-layout.properties.size
pub broadcast axiom fn align_properties<T>()
    ensures
        #![trigger align_of::<T>()]
        size_of::<T>() % align_of::<T>() == 0,
        is_power_2_exists(align_of::<T>() as int),
;

// The alignment is at least 1 by https://doc.rust-lang.org/reference/type-layout.html#r-layout.properties.size
pub broadcast proof fn align_nonzero<T>()
    ensures
        #![trigger align_of::<T>()]
        align_of::<T>() > 0,
{
    broadcast use crate::vstd::arithmetic::power::lemma_pow_positive, align_properties;
}

pub proof fn usize_size_pow2()
    ensures
        is_power_2(size_of::<usize>() as int),
{
    broadcast use group_vstd_default;

    assert(is_power_2(4)) by (compute);
    assert(is_power_2(8)) by (compute);
}

pub proof fn unsigned_int_max_bounds()
    ensures
        (usize::MAX as nat) < pow2(usize::BITS as nat),
        (usize::MAX as nat) < pow(256, size_of::<usize>()),
        (u8::MAX as nat) < pow2(u8::BITS as nat),
        (u8::MAX as nat) < pow(256, size_of::<u8>()),
        (u16::MAX as nat) < pow2(u16::BITS as nat),
        (u16::MAX as nat) < pow(256, size_of::<u16>()),
        (u32::MAX as nat) < pow2(u32::BITS as nat),
        (u32::MAX as nat) < pow(256, size_of::<u32>()),
        (u64::MAX as nat) < pow2(u64::BITS as nat),
        (u64::MAX as nat) < pow(256, size_of::<u64>()),
        (u128::MAX as nat) < pow2(u128::BITS as nat),
        (u128::MAX as nat) < pow(256, size_of::<u128>()),
{
    broadcast use layout_of_primitives;

    reveal(pow);
    reveal(pow2);
    assert(0x100 - 1 < pow2(8)) by (compute);
    assert(0x1_0000 - 1 < pow2(16)) by (compute);
    assert(0x1_0000_0000 - 1 < pow2(32)) by (compute);
    assert(0x1_0000_0000_0000_0000 - 1 < pow2(64)) by (compute);
    assert(0x1_0000_0000_0000_0000_0000_0000_0000_0000 - 1 < pow2(128)) by (compute);
    assert(pow(256, 1) == pow2(8)) by (compute);
    assert(pow(256, 2) == pow2(16)) by (compute);
    assert(pow(256, 4) == pow2(32)) by (compute);
    assert(pow(256, 8) == pow2(64)) by (compute);
    assert(pow(256, 16) == pow2(128)) by (compute);
}

pub proof fn signed_int_min_max_bounds()
    ensures
        (isize::MAX as nat) < pow2((isize::BITS - 1) as nat),
        abs(isize::MIN as int) == pow2((isize::BITS - 1) as nat),
        (isize::MAX as nat) * 2 < pow(256, size_of::<isize>()),
        abs(isize::MIN as int) * 2 == pow(256, size_of::<isize>()),
        (i8::MAX as nat) < pow2((i8::BITS - 1) as nat),
        abs(i8::MIN as int) == pow2((i8::BITS - 1) as nat),
        (i8::MAX as nat) * 2 < pow(256, size_of::<i8>()),
        abs(i8::MIN as int) * 2 == pow(256, size_of::<i8>()),
        (i16::MAX as nat) < pow2((i16::BITS - 1) as nat),
        abs(i16::MIN as int) == pow2((i16::BITS - 1) as nat),
        (i16::MAX as nat) * 2 < pow(256, size_of::<i16>()),
        abs(i16::MIN as int) * 2 == pow(256, size_of::<i16>()),
        (i32::MAX as nat) < pow2((i32::BITS - 1) as nat),
        abs(i32::MIN as int) == pow2((i32::BITS - 1) as nat),
        (i32::MAX as nat) * 2 < pow(256, size_of::<i32>()),
        abs(i32::MIN as int) * 2 == pow(256, size_of::<i32>()),
        (i64::MAX as nat) < pow2((i64::BITS - 1) as nat),
        abs(i64::MIN as int) == pow2((i64::BITS - 1) as nat),
        (i64::MAX as nat) * 2 < pow(256, size_of::<i64>()),
        abs(i64::MIN as int) * 2 == pow(256, size_of::<i64>()),
        (i128::MAX as nat) < pow2((i128::BITS - 1) as nat),
        abs(i128::MIN as int) == pow2((i128::BITS - 1) as nat),
        (i128::MAX as nat) * 2 < pow(256, size_of::<i128>()),
        abs(i128::MIN as int) * 2 == pow(256, size_of::<i128>()),
{
    broadcast use layout_of_primitives;

    reveal(pow);
    reveal(pow2);
    assert(0x80 - 1 < pow2(7)) by (compute);
    assert(0x80 == pow2(7)) by (compute);
    assert(0x8_000 - 1 < pow2(15)) by (compute);
    assert(0x8_000 == pow2(15)) by (compute);
    assert(0x80_000_000 - 1 < pow2(31)) by (compute);
    assert(0x80_000_000 == pow2(31)) by (compute);
    assert(0x8_000_000_000_000_000 - 1 < pow2(63)) by (compute);
    assert(0x8_000_000_000_000_000 == pow2(63)) by (compute);
    assert(0x80_000_000_000_000_000_000_000_000_000_000 - 1 < pow2(127)) by (compute);
    assert(0x80_000_000_000_000_000_000_000_000_000_000 == pow2(127)) by (compute);
    assert(pow(256, 1) == pow2(7) * 2) by (compute);
    assert(pow(256, 2) == pow2(15) * 2) by (compute);
    assert(pow(256, 4) == pow2(31) * 2) by (compute);
    assert(pow(256, 8) == pow2(63) * 2) by (compute);
    assert(pow(256, 16) == pow2(127) * 2) by (compute);
}

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

/// Pointers to sized types have the same size and alignment as usize
/// ([Reference](https://doc.rust-lang.org/reference/type-layout.html#r-layout.pointer.intro)).
pub broadcast axiom fn layout_of_references_and_pointers_for_sized_types<T: Sized>()
    ensures
        #![trigger size_of::<*mut T>()]
        #![trigger align_of::<*mut T>()]
        size_of::<*mut T>() == size_of::<usize>(),
        align_of::<*mut T>() == align_of::<usize>(),
;

/// Pointers to unsized types have the at least the size and alignment as pointers to sized types
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
        spec_align_of_val::<str>(x) == align_of::<
            u8,
        >(),
// todo - how to specify spec_size_of_val::<str>(x) in terms of the byte representation of x?

;

pub broadcast group group_align_properties {
    align_properties,
    align_nonzero,
}

pub broadcast group group_layout_axioms {
    layout_of_primitives,
    layout_of_unit_tuple,
    layout_of_references_and_pointers,
    layout_of_references_and_pointers_for_sized_types,
    layout_of_references_and_pointers_for_unsized_types,
    layout_of_slices,
    layout_of_str,
    group_align_properties,
}

} // verus!
