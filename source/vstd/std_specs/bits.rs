use super::super::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use super::super::arithmetic::power2::{pow2, lemma_pow2_unfold, lemma2_to64};
#[cfg(verus_keep_ghost)]
use super::super::bits::{lemma_unsigned_int_max_is_pow2_minus_1, nat_count_ones};
#[cfg(verus_keep_ghost)]
use super::super::layout::unsigned_int_max_values;

// TODO mark the lemmas as not external_body when it's supported
// along with broadcast_forall
///////////////////////////
/////////////////////////// For u8
/// Equivalent to `i.trailing_zeros()`.
/// See [`axiom_u8_trailing_zeros`] for useful properties.
pub closed spec fn u8_trailing_zeros(i: u8) -> u32
    decreases i,
{
    if i == 0 {
        8
    } else if (i & 1) != 0 {
        0
    } else {
        (1 + u8_trailing_zeros(i / 2)) as u32
    }
}

/// Equivalent to `i.leading_zeros()`.
/// See [`axiom_u8_leading_zeros`] for useful properties.
pub closed spec fn u8_leading_zeros(i: u8) -> u32
    decreases i,
{
    if i == 0 {
        8
    } else {
        (u8_leading_zeros(i / 2) - 1) as u32
    }
}

/// Equivalent to `i.trailing_ones()`.
/// See [`axiom_u8_trailing_ones`] for useful properties.
pub open spec fn u8_trailing_ones(i: u8) -> u32 {
    u8_trailing_zeros(!i)
}

/// Equivalent to `i.leading_ones()`.
/// See [`axiom_u8_leading_ones`] for useful properties.
pub open spec fn u8_leading_ones(i: u8) -> u32 {
    u8_leading_zeros(!i)
}

#[verifier::when_used_as_spec(u8_trailing_zeros)]
pub assume_specification[ u8::trailing_zeros ](i: u8) -> (r: u32)
    ensures
        r == u8_trailing_zeros(i),
;

#[verifier::when_used_as_spec(u8_trailing_ones)]
pub assume_specification[ u8::trailing_ones ](i: u8) -> (r: u32)
    ensures
        r == u8_trailing_ones(i),
;

#[verifier::when_used_as_spec(u8_leading_zeros)]
pub assume_specification[ u8::leading_zeros ](i: u8) -> (r: u32)
    ensures
        r == u8_leading_zeros(i),
;

#[verifier::when_used_as_spec(u8_leading_ones)]
pub assume_specification[ u8::leading_ones ](i: u8) -> (r: u32)
    ensures
        r == u8_leading_ones(i),
;

pub broadcast proof fn axiom_u8_trailing_zeros(i: u8)
    ensures
        0 <= #[trigger] u8_trailing_zeros(i) <= 8,
        i == 0 <==> u8_trailing_zeros(i) == 8,
        // i^th bit is 1
        0 <= u8_trailing_zeros(i) < 8 ==> (i >> u8_trailing_zeros(i) as u8) & 1u8 == 1u8,
        // trailing bits are 0
        i << sub(8, u8_trailing_zeros(i) as u8) == 0,
        forall|j: u8| 0 <= j < u8_trailing_zeros(i) ==> #[trigger] (i >> j) & 1u8 == 0u8,
    decreases i,
{
    assert(i >> 0 == i) by (bit_vector);
    assert(i << 0 == i) by (bit_vector);
    assert(i & 0 == 0) by (bit_vector);
    assert(i / 2 == (i >> 1u8)) by (bit_vector);
    assert((i & 1) == 0 ==> i != 1) by (bit_vector);
    let x = u8_trailing_zeros(i / 2) as u8;
    assert(x < 8 ==> (i >> 1) >> x == (i >> add(x, 1))) by (bit_vector);
    assert(i << 8 == 0) by (bit_vector);
    assert(i & 1 != 0 ==> i & 1 == 1) by (bit_vector);
    assert((i & 1) == 0 ==> (i >> 1) << sub(8, x) == 0 ==> i << sub(8, add(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u8_trailing_zeros(i / 2);
    }
    assert forall|j: u8| 0 <= j < u8_trailing_zeros(i) implies #[trigger] (i >> j) & 1u8 == 0u8 by {
        let y = u8_trailing_zeros(i) as u8;
        assert(y <= 8 ==> i << sub(8, y) == 0 && 0 <= j < y ==> (i >> j) & 1u8 == 0u8)
            by (bit_vector);
    }
}

pub broadcast proof fn axiom_u8_trailing_ones(i: u8)
    ensures
        0 <= #[trigger] u8_trailing_ones(i) <= 8,
        i == 0xffu8 <==> u8_trailing_ones(i) == 8,
        // i^th bit is 0
        0 <= u8_trailing_ones(i) < 8 ==> (i >> u8_trailing_ones(i) as u8) & 1u8 == 0u8,
        // trailing bits are 1
        (!i) << sub(8, u8_trailing_ones(i) as u8) == 0,
        forall|j: u8| 0 <= j < u8_trailing_ones(i) ==> #[trigger] (i >> j) & 1u8 == 1u8,
{
    axiom_u8_trailing_zeros(!i);
    assert(!0xffu8 == 0) by (bit_vector);
    assert(!i == 0 ==> i == 0xffu8) by (bit_vector);
    let x = u8_trailing_ones(i) as u8;
    assert(((!i) >> x) & 1u8 == 1u8 ==> (i >> x) & 1u8 == 0u8) by (bit_vector);
    assert forall|j: u8| 0 <= j < u8_trailing_ones(i) implies #[trigger] (i >> j) & 1u8 == 1u8 by {
        let y = u8_trailing_ones(i) as u8;
        assert(y <= 8 ==> (!i) << sub(8, y) == 0 && 0 <= j < y ==> (i >> j) & 1u8 == 1u8)
            by (bit_vector);
    }
}

pub broadcast proof fn axiom_u8_leading_zeros(i: u8)
    ensures
        0 <= #[trigger] u8_leading_zeros(i) <= 8,
        i == 0 <==> u8_leading_zeros(i) == 8,
        // i^th bit from the left is 1
        0 <= u8_leading_zeros(i) < 8 ==> (i >> sub(7u8, u8_leading_zeros(i) as u8)) & 1u8 != 0u8,
        // leading bits are 0
        i >> sub(8, u8_leading_zeros(i) as u8) == 0,
        forall|j: u8| 8 - u8_leading_zeros(i) <= j < 8 ==> #[trigger] (i >> j) & 1u8 == 0u8,
    decreases i,
{
    assert(i / 2 == (i >> 1u8)) by (bit_vector);
    assert(((i >> 1) >> sub(7u8, 0)) & 1u8 == 0u8) by (bit_vector);
    let x = u8_leading_zeros(i / 2) as u8;
    assert(i >> 0 == i) by (bit_vector);
    assert(1u8 & 1u8 == 1u8) by (bit_vector);
    assert(0 < x < 8 ==> ((i >> 1) >> sub(7u8, x)) == (i >> sub(7u8, sub(x, 1)))) by (bit_vector);
    assert(0 < x <= 8 ==> (i >> 1) >> sub(8, x) == 0 ==> i >> sub(8, sub(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u8_leading_zeros(i / 2);
    }
    assert forall|j: u8| 8 - u8_leading_zeros(i) <= j < 8 implies #[trigger] (i >> j) & 1u8
        == 0u8 by {
        let y = u8_leading_zeros(i) as u8;
        assert(y <= 8 ==> i >> sub(8, y) == 0 ==> sub(8, y) <= j < 8 ==> (i >> j) & 1u8 == 0u8)
            by (bit_vector);
    }
}

pub broadcast proof fn axiom_u8_leading_ones(i: u8)
    ensures
        0 <= #[trigger] u8_leading_ones(i) <= 8,
        i == 0xffu8 <==> u8_leading_ones(i) == 8,
        // i^th bit from the left is 0
        0 <= u8_leading_ones(i) < 8 ==> (i >> sub(7u8, u8_leading_ones(i) as u8)) & 1u8 == 0u8,
        (!i) >> sub(8, u8_leading_ones(i) as u8) == 0,
        forall|j: u8| 8 - u8_leading_ones(i) <= j < 8 ==> #[trigger] (i >> j) & 1u8 == 1u8,
{
    axiom_u8_leading_zeros(!i);
    assert(!0xffu8 == 0) by (bit_vector);
    assert(!i == 0 ==> i == 0xffu8) by (bit_vector);
    let x = u8_leading_ones(i) as u8;
    assert(((!i) >> sub(7u8, x)) & 1u8 != 0u8 ==> (i >> sub(7u8, x)) & 1u8 == 0u8) by (bit_vector);
    assert forall|j: u8| 8 - u8_leading_ones(i) <= j < 8 implies #[trigger] (i >> j) & 1u8
        == 1u8 by {
        let y = u8_leading_ones(i) as u8;
        assert(y <= 8 ==> (!i) >> sub(8, y) == 0 ==> sub(8, y) <= j < 8 ==> (i >> j) & 1u8 == 1u8)
            by (bit_vector);
    }
}

/// Equivalent to `i.reverse_bits()`.
/// See [`axiom_u8_reverse_bits`] for useful properties.
pub uninterp spec fn u8_reverse_bits(i: u8) -> u8;

#[verifier::when_used_as_spec(u8_reverse_bits)]
pub assume_specification[ u8::reverse_bits ](i: u8) -> (r: u8)
    ensures
        r == u8_reverse_bits(i),
    opens_invariants none
    no_unwind
;

pub broadcast axiom fn axiom_u8_reverse_bits(i: u8)
    ensures
        u8_reverse_bits(#[trigger] u8_reverse_bits(i)) == i,
        // bit j of the result is bit 7 - j of i
        forall|j: u8|
            j < 8 ==> #[trigger] (u8_reverse_bits(i) >> j) & 1u8 == (i >> sub(7u8, j)) & 1u8,
;

///////////////////////////
/////////////////////////// For u16
/// Equivalent to `i.trailing_zeros()`.
/// See [`axiom_u16_trailing_zeros`] for useful properties.
pub closed spec fn u16_trailing_zeros(i: u16) -> u32
    decreases i,
{
    if i == 0 {
        16
    } else if (i & 1) != 0 {
        0
    } else {
        (1 + u16_trailing_zeros(i / 2)) as u32
    }
}

/// Equivalent to `i.leading_zeros()`.
/// See [`axiom_u16_leading_zeros`] for useful properties.
pub closed spec fn u16_leading_zeros(i: u16) -> u32
    decreases i,
{
    if i == 0 {
        16
    } else {
        (u16_leading_zeros(i / 2) - 1) as u32
    }
}

/// Equivalent to `i.trailing_ones()`.
/// See [`axiom_u16_trailing_ones`] for useful properties.
pub open spec fn u16_trailing_ones(i: u16) -> u32 {
    u16_trailing_zeros(!i)
}

/// Equivalent to `i.leading_ones()`.
/// See [`axiom_u16_leading_ones`] for useful properties.
pub open spec fn u16_leading_ones(i: u16) -> u32 {
    u16_leading_zeros(!i)
}

#[verifier::when_used_as_spec(u16_trailing_zeros)]
pub assume_specification[ u16::trailing_zeros ](i: u16) -> (r: u32)
    ensures
        r == u16_trailing_zeros(i),
;

#[verifier::when_used_as_spec(u16_trailing_ones)]
pub assume_specification[ u16::trailing_ones ](i: u16) -> (r: u32)
    ensures
        r == u16_trailing_ones(i),
;

#[verifier::when_used_as_spec(u16_leading_zeros)]
pub assume_specification[ u16::leading_zeros ](i: u16) -> (r: u32)
    ensures
        r == u16_leading_zeros(i),
;

#[verifier::when_used_as_spec(u16_leading_ones)]
pub assume_specification[ u16::leading_ones ](i: u16) -> (r: u32)
    ensures
        r == u16_leading_ones(i),
;

pub broadcast proof fn axiom_u16_trailing_zeros(i: u16)
    ensures
        0 <= #[trigger] u16_trailing_zeros(i) <= 16,
        i == 0 <==> u16_trailing_zeros(i) == 16,
        // i^th bit is 1
        0 <= u16_trailing_zeros(i) < 16 ==> (i >> u16_trailing_zeros(i) as u16) & 1u16 == 1u16,
        // trailing bits are 0
        i << sub(16, u16_trailing_zeros(i) as u16) == 0,
        forall|j: u16| 0 <= j < u16_trailing_zeros(i) ==> #[trigger] (i >> j) & 1u16 == 0u16,
    decreases i,
{
    assert(i >> 0 == i) by (bit_vector);
    assert(i << 0 == i) by (bit_vector);
    assert(i & 0 == 0) by (bit_vector);
    assert(i / 2 == (i >> 1u16)) by (bit_vector);
    assert((i & 1) == 0 ==> i != 1) by (bit_vector);
    let x = u16_trailing_zeros(i / 2) as u16;
    assert(x < 16 ==> (i >> 1) >> x == (i >> add(x, 1))) by (bit_vector);
    assert(i << 16 == 0) by (bit_vector);
    assert(i & 1 != 0 ==> i & 1 == 1) by (bit_vector);
    assert((i & 1) == 0 ==> (i >> 1) << sub(16, x) == 0 ==> i << sub(16, add(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u16_trailing_zeros(i / 2);
    }
    assert forall|j: u16| 0 <= j < u16_trailing_zeros(i) implies #[trigger] (i >> j) & 1u16
        == 0u16 by {
        let y = u16_trailing_zeros(i) as u16;
        assert(y <= 16 ==> i << sub(16, y) == 0 && 0 <= j < y ==> (i >> j) & 1u16 == 0u16)
            by (bit_vector);
    }
}

pub broadcast proof fn axiom_u16_trailing_ones(i: u16)
    ensures
        0 <= #[trigger] u16_trailing_ones(i) <= 16,
        i == 0xffffu16 <==> u16_trailing_ones(i) == 16,
        // i^th bit is 0
        0 <= u16_trailing_ones(i) < 16 ==> (i >> u16_trailing_ones(i) as u16) & 1u16 == 0u16,
        // trailing bits are 1
        (!i) << sub(16, u16_trailing_ones(i) as u16) == 0,
        forall|j: u16| 0 <= j < u16_trailing_ones(i) ==> #[trigger] (i >> j) & 1u16 == 1u16,
{
    axiom_u16_trailing_zeros(!i);
    assert(!0xffffu16 == 0) by (bit_vector);
    assert(!i == 0 ==> i == 0xffffu16) by (bit_vector);
    let x = u16_trailing_ones(i) as u16;
    assert(((!i) >> x) & 1u16 == 1u16 ==> (i >> x) & 1u16 == 0u16) by (bit_vector);
    assert forall|j: u16| 0 <= j < u16_trailing_ones(i) implies #[trigger] (i >> j) & 1u16
        == 1u16 by {
        let y = u16_trailing_ones(i) as u16;
        assert(y <= 16 ==> (!i) << sub(16, y) == 0 && 0 <= j < y ==> (i >> j) & 1u16 == 1u16)
            by (bit_vector);
    }
}

pub broadcast proof fn axiom_u16_leading_zeros(i: u16)
    ensures
        0 <= #[trigger] u16_leading_zeros(i) <= 16,
        i == 0 <==> u16_leading_zeros(i) == 16,
        // i^th bit from the left is 1
        0 <= u16_leading_zeros(i) < 16 ==> (i >> sub(15u16, u16_leading_zeros(i) as u16)) & 1u16
            != 0u16,
        // leading bits are 0
        i >> sub(16, u16_leading_zeros(i) as u16) == 0,
        forall|j: u16| 16 - u16_leading_zeros(i) <= j < 16 ==> #[trigger] (i >> j) & 1u16 == 0u16,
    decreases i,
{
    assert(i / 2 == (i >> 1u16)) by (bit_vector);
    assert(((i >> 1) >> sub(15u16, 0)) & 1u16 == 0u16) by (bit_vector);
    let x = u16_leading_zeros(i / 2) as u16;
    assert(i >> 0 == i) by (bit_vector);
    assert(1u16 & 1u16 == 1u16) by (bit_vector);
    assert(0 < x < 16 ==> ((i >> 1) >> sub(15u16, x)) == (i >> sub(15u16, sub(x, 1))))
        by (bit_vector);
    assert(0 < x <= 16 ==> (i >> 1) >> sub(16, x) == 0 ==> i >> sub(16, sub(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u16_leading_zeros(i / 2);
    }
    assert forall|j: u16| 16 - u16_leading_zeros(i) <= j < 16 implies #[trigger] (i >> j) & 1u16
        == 0u16 by {
        let y = u16_leading_zeros(i) as u16;
        assert(y <= 16 ==> i >> sub(16, y) == 0 ==> sub(16, y) <= j < 16 ==> (i >> j) & 1u16
            == 0u16) by (bit_vector);
    }
}

pub broadcast proof fn axiom_u16_leading_ones(i: u16)
    ensures
        0 <= #[trigger] u16_leading_ones(i) <= 16,
        i == 0xffffu16 <==> u16_leading_ones(i) == 16,
        // i^th bit from the left is 0
        0 <= u16_leading_ones(i) < 16 ==> (i >> sub(15u16, u16_leading_ones(i) as u16)) & 1u16
            == 0u16,
        (!i) >> sub(16, u16_leading_ones(i) as u16) == 0,
        forall|j: u16| 16 - u16_leading_ones(i) <= j < 16 ==> #[trigger] (i >> j) & 1u16 == 1u16,
{
    axiom_u16_leading_zeros(!i);
    assert(!0xffffu16 == 0) by (bit_vector);
    assert(!i == 0 ==> i == 0xffffu16) by (bit_vector);
    let x = u16_leading_ones(i) as u16;
    assert(((!i) >> sub(15u16, x)) & 1u16 != 0u16 ==> (i >> sub(15u16, x)) & 1u16 == 0u16)
        by (bit_vector);
    assert forall|j: u16| 16 - u16_leading_ones(i) <= j < 16 implies #[trigger] (i >> j) & 1u16
        == 1u16 by {
        let y = u16_leading_ones(i) as u16;
        assert(y <= 16 ==> (!i) >> sub(16, y) == 0 ==> sub(16, y) <= j < 16 ==> (i >> j) & 1u16
            == 1u16) by (bit_vector);
    }
}

/// Equivalent to `i.reverse_bits()`.
/// See [`axiom_u16_reverse_bits`] for useful properties.
pub uninterp spec fn u16_reverse_bits(i: u16) -> u16;

#[verifier::when_used_as_spec(u16_reverse_bits)]
pub assume_specification[ u16::reverse_bits ](i: u16) -> (r: u16)
    ensures
        r == u16_reverse_bits(i),
    opens_invariants none
    no_unwind
;

pub broadcast axiom fn axiom_u16_reverse_bits(i: u16)
    ensures
        u16_reverse_bits(#[trigger] u16_reverse_bits(i)) == i,
        // bit j of the result is bit 15 - j of i
        forall|j: u16|
            j < 16 ==> #[trigger] (u16_reverse_bits(i) >> j) & 1u16 == (i >> sub(15u16, j)) & 1u16,
;

///////////////////////////
/////////////////////////// For u32
/// Equivalent to `i.trailing_zeros()`.
/// See [`axiom_u32_trailing_zeros`] for useful properties.
pub closed spec fn u32_trailing_zeros(i: u32) -> u32
    decreases i,
{
    if i == 0 {
        32
    } else if (i & 1) != 0 {
        0
    } else {
        (1 + u32_trailing_zeros(i / 2)) as u32
    }
}

/// Equivalent to `i.leading_zeros()`.
/// See [`axiom_u32_leading_zeros`] for useful properties.
pub closed spec fn u32_leading_zeros(i: u32) -> u32
    decreases i,
{
    if i == 0 {
        32
    } else {
        (u32_leading_zeros(i / 2) - 1) as u32
    }
}

/// Equivalent to `i.trailing_ones()`.
/// See [`axiom_u32_trailing_ones`] for useful properties.
pub open spec fn u32_trailing_ones(i: u32) -> u32 {
    u32_trailing_zeros(!i)
}

/// Equivalent to `i.leading_ones()`.
/// See [`axiom_u32_leading_ones`] for useful properties.
pub open spec fn u32_leading_ones(i: u32) -> u32 {
    u32_leading_zeros(!i)
}

#[verifier::when_used_as_spec(u32_trailing_zeros)]
pub assume_specification[ u32::trailing_zeros ](i: u32) -> (r: u32)
    ensures
        r == u32_trailing_zeros(i),
;

#[verifier::when_used_as_spec(u32_trailing_ones)]
pub assume_specification[ u32::trailing_ones ](i: u32) -> (r: u32)
    ensures
        r == u32_trailing_ones(i),
;

#[verifier::when_used_as_spec(u32_leading_zeros)]
pub assume_specification[ u32::leading_zeros ](i: u32) -> (r: u32)
    ensures
        r == u32_leading_zeros(i),
;

#[verifier::when_used_as_spec(u32_leading_ones)]
pub assume_specification[ u32::leading_ones ](i: u32) -> (r: u32)
    ensures
        r == u32_leading_ones(i),
;

pub broadcast proof fn axiom_u32_trailing_zeros(i: u32)
    ensures
        0 <= #[trigger] u32_trailing_zeros(i) <= 32,
        i == 0 <==> u32_trailing_zeros(i) == 32,
        // i^th bit is 1
        0 <= u32_trailing_zeros(i) < 32 ==> (i >> u32_trailing_zeros(i) as u32) & 1u32 == 1u32,
        // trailing bits are 0
        i << sub(32, u32_trailing_zeros(i) as u32) == 0,
        forall|j: u32| 0 <= j < u32_trailing_zeros(i) ==> #[trigger] (i >> j) & 1u32 == 0u32,
    decreases i,
{
    assert(i >> 0 == i) by (bit_vector);
    assert(i << 0 == i) by (bit_vector);
    assert(i & 0 == 0) by (bit_vector);
    assert(i / 2 == (i >> 1u32)) by (bit_vector);
    assert((i & 1) == 0 ==> i != 1) by (bit_vector);
    let x = u32_trailing_zeros(i / 2) as u32;
    assert(x < 32 ==> (i >> 1) >> x == (i >> add(x, 1))) by (bit_vector);
    assert(i << 32 == 0) by (bit_vector);
    assert(i & 1 != 0 ==> i & 1 == 1) by (bit_vector);
    assert((i & 1) == 0 ==> (i >> 1) << sub(32, x) == 0 ==> i << sub(32, add(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u32_trailing_zeros(i / 2);
    }
    assert forall|j: u32| 0 <= j < u32_trailing_zeros(i) implies #[trigger] (i >> j) & 1u32
        == 0u32 by {
        let y = u32_trailing_zeros(i) as u32;
        assert(y <= 32 ==> i << sub(32, y) == 0 && 0 <= j < y ==> (i >> j) & 1u32 == 0u32)
            by (bit_vector);
    }
}

pub broadcast proof fn axiom_u32_trailing_ones(i: u32)
    ensures
        0 <= #[trigger] u32_trailing_ones(i) <= 32,
        i == 0xffff_ffffu32 <==> u32_trailing_ones(i) == 32,
        // i^th bit is 0
        0 <= u32_trailing_ones(i) < 32 ==> (i >> u32_trailing_ones(i) as u32) & 1u32 == 0u32,
        // trailing bits are 1
        (!i) << sub(32, u32_trailing_ones(i) as u32) == 0,
        forall|j: u32| 0 <= j < u32_trailing_ones(i) ==> #[trigger] (i >> j) & 1u32 == 1u32,
{
    axiom_u32_trailing_zeros(!i);
    assert(!0xffff_ffffu32 == 0) by (bit_vector);
    assert(!i == 0 ==> i == 0xffff_ffffu32) by (bit_vector);
    let x = u32_trailing_ones(i) as u32;
    assert(((!i) >> x) & 1u32 == 1u32 ==> (i >> x) & 1u32 == 0u32) by (bit_vector);
    assert forall|j: u32| 0 <= j < u32_trailing_ones(i) implies #[trigger] (i >> j) & 1u32
        == 1u32 by {
        let y = u32_trailing_ones(i) as u32;
        assert(y <= 32 ==> (!i) << sub(32, y) == 0 && 0 <= j < y ==> (i >> j) & 1u32 == 1u32)
            by (bit_vector);
    }
}

pub broadcast proof fn axiom_u32_leading_zeros(i: u32)
    ensures
        0 <= #[trigger] u32_leading_zeros(i) <= 32,
        i == 0 <==> u32_leading_zeros(i) == 32,
        // i^th bit from the left is 1
        0 <= u32_leading_zeros(i) < 32 ==> (i >> sub(31u32, u32_leading_zeros(i) as u32)) & 1u32
            != 0u32,
        // leading bits are 0
        i >> sub(32, u32_leading_zeros(i) as u32) == 0,
        forall|j: u32| 32 - u32_leading_zeros(i) <= j < 32 ==> #[trigger] (i >> j) & 1u32 == 0u32,
    decreases i,
{
    assert(i / 2 == (i >> 1u32)) by (bit_vector);
    assert(((i >> 1) >> sub(31u32, 0)) & 1u32 == 0u32) by (bit_vector);
    let x = u32_leading_zeros(i / 2) as u32;
    assert(i >> 0 == i) by (bit_vector);
    assert(1u32 & 1u32 == 1u32) by (bit_vector);
    assert(0 < x < 32 ==> ((i >> 1) >> sub(31u32, x)) == (i >> sub(31u32, sub(x, 1))))
        by (bit_vector);
    assert(0 < x <= 32 ==> (i >> 1) >> sub(32, x) == 0 ==> i >> sub(32, sub(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u32_leading_zeros(i / 2);
    }
    assert forall|j: u32| 32 - u32_leading_zeros(i) <= j < 32 implies #[trigger] (i >> j) & 1u32
        == 0u32 by {
        let y = u32_leading_zeros(i) as u32;
        assert(y <= 32 ==> i >> sub(32, y) == 0 ==> sub(32, y) <= j < 32 ==> (i >> j) & 1u32
            == 0u32) by (bit_vector);
    }
}

pub broadcast proof fn axiom_u32_leading_ones(i: u32)
    ensures
        0 <= #[trigger] u32_leading_ones(i) <= 32,
        i == 0xffff_ffffu32 <==> u32_leading_ones(i) == 32,
        // i^th bit from the left is 0
        0 <= u32_leading_ones(i) < 32 ==> (i >> sub(31u32, u32_leading_ones(i) as u32)) & 1u32
            == 0u32,
        (!i) >> sub(32, u32_leading_ones(i) as u32) == 0,
        forall|j: u32| 32 - u32_leading_ones(i) <= j < 32 ==> #[trigger] (i >> j) & 1u32 == 1u32,
{
    axiom_u32_leading_zeros(!i);
    assert(!0xffff_ffffu32 == 0) by (bit_vector);
    assert(!i == 0 ==> i == 0xffff_ffffu32) by (bit_vector);
    let x = u32_leading_ones(i) as u32;
    assert(((!i) >> sub(31u32, x)) & 1u32 != 0u32 ==> (i >> sub(31u32, x)) & 1u32 == 0u32)
        by (bit_vector);
    assert forall|j: u32| 32 - u32_leading_ones(i) <= j < 32 implies #[trigger] (i >> j) & 1u32
        == 1u32 by {
        let y = u32_leading_ones(i) as u32;
        assert(y <= 32 ==> (!i) >> sub(32, y) == 0 ==> sub(32, y) <= j < 32 ==> (i >> j) & 1u32
            == 1u32) by (bit_vector);
    }
}

/// Equivalent to `i.reverse_bits()`.
/// See [`axiom_u32_reverse_bits`] for useful properties.
pub uninterp spec fn u32_reverse_bits(i: u32) -> u32;

#[verifier::when_used_as_spec(u32_reverse_bits)]
pub assume_specification[ u32::reverse_bits ](i: u32) -> (r: u32)
    ensures
        r == u32_reverse_bits(i),
    opens_invariants none
    no_unwind
;

pub broadcast axiom fn axiom_u32_reverse_bits(i: u32)
    ensures
        u32_reverse_bits(#[trigger] u32_reverse_bits(i)) == i,
        // bit j of the result is bit 31 - j of i
        forall|j: u32|
            j < 32 ==> #[trigger] (u32_reverse_bits(i) >> j) & 1u32 == (i >> sub(31u32, j)) & 1u32,
;

///////////////////////////
/////////////////////////// For u64
/// Equivalent to `i.trailing_zeros()`.
/// See [`axiom_u64_trailing_zeros`] for useful properties.
pub closed spec fn u64_trailing_zeros(i: u64) -> u32
    decreases i,
{
    if i == 0 {
        64
    } else if (i & 1) != 0 {
        0
    } else {
        (1 + u64_trailing_zeros(i / 2)) as u32
    }
}

/// Equivalent to `i.leading_zeros()`.
/// See [`axiom_u64_leading_zeros`] for useful properties.
#[verifier::opaque]
pub open spec fn u64_leading_zeros(i: u64) -> int
    decreases i,
{
    if i == 0 {
        64
    } else {
        u64_leading_zeros(i / 2) - 1
    }
}

/// Equivalent to `i.trailing_ones()`.
/// See [`axiom_u64_trailing_ones`] for useful properties.
pub open spec fn u64_trailing_ones(i: u64) -> u32 {
    u64_trailing_zeros(!i) as u32
}

/// Equivalent to `i.leading_ones()`.
/// See [`axiom_u64_leading_ones`] for useful properties.
pub open spec fn u64_leading_ones(i: u64) -> u32 {
    u64_leading_zeros(!i) as u32
}

#[verifier::when_used_as_spec(u64_trailing_zeros)]
pub assume_specification[ u64::trailing_zeros ](i: u64) -> (r: u32)
    ensures
        r == u64_trailing_zeros(i),
;

#[verifier::when_used_as_spec(u64_trailing_ones)]
pub assume_specification[ u64::trailing_ones ](i: u64) -> (r: u32)
    ensures
        r == u64_trailing_ones(i),
;

//#[verifier::when_used_as_spec(u64_leading_zeros)]
pub assume_specification[ u64::leading_zeros ](i: u64) -> (r: u32)
    ensures
        r as int == u64_leading_zeros(i),
;

#[verifier::when_used_as_spec(u64_leading_ones)]
pub assume_specification[ u64::leading_ones ](i: u64) -> (r: u32)
    ensures
        r == u64_leading_ones(i),
;

pub broadcast proof fn axiom_u64_trailing_zeros(i: u64)
    ensures
        0 <= #[trigger] u64_trailing_zeros(i) <= 64,
        i == 0 <==> u64_trailing_zeros(i) == 64,
        // i^th bit is 1
        0 <= u64_trailing_zeros(i) < 64 ==> (i >> u64_trailing_zeros(i) as u64) & 1u64 == 1u64,
        // trailing bits are 0
        i << sub(64, u64_trailing_zeros(i) as u64) == 0,
        forall|j: u64| 0 <= j < u64_trailing_zeros(i) ==> #[trigger] (i >> j) & 1u64 == 0u64,
    decreases i,
{
    assert(i >> 0 == i) by (bit_vector);
    assert(i << 0 == i) by (bit_vector);
    assert(i & 0 == 0) by (bit_vector);
    assert(i / 2 == (i >> 1u64)) by (bit_vector);
    assert((i & 1) == 0 ==> i != 1) by (bit_vector);
    let x = u64_trailing_zeros(i / 2) as u64;
    assert(x < 64 ==> (i >> 1) >> x == (i >> add(x, 1))) by (bit_vector);
    assert(i << 64 == 0) by (bit_vector);
    assert(i & 1 != 0 ==> i & 1 == 1) by (bit_vector);
    assert((i & 1) == 0 ==> (i >> 1) << sub(64, x) == 0 ==> i << sub(64, add(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u64_trailing_zeros(i / 2);
    }
    assert forall|j: u64| 0 <= j < u64_trailing_zeros(i) implies #[trigger] (i >> j) & 1u64
        == 0u64 by {
        let y = u64_trailing_zeros(i) as u64;
        assert(y <= 64 ==> i << sub(64, y) == 0 && 0 <= j < y ==> (i >> j) & 1u64 == 0u64)
            by (bit_vector);
    }
}

pub broadcast proof fn axiom_u64_trailing_ones(i: u64)
    ensures
        0 <= #[trigger] u64_trailing_ones(i) <= 64,
        i == 0xffff_ffff_ffff_ffffu64 <==> u64_trailing_ones(i) == 64,
        // i^th bit is 0
        0 <= u64_trailing_ones(i) < 64 ==> (i >> u64_trailing_ones(i) as u64) & 1u64 == 0u64,
        // trailing bits are 1
        (!i) << sub(64, u64_trailing_ones(i) as u64) == 0,
        forall|j: u64| 0 <= j < u64_trailing_ones(i) ==> #[trigger] (i >> j) & 1u64 == 1u64,
{
    axiom_u64_trailing_zeros(!i);
    assert(!0xffff_ffff_ffff_ffffu64 == 0) by (bit_vector);
    assert(!i == 0 ==> i == 0xffff_ffff_ffff_ffffu64) by (bit_vector);
    let x = u64_trailing_ones(i) as u64;
    assert(((!i) >> x) & 1u64 == 1u64 ==> (i >> x) & 1u64 == 0u64) by (bit_vector);
    assert forall|j: u64| 0 <= j < u64_trailing_ones(i) implies #[trigger] (i >> j) & 1u64
        == 1u64 by {
        let y = u64_trailing_ones(i) as u64;
        assert(y <= 64 ==> (!i) << sub(64, y) == 0 && 0 <= j < y ==> (i >> j) & 1u64 == 1u64)
            by (bit_vector);
    }
}

pub broadcast proof fn axiom_u64_leading_zeros(i: u64)
    ensures
        0 <= #[trigger] u64_leading_zeros(i) <= 64,
        i == 0 <==> u64_leading_zeros(i) == 64,
        // i^th bit from the left is 1
        0 <= u64_leading_zeros(i) < 64 ==> (i >> sub(63u64, u64_leading_zeros(i) as u64)) & 1u64
            != 0u64,
        // leading bits are 0
        i >> sub(64, u64_leading_zeros(i) as u64) == 0,
        forall|j: u64| 64 - u64_leading_zeros(i) <= j < 64 ==> #[trigger] (i >> j) & 1u64 == 0u64,
    decreases i,
{
    reveal(u64_leading_zeros);
    assert(i / 2 == (i >> 1u64)) by (bit_vector);
    assert(((i >> 1) >> sub(63u64, 0)) & 1u64 == 0u64) by (bit_vector);
    let x = u64_leading_zeros(i / 2) as u64;
    assert(i >> 0 == i) by (bit_vector);
    assert(1u64 & 1u64 == 1u64) by (bit_vector);
    assert(0 < x < 64 ==> ((i >> 1) >> sub(63u64, x)) == (i >> sub(63u64, sub(x, 1))))
        by (bit_vector);
    assert(0 < x <= 64 ==> (i >> 1) >> sub(64, x) == 0 ==> i >> sub(64, sub(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u64_leading_zeros(i / 2);
    }
    assert forall|j: u64| 64 - u64_leading_zeros(i) <= j < 64 implies #[trigger] (i >> j) & 1u64
        == 0u64 by {
        let y = u64_leading_zeros(i) as u64;
        assert(y <= 64 ==> i >> sub(64, y) == 0 ==> sub(64, y) <= j < 64 ==> (i >> j) & 1u64
            == 0u64) by (bit_vector);
    }
}

pub broadcast proof fn axiom_u64_leading_ones(i: u64)
    ensures
        0 <= #[trigger] u64_leading_ones(i) <= 64,
        i == 0xffff_ffff_ffff_ffffu64 <==> u64_leading_ones(i) == 64,
        // i^th bit from the left is 0
        0 <= u64_leading_ones(i) < 64 ==> (i >> sub(63u64, u64_leading_ones(i) as u64)) & 1u64
            == 0u64,
        (!i) >> sub(64, u64_leading_ones(i) as u64) == 0,
        forall|j: u64| 64 - u64_leading_ones(i) <= j < 64 ==> #[trigger] (i >> j) & 1u64 == 1u64,
{
    axiom_u64_leading_zeros(!i);
    assert(!0xffff_ffff_ffff_ffffu64 == 0) by (bit_vector);
    assert(!i == 0 ==> i == 0xffff_ffff_ffff_ffffu64) by (bit_vector);
    let x = u64_leading_ones(i) as u64;
    assert(((!i) >> sub(63u64, x)) & 1u64 != 0u64 ==> (i >> sub(63u64, x)) & 1u64 == 0u64)
        by (bit_vector);
    assert forall|j: u64| 64 - u64_leading_ones(i) <= j < 64 implies #[trigger] (i >> j) & 1u64
        == 1u64 by {
        let y = u64_leading_ones(i) as u64;
        assert(y <= 64 ==> (!i) >> sub(64, y) == 0 ==> sub(64, y) <= j < 64 ==> (i >> j) & 1u64
            == 1u64) by (bit_vector);
    }
}

/// Equivalent to `i.reverse_bits()`.
/// See [`axiom_u64_reverse_bits`] for useful properties.
pub uninterp spec fn u64_reverse_bits(i: u64) -> u64;

#[verifier::when_used_as_spec(u64_reverse_bits)]
pub assume_specification[ u64::reverse_bits ](i: u64) -> (r: u64)
    ensures
        r == u64_reverse_bits(i),
    opens_invariants none
    no_unwind
;

pub broadcast axiom fn axiom_u64_reverse_bits(i: u64)
    ensures
        u64_reverse_bits(#[trigger] u64_reverse_bits(i)) == i,
        // bit j of the result is bit 63 - j of i
        forall|j: u64|
            j < 64 ==> #[trigger] (u64_reverse_bits(i) >> j) & 1u64 == (i >> sub(63u64, j)) & 1u64,
;

///////////////////////////
/////////////////////////// For u128
/// Equivalent to `i.trailing_zeros()`.
/// See [`axiom_u128_trailing_zeros`] for useful properties.
pub closed spec fn u128_trailing_zeros(i: u128) -> u32
    decreases i,
{
    if i == 0 {
        128
    } else if (i & 1) != 0 {
        0
    } else {
        (1 + u128_trailing_zeros(i / 2)) as u32
    }
}

/// Equivalent to `i.leading_zeros()`.
/// See [`axiom_u128_leading_zeros`] for useful properties.
pub closed spec fn u128_leading_zeros(i: u128) -> u32
    decreases i,
{
    if i == 0 {
        128
    } else {
        (u128_leading_zeros(i / 2) - 1) as u32
    }
}

#[verifier::when_used_as_spec(u128_trailing_zeros)]
pub assume_specification[ u128::trailing_zeros ](i: u128) -> (r: u32)
    ensures
        r == u128_trailing_zeros(i),
;

#[verifier::when_used_as_spec(u128_leading_zeros)]
pub assume_specification[ u128::leading_zeros ](i: u128) -> (r: u32)
    ensures
        r == u128_leading_zeros(i),
;

pub broadcast proof fn axiom_u128_trailing_zeros(i: u128)
    ensures
        0 <= #[trigger] u128_trailing_zeros(i) <= 128,
        i == 0 <==> u128_trailing_zeros(i) == 128,
        // i^th bit is 1
        0 <= u128_trailing_zeros(i) < 128 ==> (i >> u128_trailing_zeros(i) as u128) & 1u128
            == 1u128,
        // trailing bits are 0
        i << sub(128, u128_trailing_zeros(i) as u128) == 0,
        forall|j: u128| 0 <= j < u128_trailing_zeros(i) ==> #[trigger] (i >> j) & 1u128 == 0u128,
    decreases i,
{
    assert(i >> 0 == i) by (bit_vector);
    assert(i << 0 == i) by (bit_vector);
    assert(i & 0 == 0) by (bit_vector);
    assert(i / 2 == (i >> 1u128)) by (bit_vector);
    assert((i & 1) == 0 ==> i != 1) by (bit_vector);
    let x = u128_trailing_zeros(i / 2) as u128;
    assert(x < 128 ==> (i >> 1) >> x == (i >> add(x, 1))) by (bit_vector);
    assert(i << 128 == 0) by (bit_vector);
    assert(i & 1 != 0 ==> i & 1 == 1) by (bit_vector);
    assert((i & 1) == 0 ==> (i >> 1) << sub(128, x) == 0 ==> i << sub(128, add(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u128_trailing_zeros(i / 2);
    }
    assert forall|j: u128| 0 <= j < u128_trailing_zeros(i) implies #[trigger] (i >> j) & 1u128
        == 0u128 by {
        let y = u128_trailing_zeros(i) as u128;
        assert(y <= 128 ==> i << sub(128, y) == 0 && 0 <= j < y ==> (i >> j) & 1u128 == 0u128)
            by (bit_vector);
    }
}

pub broadcast proof fn axiom_u128_leading_zeros(i: u128)
    ensures
        0 <= #[trigger] u128_leading_zeros(i) <= 128,
        i == 0 <==> u128_leading_zeros(i) == 128,
        // i^th bit from the left is 1
        0 <= u128_leading_zeros(i) < 128 ==> (i >> sub(127u128, u128_leading_zeros(i) as u128))
            & 1u128 != 0u128,
        // leading bits are 0
        i >> sub(128, u128_leading_zeros(i) as u128) == 0,
        forall|j: u128|
            128 - u128_leading_zeros(i) <= j < 128 ==> #[trigger] (i >> j) & 1u128 == 0u128,
    decreases i,
{
    assert(i / 2 == (i >> 1u128)) by (bit_vector);
    assert(((i >> 1) >> sub(127u128, 0)) & 1u128 == 0u128) by (bit_vector);
    let x = u128_leading_zeros(i / 2) as u128;
    assert(i >> 0 == i) by (bit_vector);
    assert(1u128 & 1u128 == 1u128) by (bit_vector);
    assert(0 < x < 128 ==> ((i >> 1) >> sub(127u128, x)) == (i >> sub(127u128, sub(x, 1))))
        by (bit_vector);
    assert(0 < x <= 128 ==> (i >> 1) >> sub(128, x) == 0 ==> i >> sub(128, sub(x, 1)) == 0)
        by (bit_vector);
    if i != 0 {
        axiom_u128_leading_zeros(i / 2);
    }
    assert forall|j: u128| 128 - u128_leading_zeros(i) <= j < 128 implies #[trigger] (i >> j)
        & 1u128 == 0u128 by {
        let y = u128_leading_zeros(i) as u128;
        assert(y <= 128 ==> i >> sub(128, y) == 0 ==> sub(128, y) <= j < 128 ==> (i >> j) & 1u128
            == 0u128) by (bit_vector);
    }
}

///////////////////////////
/////////////////////////// For usize
/// Equivalent to `i.trailing_zeros()`.
/// See [`axiom_usize_trailing_zeros`] for useful properties.
pub closed spec fn usize_trailing_zeros(i: usize) -> u32
    decreases i,
{
    if i == 0 {
        usize::BITS
    } else if (i & 1) != 0 {
        0
    } else {
        (1 + usize_trailing_zeros(i / 2)) as u32
    }
}

/// Equivalent to `i.leading_zeros()`.
/// See [`axiom_usize_leading_zeros`] for useful properties.
pub closed spec fn usize_leading_zeros(i: usize) -> u32
    decreases i,
{
    if i == 0 {
        usize::BITS
    } else {
        (usize_leading_zeros(i / 2) - 1) as u32
    }
}

#[verifier::when_used_as_spec(usize_trailing_zeros)]
pub assume_specification[ usize::trailing_zeros ](i: usize) -> (r: u32)
    ensures
        r == usize_trailing_zeros(i),
;

#[verifier::when_used_as_spec(usize_leading_zeros)]
pub assume_specification[ usize::leading_zeros ](i: usize) -> (r: u32)
    ensures
        r == usize_leading_zeros(i),
;

pub broadcast proof fn axiom_usize_trailing_zeros(i: usize)
    ensures
        0 <= #[trigger] usize_trailing_zeros(i) <= usize::BITS,
        i == 0 <==> usize_trailing_zeros(i) == usize::BITS,
        // i^th bit is 1
        0 <= usize_trailing_zeros(i) < usize::BITS ==> (i >> usize_trailing_zeros(i) as usize)
            & 1usize == 1usize,
        // trailing bits are 0
        i << sub(usize::BITS as usize, usize_trailing_zeros(i) as usize) == 0,
        forall|j: usize|
            0 <= j < usize_trailing_zeros(i) ==> #[trigger] (i >> j) & 1usize == 0usize,
    decreases i,
{
    assert(i >> 0 == i) by (bit_vector);
    assert(i << 0 == i) by (bit_vector);
    assert(i & 0 == 0) by (bit_vector);
    assert(i / 2 == (i >> 1usize)) by (bit_vector);
    assert((i & 1) == 0 ==> i != 1) by (bit_vector);
    let x = usize_trailing_zeros(i / 2) as usize;
    assert(x < usize::BITS as usize ==> (i >> 1) >> x == (i >> add(x, 1))) by (bit_vector);
    assert(i << (usize::BITS as usize) == 0) by (bit_vector);
    assert(i & 1 != 0 ==> i & 1 == 1) by (bit_vector);
    assert((i & 1) == 0 ==> (i >> 1) << sub(usize::BITS as usize, x) == 0 ==> i << sub(
        usize::BITS as usize,
        add(x, 1),
    ) == 0) by (bit_vector);
    if i != 0 {
        axiom_usize_trailing_zeros(i / 2);
    }
    assert forall|j: usize| 0 <= j < usize_trailing_zeros(i) implies #[trigger] (i >> j) & 1usize
        == 0usize by {
        let y = usize_trailing_zeros(i) as usize;
        assert(y <= usize::BITS as usize ==> i << sub(usize::BITS as usize, y) == 0 && 0 <= j < y
            ==> (i >> j) & 1usize == 0usize) by (bit_vector);
    }
}

pub broadcast proof fn axiom_usize_leading_zeros(i: usize)
    ensures
        0 <= #[trigger] usize_leading_zeros(i) <= usize::BITS,
        i == 0 <==> usize_leading_zeros(i) == usize::BITS,
        // i^th bit from the left is 1
        0 <= usize_leading_zeros(i) < usize::BITS ==> (i >> sub(
            sub(usize::BITS as usize, 1),
            usize_leading_zeros(i) as usize,
        )) & 1usize != 0usize,
        // leading bits are 0
        i >> sub(usize::BITS as usize, usize_leading_zeros(i) as usize) == 0,
        forall|j: usize|
            usize::BITS - usize_leading_zeros(i) <= j < usize::BITS ==> #[trigger] (i >> j) & 1usize
                == 0usize,
    decreases i,
{
    assert(i / 2 == (i >> 1usize)) by (bit_vector);
    assert(((i >> 1) >> sub(sub(usize::BITS as usize, 1), 0)) & 1usize == 0usize) by (bit_vector);
    let x = usize_leading_zeros(i / 2) as usize;
    assert(i >> 0 == i) by (bit_vector);
    assert(1usize & 1usize == 1usize) by (bit_vector);
    assert(0 < x < usize::BITS as usize ==> ((i >> 1) >> sub(sub(usize::BITS as usize, 1), x)) == (i
        >> sub(sub(usize::BITS as usize, 1), sub(x, 1)))) by (bit_vector);
    assert(0 < x <= usize::BITS as usize ==> (i >> 1) >> sub(usize::BITS as usize, x) == 0 ==> i
        >> sub(usize::BITS as usize, sub(x, 1)) == 0) by (bit_vector);
    if i != 0 {
        axiom_usize_leading_zeros(i / 2);
    }
    assert forall|j: usize|
        usize::BITS - usize_leading_zeros(i) <= j < usize::BITS implies #[trigger] (i >> j) & 1usize
        == 0usize by {
        let y = usize_leading_zeros(i) as usize;
        assert(y <= usize::BITS as usize ==> i >> sub(usize::BITS as usize, y) == 0 ==> sub(
            usize::BITS as usize,
            y,
        ) <= j < usize::BITS as usize ==> (i >> j) & 1usize == 0usize) by (bit_vector);
    }
}

///////////////////////////
/////////////////////////// count_ones for all unsigned types
proof fn lemma_nat_count_ones_bound(n: nat, k: nat)
    requires
        n < pow2(k),
    ensures
        nat_count_ones(n) <= k,
        n == 0 <==> nat_count_ones(n) == 0,
    decreases n,
{
    if n != 0 {
        lemma2_to64();
        assert(k > 0);
        lemma_pow2_unfold(k);
        lemma_nat_count_ones_bound(n / 2, (k - 1) as nat);
    }
}

/// See [`axiom_u8_count_ones`] for useful properties.
#[verifier::allow_in_spec]
pub assume_specification[ u8::count_ones ](i: u8) -> u32
    returns
        nat_count_ones(i as nat) as u32,
    opens_invariants none
    no_unwind
;

/// See [`axiom_u16_count_ones`] for useful properties.
#[verifier::allow_in_spec]
pub assume_specification[ u16::count_ones ](i: u16) -> u32
    returns
        nat_count_ones(i as nat) as u32,
    opens_invariants none
    no_unwind
;

/// See [`axiom_u32_count_ones`] for useful properties.
#[verifier::allow_in_spec]
pub assume_specification[ u32::count_ones ](i: u32) -> u32
    returns
        nat_count_ones(i as nat) as u32,
    opens_invariants none
    no_unwind
;

/// See [`axiom_u64_count_ones`] for useful properties.
#[verifier::allow_in_spec]
pub assume_specification[ u64::count_ones ](i: u64) -> u32
    returns
        nat_count_ones(i as nat) as u32,
    opens_invariants none
    no_unwind
;

/// See [`axiom_u128_count_ones`] for useful properties.
#[verifier::allow_in_spec]
pub assume_specification[ u128::count_ones ](i: u128) -> u32
    returns
        nat_count_ones(i as nat) as u32,
    opens_invariants none
    no_unwind
;

/// See [`axiom_usize_count_ones`] for useful properties.
#[verifier::allow_in_spec]
pub assume_specification[ usize::count_ones ](i: usize) -> u32
    returns
        nat_count_ones(i as nat) as u32,
    opens_invariants none
    no_unwind
;

pub broadcast proof fn axiom_u8_count_ones(i: u8)
    ensures
        #![trigger nat_count_ones(i as nat)]
        i.count_ones() <= 8,
        i == 0 <==> i.count_ones() == 0,
{
    lemma_unsigned_int_max_is_pow2_minus_1();
    lemma_nat_count_ones_bound(i as nat, 8);
}

pub broadcast proof fn axiom_u16_count_ones(i: u16)
    ensures
        #![trigger nat_count_ones(i as nat)]
        i.count_ones() <= 16,
        i == 0 <==> i.count_ones() == 0,
{
    lemma_unsigned_int_max_is_pow2_minus_1();
    lemma_nat_count_ones_bound(i as nat, 16);
}

pub broadcast proof fn axiom_u32_count_ones(i: u32)
    ensures
        #![trigger nat_count_ones(i as nat)]
        i.count_ones() <= 32,
        i == 0 <==> i.count_ones() == 0,
{
    lemma_unsigned_int_max_is_pow2_minus_1();
    lemma_nat_count_ones_bound(i as nat, 32);
}

pub broadcast proof fn axiom_u64_count_ones(i: u64)
    ensures
        #![trigger nat_count_ones(i as nat)]
        i.count_ones() <= 64,
        i == 0 <==> i.count_ones() == 0,
{
    lemma_unsigned_int_max_is_pow2_minus_1();
    lemma_nat_count_ones_bound(i as nat, 64);
}

pub broadcast proof fn axiom_u128_count_ones(i: u128)
    ensures
        #![trigger nat_count_ones(i as nat)]
        i.count_ones() <= 128,
        i == 0 <==> i.count_ones() == 0,
{
    lemma_unsigned_int_max_is_pow2_minus_1();
    lemma_nat_count_ones_bound(i as nat, 128);
}

pub broadcast proof fn axiom_usize_count_ones(i: usize)
    ensures
        #![trigger nat_count_ones(i as nat)]
        i.count_ones() <= usize::BITS,
        i == 0 <==> i.count_ones() == 0,
{
    unsigned_int_max_values();
    lemma_nat_count_ones_bound(i as nat, usize::BITS as nat);
}

pub broadcast group group_bits_axioms {
    axiom_u8_trailing_zeros,
    axiom_u8_trailing_ones,
    axiom_u8_leading_zeros,
    axiom_u8_leading_ones,
    axiom_u16_trailing_zeros,
    axiom_u16_trailing_ones,
    axiom_u16_leading_zeros,
    axiom_u16_leading_ones,
    axiom_u32_trailing_zeros,
    axiom_u32_trailing_ones,
    axiom_u32_leading_zeros,
    axiom_u32_leading_ones,
    axiom_u64_trailing_zeros,
    axiom_u64_trailing_ones,
    axiom_u64_leading_zeros,
    axiom_u64_leading_ones,
    axiom_u8_reverse_bits,
    axiom_u16_reverse_bits,
    axiom_u32_reverse_bits,
    axiom_u64_reverse_bits,
    axiom_u128_trailing_zeros,
    axiom_u128_leading_zeros,
    axiom_usize_trailing_zeros,
    axiom_usize_leading_zeros,
    axiom_u8_count_ones,
    axiom_u16_count_ones,
    axiom_u32_count_ones,
    axiom_u64_count_ones,
    axiom_u128_count_ones,
    axiom_usize_count_ones,
}

} // verus!
