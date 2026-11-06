use super::super::prelude::*;

verus! {

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
pub closed spec fn u8_reverse_bits(i: u8) -> u8 {
    // Swap adjacent bits, then adjacent pairs of bits, and so on up to the two halves
    let i = ((i >> 1) & 0x55) | ((i & 0x55) << 1);
    let i = ((i >> 2) & 0x33) | ((i & 0x33) << 2);
    (i >> 4) | (i << 4)
}

#[verifier::when_used_as_spec(u8_reverse_bits)]
pub assume_specification[ u8::reverse_bits ](i: u8) -> (r: u8)
    ensures
        r == u8_reverse_bits(i),
    opens_invariants none
    no_unwind
;

pub broadcast proof fn axiom_u8_reverse_bits(i: u8)
    ensures
        u8_reverse_bits(#[trigger] u8_reverse_bits(i)) == i,
        // bit j of the result is bit 7 - j of i
        forall|j: u8|
            j < 8 ==> #[trigger] (u8_reverse_bits(i) >> j) & 1u8 == (i >> sub(7u8, j)) & 1u8,
{
    let r = u8_reverse_bits(i);
    let x1 = ((i >> 1) & 0x55) | ((i & 0x55) << 1);
    let x2 = ((x1 >> 2) & 0x33) | ((x1 & 0x33) << 2);
    assert(r == (x2 >> 4) | (x2 << 4));
    assert forall|j: u8| j < 8 implies #[trigger] (r >> j) & 1u8 == (i >> sub(7u8, j)) & 1u8 by {
        assert((r >> j) & 1u8 == (i >> sub(7u8, j)) & 1u8) by (bit_vector)
            requires
                x1 == ((i >> 1) & 0x55) | ((i & 0x55) << 1),
                x2 == ((x1 >> 2) & 0x33) | ((x1 & 0x33) << 2),
                r == (x2 >> 4) | (x2 << 4),
                j < 8,
        ;
    }
    let rr = u8_reverse_bits(r);
    let y1 = ((r >> 1) & 0x55) | ((r & 0x55) << 1);
    let y2 = ((y1 >> 2) & 0x33) | ((y1 & 0x33) << 2);
    assert(rr == (y2 >> 4) | (y2 << 4));
    assert(rr == i) by (bit_vector)
        requires
            x1 == ((i >> 1) & 0x55) | ((i & 0x55) << 1),
            x2 == ((x1 >> 2) & 0x33) | ((x1 & 0x33) << 2),
            r == (x2 >> 4) | (x2 << 4),
            y1 == ((r >> 1) & 0x55) | ((r & 0x55) << 1),
            y2 == ((y1 >> 2) & 0x33) | ((y1 & 0x33) << 2),
            rr == (y2 >> 4) | (y2 << 4),
    ;
}

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
pub closed spec fn u16_reverse_bits(i: u16) -> u16 {
    // Swap adjacent bits, then adjacent pairs of bits, and so on up to the two halves
    let i = ((i >> 1) & 0x5555) | ((i & 0x5555) << 1);
    let i = ((i >> 2) & 0x3333) | ((i & 0x3333) << 2);
    let i = ((i >> 4) & 0x0f0f) | ((i & 0x0f0f) << 4);
    (i >> 8) | (i << 8)
}

#[verifier::when_used_as_spec(u16_reverse_bits)]
pub assume_specification[ u16::reverse_bits ](i: u16) -> (r: u16)
    ensures
        r == u16_reverse_bits(i),
    opens_invariants none
    no_unwind
;

pub broadcast proof fn axiom_u16_reverse_bits(i: u16)
    ensures
        u16_reverse_bits(#[trigger] u16_reverse_bits(i)) == i,
        // bit j of the result is bit 15 - j of i
        forall|j: u16|
            j < 16 ==> #[trigger] (u16_reverse_bits(i) >> j) & 1u16 == (i >> sub(15u16, j)) & 1u16,
{
    let r = u16_reverse_bits(i);
    let x1 = ((i >> 1) & 0x5555) | ((i & 0x5555) << 1);
    let x2 = ((x1 >> 2) & 0x3333) | ((x1 & 0x3333) << 2);
    let x3 = ((x2 >> 4) & 0x0f0f) | ((x2 & 0x0f0f) << 4);
    assert(r == (x3 >> 8) | (x3 << 8));
    assert forall|j: u16| j < 16 implies #[trigger] (r >> j) & 1u16 == (i >> sub(15u16, j))
        & 1u16 by {
        assert((r >> j) & 1u16 == (i >> sub(15u16, j)) & 1u16) by (bit_vector)
            requires
                x1 == ((i >> 1) & 0x5555) | ((i & 0x5555) << 1),
                x2 == ((x1 >> 2) & 0x3333) | ((x1 & 0x3333) << 2),
                x3 == ((x2 >> 4) & 0x0f0f) | ((x2 & 0x0f0f) << 4),
                r == (x3 >> 8) | (x3 << 8),
                j < 16,
        ;
    }
    let rr = u16_reverse_bits(r);
    let y1 = ((r >> 1) & 0x5555) | ((r & 0x5555) << 1);
    let y2 = ((y1 >> 2) & 0x3333) | ((y1 & 0x3333) << 2);
    let y3 = ((y2 >> 4) & 0x0f0f) | ((y2 & 0x0f0f) << 4);
    assert(rr == (y3 >> 8) | (y3 << 8));
    assert(rr == i) by (bit_vector)
        requires
            x1 == ((i >> 1) & 0x5555) | ((i & 0x5555) << 1),
            x2 == ((x1 >> 2) & 0x3333) | ((x1 & 0x3333) << 2),
            x3 == ((x2 >> 4) & 0x0f0f) | ((x2 & 0x0f0f) << 4),
            r == (x3 >> 8) | (x3 << 8),
            y1 == ((r >> 1) & 0x5555) | ((r & 0x5555) << 1),
            y2 == ((y1 >> 2) & 0x3333) | ((y1 & 0x3333) << 2),
            y3 == ((y2 >> 4) & 0x0f0f) | ((y2 & 0x0f0f) << 4),
            rr == (y3 >> 8) | (y3 << 8),
    ;
}

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
pub closed spec fn u32_reverse_bits(i: u32) -> u32 {
    // Swap adjacent bits, then adjacent pairs of bits, and so on up to the two halves
    let i = ((i >> 1) & 0x5555_5555) | ((i & 0x5555_5555) << 1);
    let i = ((i >> 2) & 0x3333_3333) | ((i & 0x3333_3333) << 2);
    let i = ((i >> 4) & 0x0f0f_0f0f) | ((i & 0x0f0f_0f0f) << 4);
    let i = ((i >> 8) & 0x00ff_00ff) | ((i & 0x00ff_00ff) << 8);
    (i >> 16) | (i << 16)
}

#[verifier::when_used_as_spec(u32_reverse_bits)]
pub assume_specification[ u32::reverse_bits ](i: u32) -> (r: u32)
    ensures
        r == u32_reverse_bits(i),
    opens_invariants none
    no_unwind
;

pub broadcast proof fn axiom_u32_reverse_bits(i: u32)
    ensures
        u32_reverse_bits(#[trigger] u32_reverse_bits(i)) == i,
        // bit j of the result is bit 31 - j of i
        forall|j: u32|
            j < 32 ==> #[trigger] (u32_reverse_bits(i) >> j) & 1u32 == (i >> sub(31u32, j)) & 1u32,
{
    let r = u32_reverse_bits(i);
    let x1 = ((i >> 1) & 0x5555_5555) | ((i & 0x5555_5555) << 1);
    let x2 = ((x1 >> 2) & 0x3333_3333) | ((x1 & 0x3333_3333) << 2);
    let x3 = ((x2 >> 4) & 0x0f0f_0f0f) | ((x2 & 0x0f0f_0f0f) << 4);
    let x4 = ((x3 >> 8) & 0x00ff_00ff) | ((x3 & 0x00ff_00ff) << 8);
    assert(r == (x4 >> 16) | (x4 << 16));
    assert forall|j: u32| j < 32 implies #[trigger] (r >> j) & 1u32 == (i >> sub(31u32, j))
        & 1u32 by {
        assert((r >> j) & 1u32 == (i >> sub(31u32, j)) & 1u32) by (bit_vector)
            requires
                x1 == ((i >> 1) & 0x5555_5555) | ((i & 0x5555_5555) << 1),
                x2 == ((x1 >> 2) & 0x3333_3333) | ((x1 & 0x3333_3333) << 2),
                x3 == ((x2 >> 4) & 0x0f0f_0f0f) | ((x2 & 0x0f0f_0f0f) << 4),
                x4 == ((x3 >> 8) & 0x00ff_00ff) | ((x3 & 0x00ff_00ff) << 8),
                r == (x4 >> 16) | (x4 << 16),
                j < 32,
        ;
    }
    let rr = u32_reverse_bits(r);
    let y1 = ((r >> 1) & 0x5555_5555) | ((r & 0x5555_5555) << 1);
    let y2 = ((y1 >> 2) & 0x3333_3333) | ((y1 & 0x3333_3333) << 2);
    let y3 = ((y2 >> 4) & 0x0f0f_0f0f) | ((y2 & 0x0f0f_0f0f) << 4);
    let y4 = ((y3 >> 8) & 0x00ff_00ff) | ((y3 & 0x00ff_00ff) << 8);
    assert(rr == (y4 >> 16) | (y4 << 16));
    assert(rr == i) by (bit_vector)
        requires
            x1 == ((i >> 1) & 0x5555_5555) | ((i & 0x5555_5555) << 1),
            x2 == ((x1 >> 2) & 0x3333_3333) | ((x1 & 0x3333_3333) << 2),
            x3 == ((x2 >> 4) & 0x0f0f_0f0f) | ((x2 & 0x0f0f_0f0f) << 4),
            x4 == ((x3 >> 8) & 0x00ff_00ff) | ((x3 & 0x00ff_00ff) << 8),
            r == (x4 >> 16) | (x4 << 16),
            y1 == ((r >> 1) & 0x5555_5555) | ((r & 0x5555_5555) << 1),
            y2 == ((y1 >> 2) & 0x3333_3333) | ((y1 & 0x3333_3333) << 2),
            y3 == ((y2 >> 4) & 0x0f0f_0f0f) | ((y2 & 0x0f0f_0f0f) << 4),
            y4 == ((y3 >> 8) & 0x00ff_00ff) | ((y3 & 0x00ff_00ff) << 8),
            rr == (y4 >> 16) | (y4 << 16),
    ;
}

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
pub closed spec fn u64_reverse_bits(i: u64) -> u64 {
    // Swap adjacent bits, then adjacent pairs of bits, and so on up to the two halves
    let i = ((i >> 1) & 0x5555_5555_5555_5555) | ((i & 0x5555_5555_5555_5555) << 1);
    let i = ((i >> 2) & 0x3333_3333_3333_3333) | ((i & 0x3333_3333_3333_3333) << 2);
    let i = ((i >> 4) & 0x0f0f_0f0f_0f0f_0f0f) | ((i & 0x0f0f_0f0f_0f0f_0f0f) << 4);
    let i = ((i >> 8) & 0x00ff_00ff_00ff_00ff) | ((i & 0x00ff_00ff_00ff_00ff) << 8);
    let i = ((i >> 16) & 0x0000_ffff_0000_ffff) | ((i & 0x0000_ffff_0000_ffff) << 16);
    (i >> 32) | (i << 32)
}

#[verifier::when_used_as_spec(u64_reverse_bits)]
pub assume_specification[ u64::reverse_bits ](i: u64) -> (r: u64)
    ensures
        r == u64_reverse_bits(i),
    opens_invariants none
    no_unwind
;

pub broadcast proof fn axiom_u64_reverse_bits(i: u64)
    ensures
        u64_reverse_bits(#[trigger] u64_reverse_bits(i)) == i,
        // bit j of the result is bit 63 - j of i
        forall|j: u64|
            j < 64 ==> #[trigger] (u64_reverse_bits(i) >> j) & 1u64 == (i >> sub(63u64, j)) & 1u64,
{
    let r = u64_reverse_bits(i);
    let x1 = ((i >> 1) & 0x5555_5555_5555_5555) | ((i & 0x5555_5555_5555_5555) << 1);
    let x2 = ((x1 >> 2) & 0x3333_3333_3333_3333) | ((x1 & 0x3333_3333_3333_3333) << 2);
    let x3 = ((x2 >> 4) & 0x0f0f_0f0f_0f0f_0f0f) | ((x2 & 0x0f0f_0f0f_0f0f_0f0f) << 4);
    let x4 = ((x3 >> 8) & 0x00ff_00ff_00ff_00ff) | ((x3 & 0x00ff_00ff_00ff_00ff) << 8);
    let x5 = ((x4 >> 16) & 0x0000_ffff_0000_ffff) | ((x4 & 0x0000_ffff_0000_ffff) << 16);
    assert(r == (x5 >> 32) | (x5 << 32));
    assert forall|j: u64| j < 64 implies #[trigger] (r >> j) & 1u64 == (i >> sub(63u64, j))
        & 1u64 by {
        assert((r >> j) & 1u64 == (i >> sub(63u64, j)) & 1u64) by (bit_vector)
            requires
                x1 == ((i >> 1) & 0x5555_5555_5555_5555) | ((i & 0x5555_5555_5555_5555) << 1),
                x2 == ((x1 >> 2) & 0x3333_3333_3333_3333) | ((x1 & 0x3333_3333_3333_3333) << 2),
                x3 == ((x2 >> 4) & 0x0f0f_0f0f_0f0f_0f0f) | ((x2 & 0x0f0f_0f0f_0f0f_0f0f) << 4),
                x4 == ((x3 >> 8) & 0x00ff_00ff_00ff_00ff) | ((x3 & 0x00ff_00ff_00ff_00ff) << 8),
                x5 == ((x4 >> 16) & 0x0000_ffff_0000_ffff) | ((x4 & 0x0000_ffff_0000_ffff) << 16),
                r == (x5 >> 32) | (x5 << 32),
                j < 64,
        ;
    }
    let rr = u64_reverse_bits(r);
    let y1 = ((r >> 1) & 0x5555_5555_5555_5555) | ((r & 0x5555_5555_5555_5555) << 1);
    let y2 = ((y1 >> 2) & 0x3333_3333_3333_3333) | ((y1 & 0x3333_3333_3333_3333) << 2);
    let y3 = ((y2 >> 4) & 0x0f0f_0f0f_0f0f_0f0f) | ((y2 & 0x0f0f_0f0f_0f0f_0f0f) << 4);
    let y4 = ((y3 >> 8) & 0x00ff_00ff_00ff_00ff) | ((y3 & 0x00ff_00ff_00ff_00ff) << 8);
    let y5 = ((y4 >> 16) & 0x0000_ffff_0000_ffff) | ((y4 & 0x0000_ffff_0000_ffff) << 16);
    assert(rr == (y5 >> 32) | (y5 << 32));
    assert(rr == i) by (bit_vector)
        requires
            x1 == ((i >> 1) & 0x5555_5555_5555_5555) | ((i & 0x5555_5555_5555_5555) << 1),
            x2 == ((x1 >> 2) & 0x3333_3333_3333_3333) | ((x1 & 0x3333_3333_3333_3333) << 2),
            x3 == ((x2 >> 4) & 0x0f0f_0f0f_0f0f_0f0f) | ((x2 & 0x0f0f_0f0f_0f0f_0f0f) << 4),
            x4 == ((x3 >> 8) & 0x00ff_00ff_00ff_00ff) | ((x3 & 0x00ff_00ff_00ff_00ff) << 8),
            x5 == ((x4 >> 16) & 0x0000_ffff_0000_ffff) | ((x4 & 0x0000_ffff_0000_ffff) << 16),
            r == (x5 >> 32) | (x5 << 32),
            y1 == ((r >> 1) & 0x5555_5555_5555_5555) | ((r & 0x5555_5555_5555_5555) << 1),
            y2 == ((y1 >> 2) & 0x3333_3333_3333_3333) | ((y1 & 0x3333_3333_3333_3333) << 2),
            y3 == ((y2 >> 4) & 0x0f0f_0f0f_0f0f_0f0f) | ((y2 & 0x0f0f_0f0f_0f0f_0f0f) << 4),
            y4 == ((y3 >> 8) & 0x00ff_00ff_00ff_00ff) | ((y3 & 0x00ff_00ff_00ff_00ff) << 8),
            y5 == ((y4 >> 16) & 0x0000_ffff_0000_ffff) | ((y4 & 0x0000_ffff_0000_ffff) << 16),
            rr == (y5 >> 32) | (y5 << 32),
    ;
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
}

} // verus!
