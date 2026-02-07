use super::prelude::*;
use super::seq::*;

verus! {

broadcast use crate::group_vstd_default;

/// byte has the form 0xxxxxxx
pub open spec fn is_leading_1(byte: u8) -> bool {
    byte & 0x80 == 0
}

/// byte has the form 110xxxxx
/// 0xe0 = 1110 0000
/// 0xc0 = 1100 0000
/// excluding 0xc0 and 0xc1 is taken care of by valid_scalar check
pub open spec fn is_leading_2(byte: u8) -> bool {
    byte & 0xe0 == 0xc0
}

/// byte has the form 1110xxxx
/// 0xf0 = 1111 0000
/// 0xe0 = 1110 0000
pub open spec fn is_leading_3(byte: u8) -> bool {
    byte & 0xf0 == 0xe0
}

/// byte has the form 11110xxx
/// 0xf8 = 1111 1000
/// 0xf0 = 1111 0000
/// excluding 0xf5, 0xf6, 0xf7 is taken care of by valid_scalar check
pub open spec fn is_leading_4(byte: u8) -> bool {
    byte & 0xf8 == 0xf0
}

/// byte has the form 10xxxxxx
pub open spec fn is_continuation(byte: u8) -> bool {
    byte & 0xc0 == 0x80
}

// 0x3f = 0011 1111
// calls byte & 0011 1111, stripping the first two bits
// i.e. bytes whose top bits are "10" are "continuation" bytes
pub open spec fn cont_bits(byte: u8) -> u32
    recommends
        is_continuation(byte),
{
    (byte & 0x3f) as u32
}

// extracts the 7 data bits from a 1-byte sequence (ascii)
// mask: 0111 1111 (0x7f)
pub open spec fn leading_1_bits(byte: u8) -> u32
    recommends
        is_leading_1(byte),
{
    (byte & 0x7F) as u32
}

// extracts the 5 data bits from the first byte of a 2-byte sequence
// mask: 0001 1111 (0x1f)
pub open spec fn leading_2_bits(byte: u8) -> u32
    recommends
        is_leading_2(byte),
{
    (byte & 0x1F) as u32
}

// extracts the 4 data bits from the first byte of a 3-byte sequence
// mask: 0000 1111 (0x0f)
pub open spec fn leading_3_bits(byte: u8) -> u32
    recommends
        is_leading_3(byte),
{
    (byte & 0x0F) as u32
}

// extracts the 3 data bits from the first byte of a 4-byte sequence
// mask: 0000 0111 (0x07)
pub open spec fn leading_4_bits(byte: u8) -> u32
    recommends
        is_leading_4(byte),
{
    (byte & 0x07) as u32
}

/// Returns the initial codepoint accumulator for the first byte.
/// The first byte is special, only want bottom 5 bits for width 2, 4 bits
/// for width 3, and 3 bits for width 4.
pub open spec fn utf8_first_byte_spec(byte: u8, width: u32) -> u32
    recommends
        width <= 4,
{
    (byte & 0x7Fu8 >> (width as u8)) as u32
}

/// Returns the value of `ch` updated with continuation byte `byte`.
pub open spec fn utf8_acc_cont_byte_spec(ch: u32, byte: u8) -> u32 {
    (ch << 6) | cont_bits(byte)
}

// 0x7f = 0111 1111
pub open spec fn scalar_of_codepoint_1(byte1: u8) -> u32 {
    leading_1_bits(byte1)
}

// 0xc1 = 1100 0001
// 0xc1 & 0x1f = 0x01
// 0x01 << 6 = 0100 0000 = 0x40
// If byte2 = 0xff then byte2 & 0x3f = 0x3f = 0011 1111
// so highest possible is 0111 1111 = 0x7f < 0x80
pub open spec fn scalar_of_codepoint_2(byte1: u8, byte2: u8) -> u32 {
    (leading_2_bits(byte1) << 6) | cont_bits(byte2)
}

pub open spec fn scalar_of_codepoint_3(byte1: u8, byte2: u8, byte3: u8) -> u32 {
    (leading_3_bits(byte1) << 12) | (cont_bits(byte2) << 6) | cont_bits(byte3)
}

// 0xf7 = 1111 0111
// 0xf7 & 0x07 = 0x07
// 0x07 << 18 = 0001 1100 0000 0000 0000 0000 = 0x1c0000
// 0xf5 = 1111 0101
// 0xf5 & 0x07 = 0x05
// 0x05 << 18 = 0001 0100 0000 0000 0000 0000 = 0x140000
pub open spec fn scalar_of_codepoint_4(byte1: u8, byte2: u8, byte3: u8, byte4: u8) -> u32 {
    (leading_4_bits(byte1) << 18) | (cont_bits(byte2) << 12) | (cont_bits(byte3) << 6) | cont_bits(
        byte4,
    )
}

/// Do we have a well-formed leading and an appropriate number
/// of well-formed continuation bytes?
pub open spec fn valid_first_bit_encoding(bytes: Seq<u8>) -> bool {
    bytes.len() > 0 && (if is_leading_1(bytes[0]) {
        true
    } else if is_leading_2(bytes[0]) {
        bytes.len() >= 2 && is_continuation(bytes[1])
    } else if is_leading_3(bytes[0]) {
        bytes.len() >= 3 && is_continuation(bytes[1]) && is_continuation(bytes[2])
    } else if is_leading_4(bytes[0]) {
        bytes.len() >= 4 && is_continuation(bytes[1]) && is_continuation(bytes[2])
            && is_continuation(bytes[3])
    } else {
        false
    })
}

/// Length in bytes of first code point
pub open spec fn length_of_first_codepoint(bytes: Seq<u8>) -> int {
    if is_leading_1(bytes[0]) {
        1
    } else if is_leading_2(bytes[0]) {
        2
    } else if is_leading_3(bytes[0]) {
        3
    } else {
        // no need to say if is_leading_4? bc could also be a continuation
        4
    }
}

/// Scalar of the first code point, assuming it has well-formed
/// leading and continuation bytes.
pub open spec fn scalar_of_first_codepoint(bytes: Seq<u8>) -> u32 {
    if is_leading_1(bytes[0]) {
        scalar_of_codepoint_1(bytes[0])
    } else if is_leading_2(bytes[0]) {
        scalar_of_codepoint_2(bytes[0], bytes[1])
    } else if is_leading_3(bytes[0]) {
        scalar_of_codepoint_3(bytes[0], bytes[1], bytes[2])
    } else {
        scalar_of_codepoint_4(bytes[0], bytes[1], bytes[2], bytes[3])
    }
}

proof fn lemma_pop_first_codepoint_decreases(bytes: Seq<u8>)
    requires
        valid_first_bit_encoding(bytes),
    ensures
        pop_first_codepoint(bytes).len() < bytes.len(),
{
    assert(length_of_first_codepoint(bytes) <= bytes.len() as int);
    assert(pop_first_codepoint(bytes).len() == bytes.len() as int - length_of_first_codepoint(
        bytes,
    )) by { axiom_seq_subrange_len(bytes, length_of_first_codepoint(bytes), bytes.len() as int) };
}

/// Remove the first codepoint and return the remainder.
pub open spec fn pop_first_codepoint(bytes: Seq<u8>) -> Seq<u8> {
    bytes.subrange(
        length_of_first_codepoint(bytes),
        bytes.len() as int,
    )
    // takes a subrange starting just after the first codepoint all the way to the end

}

/// Take only the first codepoint.
pub open spec fn first_codepoint(bytes: Seq<u8>) -> Seq<u8> {
    bytes.subrange(0, length_of_first_codepoint(bytes))
}

/// Is the scalar value allowed for the given byte-length?
pub open spec fn valid_scalar(scalar: u32, len: int) -> bool {
    // Require that it's not an 'overlong encoding'
    (len == 2 ==> scalar >= 0x80) && (len == 3 ==> scalar >= 0x800) && (len == 4 ==> scalar
        >= 0x10000 && scalar
        <= 0x10ffff)
    // Check that it's not a 'surrogate'
     && !(0xD800 <= scalar <= 0xDFFF)
}

/// Is the first codepoint valid?
/// Requires both a valid bit-encoding and a valid scalar value.
pub open spec fn valid_first_codepoint(bytes: Seq<u8>) -> bool {
    valid_first_bit_encoding(bytes) && valid_scalar(
        scalar_of_first_codepoint(bytes),
        length_of_first_codepoint(bytes),
    )
}

/// Is this byte-string a valid UTF-8 sequence?
pub open spec fn valid_utf8(bytes: Seq<u8>) -> bool
    decreases bytes.len(),
{
    bytes.len() != 0 ==> valid_first_codepoint(bytes) && valid_utf8(pop_first_codepoint(bytes))
}

/// Interpretation of a UTF-8 byte-string as a sequence of unicode scalars.
pub open spec fn decode_utf8(bytes: Seq<u8>) -> Seq<char>
    recommends
        valid_utf8(bytes),
    decreases bytes.len(),
    when valid_utf8(bytes)
{
    if bytes.len() == 0 {
        seq![]
    } else {
        seq![scalar_of_first_codepoint(bytes) as char] + decode_utf8(pop_first_codepoint(bytes))
    }
}

/// scalar has the form 0xxxxxxx (where the leading bits are zeros)
pub open spec fn is_1_byte_codepoint(c: u32) -> bool {
    0 <= c <= 0x7F
}

/// scalar has the form 00000xxx xxxxxxxx (where the leading bits are zeros)
pub open spec fn is_2_byte_codepoint(c: u32) -> bool {
    0x80 <= c <= 0x7FF
}

/// scalar has the form xxxxxxxx xxxxxxxx (where the leading bits are zeros)
pub open spec fn is_3_byte_codepoint(c: u32) -> bool {
    0x800 <= c <= 0xFFFF && !(0xD800 <= c <= 0xDFFF)
}

/// scalar has the form 000x0000 xxxxxxxx xxxxxxxx (where the leading bits are zeros)
// TODO
pub open spec fn is_4_byte_codepoint(c: u32) -> bool {
    0x10000 <= c <= 0x10FFFF
}

pub open spec fn first_byte_1_byte_codepoint(c: u32) -> u8 
    recommends
        is_1_byte_codepoint(c)
{
    (c & 0x7F) as u8
}

pub open spec fn first_byte_2_byte_codepoint(c: u32) -> u8 
    recommends
        is_2_byte_codepoint(c)
{
    0xC0 | ((c >> 6) & 0x1F) as u8
}

pub open spec fn first_byte_3_byte_codepoint(c: u32) -> u8 
    recommends
        is_3_byte_codepoint(c)
{
    0xE0 | ((c >> 12) & 0x0F) as u8
}

pub open spec fn first_byte_4_byte_codepoint(c: u32) -> u8 
    recommends
        is_4_byte_codepoint(c)
{
    0xF0 | ((c >> 18) & 0x7) as u8
}

pub open spec fn last_continuation_byte(c: u32) -> u8 
    recommends
        is_2_byte_codepoint(c) || is_3_byte_codepoint(c) || is_4_byte_codepoint(c)
{
    0x80 | (c & 0x3F) as u8
}

pub open spec fn second_last_continuation_byte(c: u32) -> u8 
    recommends
        is_3_byte_codepoint(c) || is_4_byte_codepoint(c)
{
    0x80 | ((c >> 6) & 0x3F) as u8
}

pub open spec fn third_last_continuation_byte(c: u32) -> u8 
    recommends
        is_4_byte_codepoint(c)
{
    0x80 | ((c >> 12) & 0x3F) as u8
}

pub open spec fn valid_codepoint(c: u32) -> bool {
    0 < c <= 0x10ffff && !(0xD800 <= c <= 0xDFFF)
}

pub open spec fn codepoint_of_scalar(c: u32) -> Seq<u8> 
    recommends
        valid_codepoint(c)
{
    if is_1_byte_codepoint(c) {
        seq![first_byte_1_byte_codepoint(c)]
    } else if is_2_byte_codepoint(c) {
        seq![first_byte_2_byte_codepoint(c), last_continuation_byte(c)]
    } else if is_3_byte_codepoint(c) {
        seq![first_byte_3_byte_codepoint(c), second_last_continuation_byte(c), last_continuation_byte(c)]
    } else {
        seq![first_byte_4_byte_codepoint(c), third_last_continuation_byte(c), second_last_continuation_byte(c), last_continuation_byte(c)]
    }
}

pub open spec fn encode_utf8(chars: Seq<char>) -> Seq<u8> 
    decreases chars.len()
{
    if chars.len() == 0 {
        seq![]
    } else {
        codepoint_of_scalar(chars[0] as u32) + encode_utf8(chars.drop_first())
    }
}

/// Does the index into the byte sequence fall on a character boundary?
pub open spec fn is_char_boundary(bytes: Seq<u8>, index: int) -> bool
    recommends
        valid_utf8(bytes),
    decreases bytes.len(),
    when valid_utf8(bytes)
{
    if index == 0 {
        true
    } else if index < 0 || bytes.len() < index {
        false
    } else {
        is_char_boundary(pop_first_codepoint(bytes), index - length_of_first_codepoint(bytes))
    }
}

// ============================================================================
// Lemmas for proving decode_utf8 and encode_utf8 are inverses
// ============================================================================

proof fn codepoint_of_scalar_scalar_of_codepoint_1_byte(c: u32) by (bit_vector)
    requires
        is_1_byte_codepoint(c)
    ensures
        ({
            let b1 = first_byte_1_byte_codepoint(c);
            &&& is_leading_1(b1)
            &&& scalar_of_codepoint_1(b1) == c
        })
{}

proof fn codepoint_of_scalar_scalar_of_codepoint_2_byte(c: u32) by (bit_vector)
    requires
        is_2_byte_codepoint(c)
    ensures
        ({
            let b1 = first_byte_2_byte_codepoint(c);
            let b2 = last_continuation_byte(c);
            &&& !is_leading_1(b1)
            &&& is_leading_2(b1)
            &&& is_continuation(b2)
            &&& scalar_of_codepoint_2(b1, b2) == c
        })
{}

proof fn codepoint_of_scalar_scalar_of_codepoint_3_byte(c: u32) by (bit_vector)
    requires
        is_3_byte_codepoint(c)
    ensures
        ({
            let b1 = first_byte_3_byte_codepoint(c);
            let b2 = second_last_continuation_byte(c);
            let b3 = last_continuation_byte(c);
            &&& !is_leading_1(b1)
            &&& !is_leading_2(b1)
            &&& is_leading_3(b1)
            &&& is_continuation(b2)
            &&& is_continuation(b3)
            &&& scalar_of_codepoint_3(b1, b2, b3) == c
        })
{}

proof fn codepoint_of_scalar_scalar_of_codepoint_4_byte(c: u32) by (bit_vector)
    requires
        is_4_byte_codepoint(c)
    ensures
        ({
            let b1 = first_byte_4_byte_codepoint(c);
            let b2 = third_last_continuation_byte(c);
            let b3 = second_last_continuation_byte(c);
            let b4 = last_continuation_byte(c);
            &&& !is_leading_1(b1)
            &&& !is_leading_2(b1)
            &&& !is_leading_3(b1)
            &&& is_leading_4(b1)
            &&& is_continuation(b2)
            &&& is_continuation(b3)
            &&& is_continuation(b4)
            &&& scalar_of_codepoint_4(b1, b2, b3, b4) == c
        })
{}

proof fn lemma_codepoint_scalar_roundtrip(c: u32)
    requires
        valid_codepoint(c)
    ensures
        scalar_of_first_codepoint(codepoint_of_scalar(c)) == c,
        length_of_first_codepoint(codepoint_of_scalar(c)) == codepoint_of_scalar(c).len(),
        valid_first_bit_encoding(codepoint_of_scalar(c)),
        valid_scalar(c, codepoint_of_scalar(c).len() as int)
{
    if is_1_byte_codepoint(c) {
        codepoint_of_scalar_scalar_of_codepoint_1_byte(c);
    } else if is_2_byte_codepoint(c) {
        codepoint_of_scalar_scalar_of_codepoint_2_byte(c);
    } else if is_3_byte_codepoint(c) {
        codepoint_of_scalar_scalar_of_codepoint_3_byte(c);
    } else {
        codepoint_of_scalar_scalar_of_codepoint_4_byte(c);
    }
}

pub broadcast axiom fn char_is_valid_codepoint(c: char)
    ensures
        #[trigger] valid_codepoint(c as u32)
    ;

pub proof fn encode_utf8_first_codepoint(chars: Seq<char>)
    requires
        chars.len() > 0
    ensures
        scalar_of_first_codepoint(encode_utf8(chars)) == chars[0] as u32,
        length_of_first_codepoint(encode_utf8(chars)) == codepoint_of_scalar(chars[0] as u32).len(),
        valid_first_codepoint(encode_utf8(chars)),
        pop_first_codepoint(encode_utf8(chars)) =~= encode_utf8(chars.drop_first())
{
    let bytes = encode_utf8(chars);
    char_is_valid_codepoint(chars[0]);
    lemma_codepoint_scalar_roundtrip(chars[0] as u32);
}

pub broadcast proof fn encode_utf8_valid_utf8(chars: Seq<char>)
    ensures valid_utf8(#[trigger] encode_utf8(chars))
    decreases chars.len()
{
    if chars.len() == 0 {
    } else {
        let bytes = encode_utf8(chars);
        encode_utf8_first_codepoint(chars);
        assert(pop_first_codepoint(bytes) =~= encode_utf8(chars.drop_first()));
        encode_utf8_valid_utf8(chars.drop_first());
    }
}

/// Main theorem: decode_utf8(encode_utf8(chars)) == chars
pub proof fn theorem_decode_encode_inverse(chars: Seq<char>)
    ensures
        decode_utf8(encode_utf8(chars)) == chars,
    decreases chars.len(),
{
    broadcast use encode_utf8_valid_utf8;
    if chars.len() == 0 {
    } else {
        let bytes = encode_utf8(chars);
        encode_utf8_first_codepoint(chars);
        assume(scalar_of_first_codepoint(bytes) as char == chars[0]); // todo

        let rest = chars.drop_first();
        theorem_decode_encode_inverse(chars.drop_first());
    }
}

}