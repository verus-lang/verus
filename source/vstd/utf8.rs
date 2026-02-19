use super::prelude::*;
use super::seq::*;

verus! {

broadcast use super::seq::group_seq_axioms;

/// byte has the form 0xxxxxxx
pub open spec fn is_leading_1(byte: u8) -> bool {
    0x00 <= byte <= 0x7f
}

/*
result == 1 <==> 0x00 <= b <= 0x7f,
        result == 2 <==> 0xc2 <= b <= 0xdf,
        result == 3 <==> 0xe0 <= b <= 0xef,
        result == 4 <==> 0xf0 <= b <= 0xf4,
*/

/// byte has the form 110xxxxx
/// 0xe0 = 1110 0000
/// 0xc0 = 1100 0000
/// excluding 0xc0 and 0xc1 is taken care of by valid_scalar_of_len check
pub open spec fn is_leading_2(byte: u8) -> bool {
    0xc2 <= byte <= 0xdf
}

/// byte has the form 1110xxxx
/// 0xf0 = 1111 0000
/// 0xe0 = 1110 0000
pub open spec fn is_leading_3(byte: u8) -> bool {
    0xe0 <= byte <= 0xef
}

/// byte has the form 11110xxx
/// 0xf8 = 1111 1000
/// 0xf0 = 1111 0000
/// excluding 0xf5, 0xf6, 0xf7 is taken care of by valid_scalar_of_len check
pub open spec fn is_leading_4(byte: u8) -> bool {
    0xf0 <= byte <= 0xf4
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
pub open spec fn scalar_of_codepoint_1(byte1: u8) -> u32
    recommends
        is_leading_1(byte1),
{
    leading_1_bits(byte1)
}

// 0xc1 = 1100 0001
// 0xc1 & 0x1f = 0x01
// 0x01 << 6 = 0100 0000 = 0x40
// If byte2 = 0xff then byte2 & 0x3f = 0x3f = 0011 1111
// so highest possible is 0111 1111 = 0x7f < 0x80
pub open spec fn scalar_of_codepoint_2(byte1: u8, byte2: u8) -> u32
    recommends
        is_leading_2(byte1) && is_continuation(byte2),
{
    (leading_2_bits(byte1) << 6) | cont_bits(byte2)
}

pub open spec fn scalar_of_codepoint_3(byte1: u8, byte2: u8, byte3: u8) -> u32
    recommends
        is_leading_3(byte1) && is_continuation(byte2) && is_continuation(byte3),
{
    (leading_3_bits(byte1) << 12) | (cont_bits(byte2) << 6) | cont_bits(byte3)
}

// 0xf7 = 1111 0111
// 0xf7 & 0x07 = 0x07
// 0x07 << 18 = 0001 1100 0000 0000 0000 0000 = 0x1c0000
// 0xf5 = 1111 0101
// 0xf5 & 0x07 = 0x05
// 0x05 << 18 = 0001 0100 0000 0000 0000 0000 = 0x140000
pub open spec fn scalar_of_codepoint_4(byte1: u8, byte2: u8, byte3: u8, byte4: u8) -> u32
    recommends
        is_leading_4(byte1) && is_continuation(byte2) && is_continuation(byte3) && is_continuation(
            byte4,
        ),
{
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
pub open spec fn length_of_first_codepoint(bytes: Seq<u8>) -> int
    recommends
        bytes.len() > 0,
{
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
pub open spec fn scalar_of_first_codepoint(bytes: Seq<u8>) -> u32
    recommends
        bytes.len() > 0,
{
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
pub open spec fn pop_first_codepoint(bytes: Seq<u8>) -> Seq<u8>
    recommends
        bytes.len() > 0,
{
    bytes.subrange(
        length_of_first_codepoint(bytes),
        bytes.len() as int,
    )
    // takes a subrange starting just after the first codepoint all the way to the end

}

/// Take only the first codepoint.
pub open spec fn first_codepoint(bytes: Seq<u8>) -> Seq<u8>
    recommends
        bytes.len() > 0,
{
    bytes.subrange(0, length_of_first_codepoint(bytes))
}

/// Is the scalar value allowed for the given byte-length?
// todo -- should this have a check for len 1?
pub open spec fn valid_scalar_of_len(scalar: u32, len: int) -> bool {
    // Require that it's not an 'overlong encoding'
    (len == 2 ==> scalar >= 0x80) && (len == 3 ==> scalar >= 0x800) && (len == 4 ==> scalar
        >= 0x10000 && scalar
        <= 0x10ffff)
    // Check that it's not a 'surrogate'
     && !(0xD800 <= scalar <= 0xDFFF)
}

/// Is the first codepoint valid?
/// Requires both a valid bit-encoding and a valid scalar value.
pub open spec fn valid_first_codepoint(bytes: Seq<u8>) -> bool
    recommends
        bytes.len() > 0,
{
    valid_first_bit_encoding(bytes) && valid_scalar_of_len(
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

/// True when the given `u32` represents a UTF-8 codepoint that is 1 byte long.
/// The value must have the form 0xxxxxxx (where the leading bytes are zeros).
/// todo - redo these comments maybe?
pub open spec fn is_1_byte_codepoint(c: u32) -> bool {
    0 <= c <= 0x7F
}

/// True when the given `u32` represents a UTF-8 codepoint that is 2 bytes long.
/// The value must have the form 00000xxx xxxxxxxx (where the leading bytes are zeros).
pub open spec fn is_2_byte_codepoint(c: u32) -> bool {
    0x80 <= c <= 0x7FF
}

/// True when the given `u32` represents a UTF-8 codepoint that is 3 bytes long.
/// The value must have the form xxxxxxxx xxxxxxxx (where the leading bytes are zeros) and not be in the range 0xD800 to 0xDFFF.
pub open spec fn is_3_byte_codepoint(c: u32) -> bool {
    0x800 <= c <= 0xFFFF && !(0xD800 <= c <= 0xDFFF)
}

/// True when the given `u32` represents a UTF-8 codepoint that is 4 bytes long.
/// The value must have the form 000x0000 xxxxxxxx xxxxxxxx (where the leading bytes are zeros).
pub open spec fn is_4_byte_codepoint(c: u32) -> bool {
    0x10000 <= c <= 0x10FFFF
}

/// Converts a `u32` which represents a 1-byte UTF-8 codepoint to the byte representation of that codepoint.
pub open spec fn first_byte_1_byte_codepoint(c: u32) -> u8
    recommends
        is_1_byte_codepoint(c),
{
    (c & 0x7F) as u8
}

/// Converts a `u32` which represents a 2-byte UTF-8 codepoint to the first byte of that codepoint.
pub open spec fn first_byte_2_byte_codepoint(c: u32) -> u8
    recommends
        is_2_byte_codepoint(c),
{
    0xC0 | ((c >> 6) & 0x1F) as u8
}

/// Converts a `u32` which represents a 3-byte UTF-8 codepoint to the first byte of that codepoint.
pub open spec fn first_byte_3_byte_codepoint(c: u32) -> u8
    recommends
        is_3_byte_codepoint(c),
{
    0xE0 | ((c >> 12) & 0x0F) as u8
}

/// Converts a `u32` which represents a 4-byte UTF-8 codepoint to the first byte of that codepoint.
pub open spec fn first_byte_4_byte_codepoint(c: u32) -> u8
    recommends
        is_4_byte_codepoint(c),
{
    0xF0 | ((c >> 18) & 0x7) as u8
}

/// Converts a `u32` which represents a 2-byte, 3-byte, or 4-byte UTF-8 codepoint to the last continuation byte of that codepoint.
pub open spec fn last_continuation_byte(c: u32) -> u8
    recommends
        is_2_byte_codepoint(c) || is_3_byte_codepoint(c) || is_4_byte_codepoint(c),
{
    0x80 | (c & 0x3F) as u8
}

/// Converts a `u32` which represents a 3-byte or 4-byte UTF-8 codepoint to the second-last continuation byte of that codepoint.
pub open spec fn second_last_continuation_byte(c: u32) -> u8
    recommends
        is_3_byte_codepoint(c) || is_4_byte_codepoint(c),
{
    0x80 | ((c >> 6) & 0x3F) as u8
}

/// Converts a `u32` which represents a 4-byte UTF-8 codepoint to the third-last continuation byte of that codepoint.
pub open spec fn third_last_continuation_byte(c: u32) -> u8
    recommends
        is_4_byte_codepoint(c),
{
    0x80 | ((c >> 12) & 0x3F) as u8
}

/// True when the given `u32` can be encoded as UTF-8.
pub open spec fn valid_scalar(c: u32) -> bool {
    0 <= c <= 0x10ffff && !(0xD800 <= c <= 0xDFFF)
}

/// Converts a `u32` to the codepoint of its UTF-8 representation.
pub open spec fn codepoint_of_scalar(c: u32) -> Seq<u8>
    recommends
        valid_scalar(c),
{
    if is_1_byte_codepoint(c) {
        seq![first_byte_1_byte_codepoint(c)]
    } else if is_2_byte_codepoint(c) {
        seq![first_byte_2_byte_codepoint(c), last_continuation_byte(c)]
    } else if is_3_byte_codepoint(c) {
        seq![
            first_byte_3_byte_codepoint(c),
            second_last_continuation_byte(c),
            last_continuation_byte(c),
        ]
    } else {
        seq![
            first_byte_4_byte_codepoint(c),
            third_last_continuation_byte(c),
            second_last_continuation_byte(c),
            last_continuation_byte(c),
        ]
    }
}

/// Converts a sequence of `char`s to its UTF-8 representation.
pub open spec fn encode_utf8(chars: Seq<char>) -> Seq<u8>
    decreases chars.len(),
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

/* encode_utf8 and decode_utf8 correspondence */

// codepoint_of_scalar((scalar_of_codepoint_1(bytes[0]) as char) as u32)[0] == bytes[0]
proof fn codepoint_of_scalar_scalar_of_codepoint_1_byte(c: u32)
    by (bit_vector)
    requires
        is_1_byte_codepoint(c),
    ensures
        ({
            let b1 = first_byte_1_byte_codepoint(c);
            &&& is_leading_1(b1)
            &&& scalar_of_codepoint_1(b1) == c
        }),
{
}

proof fn scalar_of_codepoint_codepoint_of_scalar_1_byte(b1: u8)
    by (bit_vector)
    requires
        is_leading_1(b1),
        valid_scalar_of_len(scalar_of_codepoint_1(b1), 1),
    ensures
        ({
            let c = scalar_of_codepoint_1(b1);
            &&& valid_scalar(c)
            &&& is_1_byte_codepoint(c)
            &&& first_byte_1_byte_codepoint(c) == b1
        }),
{
}

proof fn codepoint_of_scalar_scalar_of_codepoint_2_byte(c: u32)
    by (bit_vector)
    requires
        is_2_byte_codepoint(c),
    ensures
        ({
            let b1 = first_byte_2_byte_codepoint(c);
            let b2 = last_continuation_byte(c);
            //&&& !is_leading_1(b1)
            &&& is_leading_2(b1)
            &&& is_continuation(b2)
            &&& scalar_of_codepoint_2(b1, b2) == c
        }),
{
}

proof fn scalar_of_codepoint_codepoint_of_scalar_2_byte(b1: u8, b2: u8)
    by (bit_vector)
    requires
        is_leading_2(b1),
        is_continuation(b2),
        valid_scalar_of_len(scalar_of_codepoint_2(b1, b2), 2),
    ensures
        ({
            let c = scalar_of_codepoint_2(b1, b2);
            &&& valid_scalar(c)
            &&& is_2_byte_codepoint(c)
            &&& first_byte_2_byte_codepoint(c) == b1
            &&& last_continuation_byte(c) == b2
        }),
{
}

proof fn codepoint_of_scalar_scalar_of_codepoint_3_byte(c: u32)
    by (bit_vector)
    requires
        is_3_byte_codepoint(c),
    ensures
        ({
            let b1 = first_byte_3_byte_codepoint(c);
            let b2 = second_last_continuation_byte(c);
            let b3 = last_continuation_byte(c);
            //&&& !is_leading_1(b1)
            //&&& !is_leading_2(b1)
            &&& is_leading_3(b1)
            &&& is_continuation(b2)
            &&& is_continuation(b3)
            &&& scalar_of_codepoint_3(b1, b2, b3) == c
        }),
{
}

proof fn scalar_of_codepoint_codepoint_of_scalar_3_byte(b1: u8, b2: u8, b3: u8)
    by (bit_vector)
    requires
        is_leading_3(b1),
        is_continuation(b2),
        is_continuation(b3),
        valid_scalar_of_len(scalar_of_codepoint_3(b1, b2, b3), 3),
    ensures
        ({
            let c = scalar_of_codepoint_3(b1, b2, b3);
            &&& valid_scalar(c)
            &&& is_3_byte_codepoint(c)
            &&& first_byte_3_byte_codepoint(c) == b1
            &&& second_last_continuation_byte(c) == b2
            &&& last_continuation_byte(c) == b3
        }),
{
}

proof fn codepoint_of_scalar_scalar_of_codepoint_4_byte(c: u32)
    by (bit_vector)
    requires
        is_4_byte_codepoint(c),
    ensures
        ({
            let b1 = first_byte_4_byte_codepoint(c);
            let b2 = third_last_continuation_byte(c);
            let b3 = second_last_continuation_byte(c);
            let b4 = last_continuation_byte(c);
            // &&& !is_leading_1(b1)
            // &&& !is_leading_2(b1)
            // &&& !is_leading_3(b1)
            &&& is_leading_4(b1)
            &&& is_continuation(b2)
            &&& is_continuation(b3)
            &&& is_continuation(b4)
            &&& scalar_of_codepoint_4(b1, b2, b3, b4) == c
        }),
{
}

proof fn scalar_of_codepoint_codepoint_of_scalar_4_byte(b1: u8, b2: u8, b3: u8, b4: u8)
    by (bit_vector)
    requires
        is_leading_4(b1),
        is_continuation(b2),
        is_continuation(b3),
        is_continuation(b4),
        valid_scalar_of_len(scalar_of_codepoint_4(b1, b2, b3, b4), 4),
    ensures
        ({
            let c = scalar_of_codepoint_4(b1, b2, b3, b4);
            &&& valid_scalar(c)
            &&& is_4_byte_codepoint(c)
            &&& first_byte_4_byte_codepoint(c) == b1
            &&& third_last_continuation_byte(c) == b2
            &&& second_last_continuation_byte(c) == b3
            &&& last_continuation_byte(c) == b4
        }),
{
}

pub broadcast proof fn char_is_valid_scalar(c: char)
    ensures
        #[trigger] valid_scalar(c as u32),
{
}

pub broadcast proof fn char_u32_cast(c: char, u: u32)
    requires
        u == c as u32,
    ensures
        #![trigger c as u32, u as char]
        u as char == c,
{
}

/// Properties of the first codepoint of the result of `encode_utf8`.
pub proof fn encode_utf8_first_codepoint(chars: Seq<char>)
    requires
        chars.len() > 0,
    ensures
        scalar_of_first_codepoint(encode_utf8(chars)) == chars[0] as u32,
        length_of_first_codepoint(encode_utf8(chars)) == codepoint_of_scalar(chars[0] as u32).len(),
        valid_first_codepoint(encode_utf8(chars)),
{
    char_is_valid_scalar(chars[0]);
    let s = chars[0] as u32;
    if is_1_byte_codepoint(s) {
        codepoint_of_scalar_scalar_of_codepoint_1_byte(s);
    } else if is_2_byte_codepoint(s) {
        codepoint_of_scalar_scalar_of_codepoint_2_byte(s);
    } else if is_3_byte_codepoint(s) {
        codepoint_of_scalar_scalar_of_codepoint_3_byte(s);
    } else {
        codepoint_of_scalar_scalar_of_codepoint_4_byte(s);
    }
}

/// Ensures the result of `encode_utf8` always satisfies `valid_utf8`.
pub broadcast proof fn encode_utf8_valid_utf8(chars: Seq<char>)
    ensures
        valid_utf8(#[trigger] encode_utf8(chars)),
    decreases chars.len(),
{
    if chars.len() == 0 {
    } else {
        let bytes = encode_utf8(chars);
        encode_utf8_first_codepoint(chars);
        assert(pop_first_codepoint(bytes) =~= encode_utf8(chars.drop_first()));
        encode_utf8_valid_utf8(chars.drop_first());
    }
}

/// Ensures that performing `encode_utf8` followed by `decode_utf8` results in the original `char` sequence.
pub proof fn encode_utf8_decode_utf8(chars: Seq<char>)
    ensures
        decode_utf8(encode_utf8(chars)) == chars,
    decreases chars.len(),
{
    broadcast use encode_utf8_valid_utf8;

    if chars.len() == 0 {
    } else {
        let bytes = encode_utf8(chars);
        encode_utf8_first_codepoint(chars);
        char_u32_cast(chars[0], scalar_of_first_codepoint(bytes));

        assert(pop_first_codepoint(bytes) =~= encode_utf8(chars.drop_first()));
        let rest = chars.drop_first();
        encode_utf8_decode_utf8(rest);
    }
}

pub proof fn decode_utf8_first_codepoint(bytes: Seq<u8>)
    requires
        valid_utf8(bytes),
        bytes.len() > 0,
    ensures
        codepoint_of_scalar((scalar_of_first_codepoint(bytes) as char) as u32) == first_codepoint(
            bytes,
        ),
{
    if is_leading_1(bytes[0]) {
        scalar_of_codepoint_codepoint_of_scalar_1_byte(bytes[0]);
    } else if is_leading_2(bytes[0]) {
        scalar_of_codepoint_codepoint_of_scalar_2_byte(bytes[0], bytes[1]);
    } else if is_leading_3(bytes[0]) {
        scalar_of_codepoint_codepoint_of_scalar_3_byte(bytes[0], bytes[1], bytes[2]);
    } else {
        scalar_of_codepoint_codepoint_of_scalar_4_byte(bytes[0], bytes[1], bytes[2], bytes[3]);
    }
}

pub proof fn decode_utf8_encode_utf8(bytes: Seq<u8>)
    requires
        valid_utf8(bytes),
    ensures
        encode_utf8(decode_utf8(bytes)) == bytes,
    decreases bytes.len(),
{
    broadcast use encode_utf8_valid_utf8;

    if bytes.len() == 0 {
    } else {
        let chars = decode_utf8(bytes);
        let first = scalar_of_first_codepoint(bytes) as char;
        let rest = pop_first_codepoint(bytes);

        char_is_valid_scalar(first);
        assert(codepoint_of_scalar(first as u32) == first_codepoint(bytes)) by {
            decode_utf8_first_codepoint(bytes);
        }

        assert(chars.drop_first() =~= decode_utf8(rest));
        decode_utf8_encode_utf8(rest);
    }
}

/* ascii */

pub open spec fn is_ascii_chars(chars: Seq<char>) -> bool {
    forall |i| 0 <= i < chars.len() ==> '\0' <= #[trigger] chars[i] <= '\x7f'

}

// todo - add to a broadcast group
pub broadcast proof fn is_ascii_chars_encode_utf8(chars: Seq<char>)
    requires
        #[trigger] is_ascii_chars(chars),
    ensures
        chars.len() == encode_utf8(chars).len(),
        forall|i|
            #![trigger chars[i]]
            #![trigger encode_utf8(chars)[i]]
            0 <= i < chars.len() ==> chars[i] as u8 == encode_utf8(chars)[i],
    decreases chars.len(),
{
    if chars.len() == 0 {
    } else {
        let c0 = chars[0] as u32;
        assert(c0 as u8 == first_byte_1_byte_codepoint(c0)) by (bit_vector)
            requires
                is_1_byte_codepoint(c0),
        ;
        is_ascii_chars_encode_utf8(chars.drop_first());
    }
}

pub broadcast proof fn is_ascii_chars_nat_bound(chars: Seq<char>)
    ensures
        #[trigger] is_ascii_chars(s) ==> forall|i: int| 0 <= i < s@.len() ==> (s@.index(i) as nat) < 128
{}

//todo - add cfg
pub broadcast proof fn is_ascii_concat(c1: Seq<char>, s2: Seq<char>, s3: Seq<char>)
    requires
        s1@ =~= #[trigger] s2@ + s3@,
    ensures
        #[trigger] is_ascii(s1) <==> #[trigger] is_ascii(s2) && #[trigger] is_ascii(s3)
{
    if (is_ascii(s1)) {
        assert(s2@ =~= s1@.subrange(0, s2@.len() as int));
        assert(s3@ =~= s1@.subrange(s2@.len() as int, s1@.len() as int));
    }
}

} // verus!
