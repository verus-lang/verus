//! Definitions for UTF-8 encoding and decoding of character sequences.
//!
//! [UTF-8](https://en.wikipedia.org/wiki/UTF-8) is a variable-width character encoding scheme.
//! Each character is encoded with between 1 and 4 bytes.
//! Specifications for encoding and decoding characters to their UTF-8 byte sequences are given by [`encode_utf8`] and [`decode_utf8`], respectively.
//! Characters in the ASCII character set are encoded in UTF-8 with 1-byte encodings identical to those used by ASCII.
//! Thus, some UTF-8 byte sequences can also be considered ASCII byte sequences, as defined in [`is_ascii_chars`].
//!
//! UTF-8 encodes numerical values called Unicode _scalars_ (see below), which assign a unique value to each Unicode character.
//! A scalar value is encoded in UTF-8 using a leading byte and between 0 and 3 continuation bytes, where larger scalar values require more continuation bytes.
//! The first part of the bit pattern in the leading byte is reserved for describing the number of bytes in the scalar's encoding (e.g., [`is_leading_byte_width_1`]).
//! The rest of the leading byte contains data bits corresponding to the scalar's value (e.g., [`leading_bits_width_1`]).
//! The continuation bytes also follow a specific bit pattern ([`is_continuation_byte`]) and contain the remainder of the data bits ([`continuation_bits`]).
//!
//! This module makes use of terminology from the [Unicode standard](https://www.unicode.org/glossary/).
//! A Unicode _scalar_ is a numerical value (represented in this module as a `u32`) corresponding to a character that can be encoded in UTF-8.
//! All Rust `char`s correspond to Unicode scalars ([`char_is_scalar`]),
//! and every numerical value encoded in a UTF-8 byte sequence must fall within the range defined for Unicode scalars ([`is_scalar`]).
//! The Unicode standard also defines a _codepoint_ to be a numerical value which falls in the range available for encoding characters in UTF-8.
//! This may sound similar to the definition of scalar.
//! However, the definition of codepoint is more permissive than that for scalars,
//! as it includes some values which are technically possible to encode in the UTF-8 scheme,
//! but in fact are not legal Unicode values
//! (namely, the [high-surrogate and low-surrogate ranges](https://en.wikipedia.org/wiki/UTF-8#Surrogates)).
//! To align with the Unicode terminology, in this module, we use the term "scalar" to describe the numerical values
//! which can be encoded in valid UTF-8 byte sequences, and the term "codepoint" to describe numerical values which
//! are learned upon decoding a byte sequence but may or may not be legal Unicode values.
use super::prelude::*;
use super::seq::*;

verus! {

broadcast use super::seq::group_seq_axioms;
/* Decoding UTF-8 to chars */

/// True when the given byte conforms to the bit pattern for the first byte of a 1-byte UTF-8 encoding of a single codepoint.
/// The byte must have the form 0xxxxxxx.
pub open spec fn is_leading_byte_width_1(byte: u8) -> bool {
    0x00 <= byte <= 0x7f
}

/// True when the given byte conforms to the bit pattern for the first byte of a 2-byte UTF-8 encoding of a single codepoint.
/// The byte must have the form 110xxxxx.
pub open spec fn is_leading_byte_width_2(byte: u8) -> bool {
    0xc0 <= byte <= 0xdf
}

/// True when the given byte conforms to the bit pattern for the first byte of a 3-byte UTF-8 encoding of a single codepoint.
/// The byte must have the form 1110xxxx.
pub open spec fn is_leading_byte_width_3(byte: u8) -> bool {
    0xe0 <= byte <= 0xef
}

/// True when the given byte conforms to the bit pattern for the first byte of a 4-byte UTF-8 encoding of a single codepoint.
/// The byte must have the form 11110xxx.
pub open spec fn is_leading_byte_width_4(byte: u8) -> bool {
    0xf0 <= byte <= 0xf7
}

/// True when the given byte conforms to the bit pattern for a continuation byte of a UTF-8 encoding of a single codepoint.
/// The byte must have the form 10xxxxxx.
pub open spec fn is_continuation_byte(byte: u8) -> bool {
    0x80 <= byte <= 0xbf
}

/// Value of the 6 data bits from the given continuation byte, assuming that it is a valid continuation byte for a UTF-8 encoding.
pub open spec fn continuation_bits(byte: u8) -> u32
    recommends
        is_continuation_byte(byte),
{
    // 0x3f = 0011 1111
    (byte & 0x3f) as u32
}

/// Value of the 7 data bits from the given byte, assuming that it is a valid leading byte for a 1-byte UTF-8 encoding.
pub open spec fn leading_bits_width_1(byte: u8) -> u32
    recommends
        is_leading_byte_width_1(byte),
{
    // 0x7f = 0111 1111
    (byte & 0x7F) as u32
}

/// Value of the 5 data bits from the given byte, assuming that it is a valid leading byte for a 2-byte UTF-8 encoding.
pub open spec fn leading_bits_width_2(byte: u8) -> u32
    recommends
        is_leading_byte_width_2(byte),
{
    // 0x1f = 0001 1111
    (byte & 0x1F) as u32
}

/// Value of the 4 data bits from the given byte, assuming that it is a valid leading byte for a 3-byte UTF-8 encoding.
pub open spec fn leading_bits_width_3(byte: u8) -> u32
    recommends
        is_leading_byte_width_3(byte),
{
    // 0x0f = 0000 1111
    (byte & 0x0F) as u32
}

/// Value of the 3 data bits from the given byte, assuming that it is a valid leading byte for a 4-byte UTF-8 encoding.
pub open spec fn leading_bits_width_4(byte: u8) -> u32
    recommends
        is_leading_byte_width_4(byte),
{
    // 0x07 = 0000 0111
    (byte & 0x07) as u32
}

/// The codepoint encoded by the given byte, assuming that it is a valid leading byte for a 1-byte UTF-8 encoding.
pub open spec fn codepoint_width_1(byte1: u8) -> u32
    recommends
        is_leading_byte_width_1(byte1),
{
    leading_bits_width_1(byte1)
}

// 0xc1 = 1100 0001
// 0xc1 & 0x1f = 0x01
// 0x01 << 6 = 0100 0000 = 0x40
// If byte2 = 0xff then byte2 & 0x3f = 0x3f = 0011 1111
// so highest possible is 0111 1111 = 0x7f < 0x80
/// The codepoint encoded by the given 2 bytes, assuming that they are a valid leading and continuation byte, respectively, for 2-byte UTF-8 encoding.
pub open spec fn codepoint_width_2(byte1: u8, byte2: u8) -> u32
    recommends
        is_leading_byte_width_2(byte1),
        is_continuation_byte(byte2),
{
    (leading_bits_width_2(byte1) << 6) | continuation_bits(byte2)
}

/// The codepoint encoded by the given 3 bytes, assuming that they are a valid leading and continuation bytes, respectively, for 3-byte UTF-8 encoding.
pub open spec fn codepoint_width_3(byte1: u8, byte2: u8, byte3: u8) -> u32
    recommends
        is_leading_byte_width_3(byte1),
        is_continuation_byte(byte2),
        is_continuation_byte(byte3),
{
    (leading_bits_width_3(byte1) << 12) | (continuation_bits(byte2) << 6) | continuation_bits(byte3)
}

// 0xf7 = 1111 0111
// 0xf7 & 0x07 = 0x07
// 0x07 << 18 = 0001 1100 0000 0000 0000 0000 = 0x1c0000
// 0xf5 = 1111 0101
// 0xf5 & 0x07 = 0x05
// 0x05 << 18 = 0001 0100 0000 0000 0000 0000 = 0x140000
/// The codepoint encoded by the given 4 bytes, assuming that they are a valid leading and continuation bytes, respectively, for 4-byte UTF-8 encoding.
pub open spec fn codepoint_width_4(byte1: u8, byte2: u8, byte3: u8, byte4: u8) -> u32
    recommends
        is_leading_byte_width_4(byte1),
        is_continuation_byte(byte2),
        is_continuation_byte(byte3),
        is_continuation_byte(byte4),
{
    (leading_bits_width_4(byte1) << 18) | (continuation_bits(byte2) << 12) | (continuation_bits(
        byte3,
    ) << 6) | continuation_bits(byte4)
}

/// True when the given byte sequence begins with a well-formed leading byte and an appropriate number of well-formed continuation bytes for a UTF-8 encoding of a single codepoint.
pub open spec fn valid_leading_and_continuation_bytes_first_codepoint(bytes: Seq<u8>) -> bool {
    ||| (bytes.len() >= 1 && is_leading_byte_width_1(bytes[0]))
    ||| (bytes.len() >= 2 && is_leading_byte_width_2(bytes[0]) && is_continuation_byte(bytes[1]))
    ||| (bytes.len() >= 3 && is_leading_byte_width_3(bytes[0]) && is_continuation_byte(bytes[1])
        && is_continuation_byte(bytes[2]))
    ||| (bytes.len() >= 4 && is_leading_byte_width_4(bytes[0]) && is_continuation_byte(bytes[1])
        && is_continuation_byte(bytes[2]) && is_continuation_byte(bytes[3]))
}

/// Returns the first codepoint encoded in UTF-8 in the given byte sequence, assuming that the sequence begins with a well-formed leading byte and an appropriate number of well-formed continuation bytes.
pub open spec fn decode_first_codepoint(bytes: Seq<u8>) -> u32
    recommends
        valid_leading_and_continuation_bytes_first_codepoint(bytes),
{
    if is_leading_byte_width_1(bytes[0]) {
        codepoint_width_1(bytes[0])
    } else if is_leading_byte_width_2(bytes[0]) {
        codepoint_width_2(bytes[0], bytes[1])
    } else if is_leading_byte_width_3(bytes[0]) {
        codepoint_width_3(bytes[0], bytes[1], bytes[2])
    } else {
        codepoint_width_4(bytes[0], bytes[1], bytes[2], bytes[3])
    }
}

/// The length in bytes of the first codepoint encoded in UTF-8 in the given byte sequence, assuming that the sequence begins with a well-formed leading byte and an appropriate number of well-formed continuation bytes.
pub open spec fn length_of_first_codepoint(bytes: Seq<u8>) -> int
    recommends
        valid_leading_and_continuation_bytes_first_codepoint(bytes),
{
    if is_leading_byte_width_1(bytes[0]) {
        1
    } else if is_leading_byte_width_2(bytes[0]) {
        2
    } else if is_leading_byte_width_3(bytes[0]) {
        3
    } else {
        4
    }
}

/// True when the given codepoint, when encoded in UTF-8 using `len` number of bytes, would not be an "overlong encoding".
/// An overlong encoding is one that uses more bytes than needed to encode the given value.
pub open spec fn not_overlong_encoding(codepoint: u32, len: int) -> bool {
    &&& (len == 2 ==> 0x80 <= codepoint)
    &&& (len == 3 ==> 0x800 <= codepoint)
    &&& (len == 4 ==> 0x10000 <= codepoint <= 0x10ffff)
}

/// True when the given codepoint does not fall into the "surrogate range" of the Unicode standard.
/// The surrogate range contains values which are technically possible to encode in UTF-8 but are not valid Unicode scalars.
pub open spec fn not_surrogate(codepoint: u32) -> bool {
    !(0xD800 <= codepoint <= 0xDFFF)
}

/// True when the given byte sequence begins with a well-formed UTF-8 encoding of a single scalar.
/// To be a well-formed encoding, the bytes must: follow the expected bit pattern for leading and continuation bytes
/// for a single scalar encoding, not be an "overlong encoding", and not fall in the surrogate range.
pub open spec fn valid_first_scalar(bytes: Seq<u8>) -> bool {
    &&& valid_leading_and_continuation_bytes_first_codepoint(bytes)
    &&& not_overlong_encoding(decode_first_codepoint(bytes), length_of_first_codepoint(bytes))
    &&& not_surrogate(decode_first_codepoint(bytes))
}

/// The first scalar encoded in UTF-8 in the given byte sequence, assuming that the sequence begins with a well-formed encoding of a single scalar.
pub open spec fn decode_first_scalar(bytes: Seq<u8>) -> u32
    recommends
        valid_first_scalar(bytes),
{
    decode_first_codepoint(bytes)
}

/// The length in bytes of first scalar encoded in UTF-8 in the given byte sequence, assuming that the sequence begins with a well-formed encoding of a single scalar.
pub open spec fn length_of_first_scalar(bytes: Seq<u8>) -> int
    recommends
        valid_first_scalar(bytes),
{
    length_of_first_codepoint(bytes)
}

/// Removes the first scalar encoded in UTF-8 in the given byte sequence and returns the rest of the sequence, assuming that the sequence begins with a well-formed encoding of a single scalar.
pub open spec fn pop_first_scalar(bytes: Seq<u8>) -> Seq<u8>
    recommends
        valid_first_scalar(bytes),
{
    bytes.subrange(length_of_first_scalar(bytes), bytes.len() as int)
}

proof fn lemma_pop_first_scalar_decreases(bytes: Seq<u8>)
    requires
        valid_first_scalar(bytes),
    ensures
        pop_first_scalar(bytes).len() < bytes.len(),
{
    assert(length_of_first_scalar(bytes) <= bytes.len() as int);
    assert(pop_first_scalar(bytes).len() == bytes.len() as int - length_of_first_scalar(bytes)) by {
        axiom_seq_subrange_len(bytes, length_of_first_scalar(bytes), bytes.len() as int)
    };
}

/// Takes the bytes corresponding to the first scalar encoded in UTF-8 in the given byte sequence, assuming that the sequence begins with a well-formed encoding of a single scalar.
pub open spec fn take_first_scalar(bytes: Seq<u8>) -> Seq<u8>
    recommends
        valid_first_scalar(bytes),
{
    bytes.subrange(0, length_of_first_scalar(bytes))
}

/// True when the given bytes form a valid UTF-8 encoding.
pub open spec fn valid_utf8(bytes: Seq<u8>) -> bool
    decreases bytes.len(),
{
    bytes.len() != 0 ==> valid_first_scalar(bytes) && valid_utf8(pop_first_scalar(bytes))
}

/// The sequence of characters encoded as Unicode scalars in the given bytes, assuming that the bytes form a valid UTF-8 encoding.
pub open spec fn decode_utf8(bytes: Seq<u8>) -> Seq<char>
    recommends
        valid_utf8(bytes),
    decreases bytes.len(),
    when valid_utf8(bytes)
{
    if bytes.len() == 0 {
        seq![]
    } else {
        seq![decode_first_scalar(bytes) as char] + decode_utf8(pop_first_scalar(bytes))
    }
}

/// The length in bytes of the last scalar encoded in UTF-8 in the given byte sequence, assuming that the bytes form a valid UTF-8 encoding.
pub open spec fn length_of_last_scalar(bytes: Seq<u8>) -> int
    recommends
        valid_utf8(bytes),
        bytes.len() > 0,
{
    let n = bytes.len() as int;
    if !is_continuation_byte(bytes[n - 1]) {
        1
    } else if !is_continuation_byte(bytes[n - 2]) {
        2
    } else if !is_continuation_byte(bytes[n - 3]) {
        3
    } else {
        4
    }
}

/// Takes the bytes corresponding to the last scalar encoded in UTF-8 in the given byte sequence, assuming that the bytes form a valid UTF-8 encoding.
pub open spec fn take_last_scalar(bytes: Seq<u8>) -> Seq<u8>
    recommends
        valid_utf8(bytes),
        bytes.len() > 0,
{
    let len = length_of_last_scalar(bytes);
    bytes.subrange(bytes.len() - len, bytes.len() as int)
}

/// The last scalar encoded in UTF-8 in the given byte sequence, assuming that the bytes form a valid UTF-8 encoding.
pub open spec fn decode_last_scalar(bytes: Seq<u8>) -> u32
    recommends
        valid_utf8(bytes),
        bytes.len() > 0,
{
    let n = bytes.len() as int;
    if !is_continuation_byte(bytes[n - 1]) {
        codepoint_width_1(bytes[n - 1])
    } else if !is_continuation_byte(bytes[n - 2]) {
        codepoint_width_2(bytes[n - 2], bytes[n - 1])
    } else if !is_continuation_byte(bytes[n - 3]) {
        codepoint_width_3(bytes[n - 3], bytes[n - 2], bytes[n - 1])
    } else {
        codepoint_width_4(bytes[n - 4], bytes[n - 3], bytes[n - 2], bytes[n - 1])
    }
}

/* Encoding chars as UTF-8 */

/// True when the given value is a Unicode scalar with a 1-byte UTF-8 encoding.
pub open spec fn has_width_1_encoding(v: u32) -> bool {
    0 <= v <= 0x7F
}

/// True when the given value is a Unicode scalar with a 2-byte UTF-8 encoding.
pub open spec fn has_width_2_encoding(v: u32) -> bool {
    0x80 <= v <= 0x7FF
}

/// True when the given value is a Unicode scalar with a 3-byte UTF-8 encoding.
pub open spec fn has_width_3_encoding(v: u32) -> bool {
    0x800 <= v <= 0xFFFF && !(0xD800 <= v <= 0xDFFF)
}

/// True when the given value is a Unicode scalar with a 4-byte UTF-8 encoding.
pub open spec fn has_width_4_encoding(v: u32) -> bool {
    0x10000 <= v <= 0x10FFFF
}

/// True when the given `u32` represents a Unicode scalar, i.e., a value that can be encoded in UTF-8.
/// This definition is equivalent to: `0 <= v <= 0x10ffff && !(0xD800 <= v <= 0xDFFF)`.
pub open spec fn is_scalar(v: u32) -> bool {
    ||| has_width_1_encoding(v)
    ||| has_width_2_encoding(v)
    ||| has_width_3_encoding(v)
    ||| has_width_4_encoding(v)
}

/// The first (and only) byte of the UTF-8 encoding of the given scalar value, assuming that the scalar has a 1-byte UTF-8 encoding.
pub open spec fn leading_byte_width_1(scalar: u32) -> u8
    recommends
        has_width_1_encoding(scalar),
{
    (scalar & 0x7F) as u8
}

/// The first byte of the UTF-8 encoding of the given scalar value, assuming that the scalar has a 2-byte UTF-8 encoding.
pub open spec fn leading_byte_width_2(scalar: u32) -> u8
    recommends
        has_width_2_encoding(scalar),
{
    0xC0 | ((scalar >> 6) & 0x1F) as u8
}

/// The first byte of the UTF-8 encoding of the given scalar value, assuming that the scalar has a 3-byte UTF-8 encoding.
pub open spec fn leading_byte_width_3(scalar: u32) -> u8
    recommends
        has_width_3_encoding(scalar),
{
    0xE0 | ((scalar >> 12) & 0x0F) as u8
}

/// The first byte of the UTF-8 encoding of the given scalar value, assuming that the scalar has a 4-byte UTF-8 encoding.
pub open spec fn leading_byte_width_4(scalar: u32) -> u8
    recommends
        has_width_4_encoding(scalar),
{
    0xF0 | ((scalar >> 18) & 0x7) as u8
}

/// The last continuation byte of the UTF-8 encoding of the given scalar value, assuming that the scalar has a 2, 3, or 4-byte UTF-8 encoding.
pub open spec fn last_continuation_byte(scalar: u32) -> u8
    recommends
        has_width_2_encoding(scalar) || has_width_3_encoding(scalar) || has_width_4_encoding(
            scalar,
        ),
{
    0x80 | (scalar & 0x3F) as u8
}

/// The second-to-last continuation byte of the UTF-8 encoding of the given scalar value, assuming that the scalar has a 3 or 4-byte UTF-8 encoding.
pub open spec fn second_last_continuation_byte(scalar: u32) -> u8
    recommends
        has_width_3_encoding(scalar) || has_width_4_encoding(scalar),
{
    0x80 | ((scalar >> 6) & 0x3F) as u8
}

/// The third-to-last continuation byte of the UTF-8 encoding of the given scalar value, assuming that the scalar has a 4-byte UTF-8 encoding.
pub open spec fn third_last_continuation_byte(scalar: u32) -> u8
    recommends
        has_width_4_encoding(scalar),
{
    0x80 | ((scalar >> 12) & 0x3F) as u8
}

/// The UTF-8 encoding of the given value, assuming that it is a Unicode scalar.
pub open spec fn encode_scalar(scalar: u32) -> Seq<u8>
    recommends
        is_scalar(scalar),
{
    if has_width_1_encoding(scalar) {
        seq![leading_byte_width_1(scalar)]
    } else if has_width_2_encoding(scalar) {
        seq![leading_byte_width_2(scalar), last_continuation_byte(scalar)]
    } else if has_width_3_encoding(scalar) {
        seq![
            leading_byte_width_3(scalar),
            second_last_continuation_byte(scalar),
            last_continuation_byte(scalar),
        ]
    } else {
        seq![
            leading_byte_width_4(scalar),
            third_last_continuation_byte(scalar),
            second_last_continuation_byte(scalar),
            last_continuation_byte(scalar),
        ]
    }
}

/// The UTF-8 encoding of the given `char` sequence.
pub open spec fn encode_utf8(chars: Seq<char>) -> Seq<u8>
    decreases chars.len(),
{
    if chars.len() == 0 {
        seq![]
    } else {
        encode_scalar(chars[0] as u32) + encode_utf8(chars.drop_first())
    }
}

/* Correspondence between encode_utf8 and decode_utf8 definitions */

// Performing encode followed by decode on a scalar with a 1-byte UTF-8 encoding results in the same value.
proof fn encode_decode_width_1(c: u32)
    by (bit_vector)
    requires
        has_width_1_encoding(c),
    ensures
        ({
            let b1 = leading_byte_width_1(c);
            &&& is_leading_byte_width_1(b1)
            &&& codepoint_width_1(b1) == c
        }),
{
}

// Performing decode followed by encode on a 1-byte UTF-8 encoding results in the same byte.
proof fn decode_encode_width_1(b1: u8)
    by (bit_vector)
    requires
        is_leading_byte_width_1(b1),
    ensures
        ({
            let c = codepoint_width_1(b1);
            &&& has_width_1_encoding(c)
            &&& leading_byte_width_1(c) == b1
        }),
{
}

// Performing encode followed by decode on a scalar with a 2-byte UTF-8 encoding  results in the same value.
proof fn encode_decode_width_2(c: u32)
    by (bit_vector)
    requires
        has_width_2_encoding(c),
    ensures
        ({
            let b1 = leading_byte_width_2(c);
            let b2 = last_continuation_byte(c);
            &&& is_leading_byte_width_2(b1)
            &&& is_continuation_byte(b2)
            &&& codepoint_width_2(b1, b2) == c
        }),
{
}

// Performing decode followed by encode on a 2-byte UTF-8 encoding results in the same bytes.
proof fn decode_encode_width_2(b1: u8, b2: u8)
    by (bit_vector)
    requires
        is_leading_byte_width_2(b1),
        is_continuation_byte(b2),
        not_overlong_encoding(codepoint_width_2(b1, b2), 2),
    ensures
        ({
            let c = codepoint_width_2(b1, b2);
            &&& has_width_2_encoding(c)
            &&& leading_byte_width_2(c) == b1
            &&& last_continuation_byte(c) == b2
        }),
{
}

// Performing encode followed by decode on a scalar with a 3-byte UTF-8 encoding  results in the same value.
proof fn encode_decode_width_3(c: u32)
    by (bit_vector)
    requires
        has_width_3_encoding(c),
    ensures
        ({
            let b1 = leading_byte_width_3(c);
            let b2 = second_last_continuation_byte(c);
            let b3 = last_continuation_byte(c);
            &&& is_leading_byte_width_3(b1)
            &&& is_continuation_byte(b2)
            &&& is_continuation_byte(b3)
            &&& codepoint_width_3(b1, b2, b3) == c
        }),
{
}

// Performing decode followed by encode on a 3-byte UTF-8 encoding results in the same bytes.
proof fn decode_encode_width_3(b1: u8, b2: u8, b3: u8)
    by (bit_vector)
    requires
        is_leading_byte_width_3(b1),
        is_continuation_byte(b2),
        is_continuation_byte(b3),
        not_overlong_encoding(codepoint_width_3(b1, b2, b3), 3),
        not_surrogate(codepoint_width_3(b1, b2, b3)),
    ensures
        ({
            let c = codepoint_width_3(b1, b2, b3);
            &&& has_width_3_encoding(c)
            &&& leading_byte_width_3(c) == b1
            &&& second_last_continuation_byte(c) == b2
            &&& last_continuation_byte(c) == b3
        }),
{
}

// Performing encode followed by decode on a scalar with a 4-byte UTF-8 encoding results in the same value.
proof fn encode_decode_width_4(c: u32)
    by (bit_vector)
    requires
        has_width_4_encoding(c),
    ensures
        ({
            let b1 = leading_byte_width_4(c);
            let b2 = third_last_continuation_byte(c);
            let b3 = second_last_continuation_byte(c);
            let b4 = last_continuation_byte(c);
            &&& is_leading_byte_width_4(b1)
            &&& is_continuation_byte(b2)
            &&& is_continuation_byte(b3)
            &&& is_continuation_byte(b4)
            &&& codepoint_width_4(b1, b2, b3, b4) == c
        }),
{
}

// Performing decode followed by encode on a 4-byte UTF-8 encoding results in the same bytes.
proof fn decode_encode_width_4(b1: u8, b2: u8, b3: u8, b4: u8)
    by (bit_vector)
    requires
        is_leading_byte_width_4(b1),
        is_continuation_byte(b2),
        is_continuation_byte(b3),
        is_continuation_byte(b4),
        not_overlong_encoding(codepoint_width_4(b1, b2, b3, b4), 4),
    ensures
        ({
            let c = codepoint_width_4(b1, b2, b3, b4);
            &&& has_width_4_encoding(c)
            &&& leading_byte_width_4(c) == b1
            &&& third_last_continuation_byte(c) == b2
            &&& second_last_continuation_byte(c) == b3
            &&& last_continuation_byte(c) == b4
        }),
{
}

/// A `char` always represents a Unicode scalar value.
pub broadcast proof fn char_is_scalar(c: char)
    ensures
        is_scalar(#[trigger] (c as u32)),
{
}

/// Ensures that a `char`, when cast to a `u32`, can be cast back to a `char`.
pub broadcast proof fn char_u32_cast(c: char, u: u32)
    requires
        u == #[trigger] (c as u32),
    ensures
        #[trigger] (u as char) == c,
{
}

/// Properties of the first scalar from the result of [`encode_utf8`].
pub proof fn encode_utf8_first_scalar(chars: Seq<char>)
    requires
        chars.len() > 0,
    ensures
        decode_first_scalar(encode_utf8(chars)) == chars[0] as u32,
        length_of_first_scalar(encode_utf8(chars)) == encode_scalar(chars[0] as u32).len(),
        valid_first_scalar(encode_utf8(chars)),
{
    char_is_scalar(chars[0]);
    let s = chars[0] as u32;
    if has_width_1_encoding(s) {
        encode_decode_width_1(s);
    } else if has_width_2_encoding(s) {
        encode_decode_width_2(s);
    } else if has_width_3_encoding(s) {
        encode_decode_width_3(s);
    } else {
        encode_decode_width_4(s);
    }
}

/// Ensures the result of [`encode_utf8`] always satisfies [`valid_utf8`].
pub broadcast proof fn encode_utf8_valid_utf8(chars: Seq<char>)
    ensures
        valid_utf8(#[trigger] encode_utf8(chars)),
    decreases chars.len(),
{
    if chars.len() == 0 {
    } else {
        let bytes = encode_utf8(chars);
        encode_utf8_first_scalar(chars);
        assert(pop_first_scalar(bytes) =~= encode_utf8(chars.drop_first()));
        encode_utf8_valid_utf8(chars.drop_first());
    }
}

/// Ensures that performing [`encode_utf8`] followed by [`decode_utf8`] results in the original `char` sequence.
pub broadcast proof fn encode_utf8_decode_utf8(chars: Seq<char>)
    ensures
        #[trigger] decode_utf8(encode_utf8(chars)) == chars,
    decreases chars.len(),
{
    broadcast use encode_utf8_valid_utf8;

    if chars.len() == 0 {
    } else {
        let bytes = encode_utf8(chars);
        encode_utf8_first_scalar(chars);
        char_u32_cast(chars[0], decode_first_scalar(bytes));

        assert(pop_first_scalar(bytes) =~= encode_utf8(chars.drop_first()));
        let rest = chars.drop_first();
        encode_utf8_decode_utf8(rest);
    }
}

/// Properties of the first scalar from the result of [`decode_utf8`].
pub proof fn decode_utf8_first_scalar(bytes: Seq<u8>)
    requires
        valid_utf8(bytes),
        bytes.len() > 0,
    ensures
        encode_scalar((decode_first_scalar(bytes) as char) as u32) == take_first_scalar(bytes),
{
    if is_leading_byte_width_1(bytes[0]) {
        decode_encode_width_1(bytes[0]);
    } else if is_leading_byte_width_2(bytes[0]) {
        decode_encode_width_2(bytes[0], bytes[1]);
    } else if is_leading_byte_width_3(bytes[0]) {
        decode_encode_width_3(bytes[0], bytes[1], bytes[2]);
    } else {
        decode_encode_width_4(bytes[0], bytes[1], bytes[2], bytes[3]);
    }
}

/// Ensures that performing [`decode_utf8`] followed by [`encode_utf8`] results in the original byte sequence.
pub broadcast proof fn decode_utf8_encode_utf8(bytes: Seq<u8>)
    requires
        valid_utf8(bytes),
    ensures
        #[trigger] encode_utf8(decode_utf8(bytes)) == bytes,
    decreases bytes.len(),
{
    broadcast use encode_utf8_valid_utf8;

    if bytes.len() == 0 {
    } else {
        let chars = decode_utf8(bytes);
        let first = decode_first_scalar(bytes) as char;
        let rest = pop_first_scalar(bytes);

        char_is_scalar(first);
        assert(encode_scalar(first as u32) == take_first_scalar(bytes)) by {
            decode_utf8_first_scalar(bytes);
        }

        assert(chars.drop_first() =~= decode_utf8(rest));
        decode_utf8_encode_utf8(rest);
    }
}

/* Partial UTF-8 sequences */

/// True when the first `i` bytes in the given sequence represent a valid UTF-8 encoding.
pub open spec fn partial_valid_utf8(bytes: Seq<u8>, i: int) -> bool {
    0 <= i <= bytes.len() && valid_utf8(bytes.subrange(0, i))
}

/// Ensures that a byte sequence is not a valid UTF-8 byte sequence when it has a suffix that is not a valid UTF-8 byte sequence.
pub proof fn partial_valid_partial_invalid_utf8(bytes: Seq<u8>, i: int)
    requires
        0 <= i <= bytes.len(),
        valid_utf8(bytes.subrange(0, i)),
        !valid_utf8(bytes.subrange(i, bytes.len() as int)),
    ensures
        !valid_utf8(bytes),
{
    partial_valid_utf8_invalid_subrange_helper(bytes, i, 0);
    assert(bytes.subrange(0, bytes.len() as int) =~= bytes);
}

proof fn partial_valid_utf8_invalid_subrange_helper(bytes: Seq<u8>, i: int, j: int)
    requires
        0 <= j <= i <= bytes.len(),
        valid_utf8(bytes.subrange(0, i)),
        !valid_utf8(bytes.subrange(i, bytes.len() as int)),
        valid_utf8(bytes.subrange(0, j)),
        valid_utf8(bytes.subrange(j, i)),
    ensures
        !valid_utf8(bytes.subrange(j, bytes.len() as int)),
    decreases (bytes.len() - j),
{
    if j == i {
    } else {
        let bytes_j = bytes.subrange(j, bytes.len() as int);
        if valid_first_scalar(bytes_j) {
            partial_valid_utf8_extend(bytes, j);
            let k = length_of_first_scalar(bytes_j);

            assert(pop_first_scalar(bytes.subrange(j, i)) == bytes.subrange(j + k, i));

            partial_valid_utf8_invalid_subrange_helper(bytes, i, j + k);

            assert(bytes_j.subrange(k, bytes_j.len() as int) == bytes.subrange(
                j + k,
                bytes.len() as int,
            ));
        }
    }
}

/// Ensures that concatenating two valid UTF-8 byte sequence results in a valid UTF-8 byte sequence.
pub broadcast proof fn valid_utf8_concat(b1: Seq<u8>, b2: Seq<u8>)
    requires
        #[trigger] valid_utf8(b1),
        #[trigger] valid_utf8(b2),
    ensures
        #[trigger] valid_utf8(b1 + b2),
    decreases b1.len(),
{
    if b1.len() == 0 {
        assert(b1 + b2 == b2) by { Seq::add_empty_left(b1, b2) };
        assert(valid_utf8(b1 + b2));
    } else {
        let rest = pop_first_scalar(b1);
        assert(pop_first_scalar(b1).len() < b1.len()) by { lemma_pop_first_scalar_decreases(b1) };
        valid_utf8_concat(rest, b2);
        assert(pop_first_scalar(b1 + b2) =~= rest + b2);
        assert(valid_utf8(b1 + b2));
    }
}

/// Ensures that if the prefix of a byte sequence is valid UTF-8, and remainder of the sequence begins with a valid UTF-8 encoding of a single scalar,
/// then the prefix extended by that scalar encoding is also valid UTF-8.
pub broadcast proof fn partial_valid_utf8_extend(bytes: Seq<u8>, i: int)
    requires
        #[trigger] partial_valid_utf8(bytes, i),
        #[trigger] valid_first_scalar(bytes.subrange(i, bytes.len() as int)),
    ensures
        #[trigger] partial_valid_utf8(
            bytes,
            i + length_of_first_scalar(bytes.subrange(i, bytes.len() as int)),
        ),
{
    reveal_with_fuel(valid_utf8, 2);
    let scalar = bytes.subrange(
        i,
        i + length_of_first_scalar(bytes.subrange(i, bytes.len() as int)),
    );
    valid_utf8_concat(bytes.subrange(0, i), scalar);
    assert(bytes.subrange(0, i) + scalar =~= bytes.subrange(
        0,
        i + length_of_first_scalar(bytes.subrange(i, bytes.len() as int)),
    ));
}

/// Ensures that if the prefix of a byte sequence is valid UTF-8, and remainder of the sequence begins with a subsequence of valid UTF-8 encodings for 1-byte scalars (i.e. ASCII characters),
/// then the prefix extended by that subsequence is also valid UTF-8.
pub broadcast proof fn partial_valid_utf8_extend_ascii_block(bytes: Seq<u8>, start: int, end: int)
    requires
        forall|i: int|
            0 <= start <= i < end <= bytes.len() ==> #[trigger] is_leading_byte_width_1(bytes[i]),
        partial_valid_utf8(bytes, start),
        0 <= start <= end <= bytes.len(),
    ensures
        #![trigger partial_valid_utf8(bytes, start), partial_valid_utf8(bytes, end)]
        partial_valid_utf8(bytes, end),
    decreases end - start,
{
    if end == start {
    } else {
        partial_valid_utf8_extend_ascii_block(bytes, start, end - 1);

        let b = bytes[end - 1];
        assert(is_leading_byte_width_1(b));
        partial_valid_utf8_extend(bytes, end - 1);
    }
}

/* Reasoning about character boundaries */

/// True when the given index into the byte sequence is the first byte of a character's encoding or the end of the sequence, assuming that the sequence is valid UTF-8.
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
        is_char_boundary(pop_first_scalar(bytes), index - length_of_first_scalar(bytes))
    }
}

proof fn take_first_scalar_valid_utf8(bytes: Seq<u8>)
    requires
        valid_utf8(bytes),
    ensures
        bytes.len() > 0 ==> valid_utf8(take_first_scalar(bytes)),
{
    reveal_with_fuel(valid_utf8, 2);
}

/// Ensures that the two subsequences formed by splitting a valid UTF-8 byte sequence at a character boundary are also valid UTF-8 byte sequences.
pub broadcast proof fn valid_utf8_split(bytes: Seq<u8>, index: int)
    requires
        valid_utf8(bytes),
        is_char_boundary(bytes, index),
    ensures
        #![trigger valid_utf8(bytes.subrange(0, index)), is_char_boundary(bytes, index)]
        #![trigger valid_utf8(bytes.subrange(index, bytes.len() as int)), is_char_boundary(bytes, index)]
        valid_utf8(bytes.subrange(0, index)),
        valid_utf8(bytes.subrange(index, bytes.len() as int)),
    decreases bytes.len(),
{
    if index == 0 {
        assert(bytes =~= bytes.subrange(index, bytes.len() as int));
    } else {
        broadcast use axiom_seq_subrange_len;

        let s1 = bytes.subrange(0, index);
        let s2 = bytes.subrange(index, bytes.len() as int);
        let head = take_first_scalar(bytes);
        let tail = pop_first_scalar(bytes);
        let new_offset = index - length_of_first_scalar(bytes);
        // recursive call: show valid on split for tail
        valid_utf8_split(tail, new_offset);
        let n1 = tail.subrange(0, new_offset);
        let n2 = tail.subrange(new_offset, tail.len() as int);
        // now we need to concatenate the head back on
        assert(s1 =~= head + n1) by {
            assert(s1.len() == head.len() + n1.len()) by {
                // to use subrange len axiom, we need to show that new_offset is in bounds for tail
                is_char_boundary_len_first_scalar(bytes, index);
            }
        }
        assert(valid_utf8(head + n1)) by {
            take_first_scalar_valid_utf8(bytes);
            valid_utf8_concat(head, n1);
        }
        assert(s2 =~= n2);
    }
}

/// Ensures that a valid UTF-8 byte sequence can be decoded by separately decoding the two subsequences formed by splitting the original sequence at a character boundary.
pub broadcast proof fn decode_utf8_split(bytes: Seq<u8>, index: int)
    requires
        valid_utf8(bytes),
        is_char_boundary(bytes, index),
    ensures
        #![trigger decode_utf8(bytes.subrange(0, index)), is_char_boundary(bytes, index)]
        #![trigger decode_utf8(bytes.subrange(index, bytes.len() as int)), is_char_boundary(bytes, index)]
        decode_utf8(bytes) =~= decode_utf8(bytes.subrange(0, index)) + decode_utf8(
            bytes.subrange(index, bytes.len() as int),
        ),
    decreases index,
{
    if index == 0 {
        assert(bytes.subrange(index, bytes.len() as int) =~= bytes);
    } else {
        let first = bytes.subrange(0, index);
        let second = bytes.subrange(index, bytes.len() as int);
        is_char_boundary_len_first_scalar(bytes, index);
        valid_utf8_split(bytes, index);
        let bytes_tail = pop_first_scalar(bytes);
        let first_tail = pop_first_scalar(first);
        let bytes_head = decode_first_scalar(bytes) as char;
        let first_head = decode_first_scalar(first) as char;
        let new_index = (index - length_of_first_scalar(bytes)) as int;
        decode_utf8_split(bytes_tail, new_index);
        assert(second =~= bytes_tail.subrange(new_index, bytes_tail.len() as int));
        assert(first_tail =~= bytes_tail.subrange(0, new_index));
    }
}

proof fn is_char_boundary_len_first_scalar(bytes: Seq<u8>, index: int)
    requires
        valid_utf8(bytes),
        is_char_boundary(bytes, index),
    ensures
        index > 0 ==> index >= length_of_first_scalar(bytes),
{
    reveal_with_fuel(is_char_boundary, 2);
}

/// Ensures that the start and end of a valid UTF-8 byte sequence are character boundaries.
pub broadcast proof fn is_char_boundary_start_end_of_seq(bytes: Seq<u8>)
    requires
        valid_utf8(bytes),
    ensures
        #![trigger is_char_boundary(bytes, 0)]
        #![trigger is_char_boundary(bytes, bytes.len() as int)]
        is_char_boundary(bytes, 0),
        is_char_boundary(bytes, bytes.len() as int),
    decreases bytes.len(),
{
    if bytes.len() == 0 {
    } else {
        is_char_boundary_start_end_of_seq(pop_first_scalar(bytes));
    }
}

/// Ensures that any byte in a valid UTF-8 byte sequence falls on a character boundary (i.e. the first byte in a codepoint's encoding) if and only if it does not have the form of a UTF-8 continuation byte.
pub broadcast proof fn is_char_boundary_iff_not_is_continuation_byte(bytes: Seq<u8>, index: int)
    requires
        valid_utf8(bytes),
        0 <= index < bytes.len(),
    ensures
        #[trigger] is_char_boundary(bytes, index) <==> !(#[trigger] is_continuation_byte(
            bytes[index],
        )),
    decreases bytes.len(),
{
    if 0 <= index < length_of_first_scalar(bytes) {
        reveal_with_fuel(is_char_boundary, 2);
    } else {
        is_char_boundary_iff_not_is_continuation_byte(
            pop_first_scalar(bytes),
            index - length_of_first_scalar(bytes),
        );
    }
}

/// Ensures that any byte in a valid UTF-8 byte sequence falls on a character boundary (i.e. the first byte in a codepoint's encoding) if and only if it has the form of a UTF-8 leading byte.
pub broadcast proof fn is_char_boundary_iff_is_leading_byte(bytes: Seq<u8>, index: int)
    requires
        valid_utf8(bytes),
        0 <= index < bytes.len(),
    ensures
        #![trigger is_char_boundary(bytes, index), is_leading_byte_width_1(bytes[index])]
        #![trigger is_char_boundary(bytes, index), is_leading_byte_width_2(bytes[index])]
        #![trigger is_char_boundary(bytes, index), is_leading_byte_width_3(bytes[index])]
        #![trigger is_char_boundary(bytes, index), is_leading_byte_width_4(bytes[index])]
        is_char_boundary(bytes, index) <==> (is_leading_byte_width_1(bytes[index])
            || is_leading_byte_width_2(bytes[index]) || is_leading_byte_width_3(bytes[index])
            || is_leading_byte_width_4(bytes[index])),
    decreases bytes.len(),
{
    if 0 <= index < length_of_first_scalar(bytes) {
        reveal_with_fuel(is_char_boundary, 2);
    } else {
        is_char_boundary_iff_is_leading_byte(
            pop_first_scalar(bytes),
            index - length_of_first_scalar(bytes),
        );
    }
}

pub broadcast proof fn valid_utf8_last(s: Seq<u8>)
    requires
        valid_utf8(s),
        s.len() > 0,
    ensures
        #![trigger is_continuation_byte(s.last())]
        #![trigger is_leading_byte_width_1(s.last())]
        !is_continuation_byte(s.last()) ==> is_leading_byte_width_1(s.last()),
    decreases s.len(),
{
    // this proof must be discharged recursively, since valid_utf8 only tells you information
    // about the first codepoint and recurses from there
    let first = decode_first_scalar(s);
    let rest = pop_first_scalar(s);

    if rest.len() == 0 {
        if s.len() > 1 {
            assert(is_continuation_byte(s[s.len() - 1]));
        }
    } else {
        valid_utf8_last(rest);
    }
}

/* Bit-level reasoning */

/// Formulates the byte ranges for each type of byte in UTF-8 (leading and continuation) in terms of bitwise operators instead of ranges.
pub broadcast proof fn utf8_byte_ranges_bitwise(b: u8)
    by (bit_vector)
    ensures
        #![trigger b & 0x80]
        #![trigger b & 0xf0]
        #![trigger b & 0xf8]
        #![trigger b & 0xe0]
        #![trigger b & 0xc0]
        0x00 <= b <= 0x7f <==> b & 0x80 == 0,
        0xc0 <= b <= 0xdf <==> b & 0xe0 == 0xc0,
        0xe0 <= b <= 0xef <==> b & 0xf0 == 0xe0,
        0xf0 <= b <= 0xf7 <==> b & 0xf8 == 0xf0,
        0x80 <= b <= 0xbf <==> b & 0xc0 == 0x80,
{
}

/* ASCII */

/// True when the given character sequence only contains ASCII characters.
pub open spec fn is_ascii_chars(chars: Seq<char>) -> bool {
    forall|i| 0 <= i < chars.len() ==> '\0' <= #[trigger] chars[i] <= '\u{7f}'
}

/// Ensures that the UTF-8 encoding for an ASCII character sequence has the same length of the original sequence and corresponds byte-by-byte to the characters in the original sequence.
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
        assert(c0 as u8 == leading_byte_width_1(c0)) by (bit_vector)
            requires
                has_width_1_encoding(c0),
        ;
        is_ascii_chars_encode_utf8(chars.drop_first());
    }
}

/// Ensures that all characters in an ASCII character sequence have a numerical representation that falls in the range 0 (inclusive) to 128 (exclusive).
pub broadcast proof fn is_ascii_chars_nat_bound(chars: Seq<char>)
    ensures
        #[trigger] is_ascii_chars(chars) ==> forall|i: int|
            0 <= i < chars.len() ==> (chars.index(i) as nat) < 128,
{
}

/// Ensures that an ASCII character sequence is formed by the concatenation of two ASCII character sequences.
pub broadcast proof fn is_ascii_chars_concat(c1: Seq<char>, c2: Seq<char>, c3: Seq<char>)
    requires
        c1 =~= c2 + c3,
    ensures
        #![trigger c2 + c3, is_ascii_chars(c1), is_ascii_chars(c2), is_ascii_chars(c3)]
        is_ascii_chars(c1) <==> is_ascii_chars(c2) && is_ascii_chars(c3),
{
    if (is_ascii_chars(c1)) {
        assert(c2 =~= c1.subrange(0, c2.len() as int));
        assert(c3 =~= c1.subrange(c2.len() as int, c1.len() as int));
    }
}

pub broadcast group group_utf8_lib {
    encode_utf8_valid_utf8,
    encode_utf8_decode_utf8,
    decode_utf8_encode_utf8,
    char_is_scalar,
    char_u32_cast,
    valid_utf8_concat,
    partial_valid_utf8_extend,
    partial_valid_utf8_extend_ascii_block,
    valid_utf8_split,
    decode_utf8_split,
    is_char_boundary_start_end_of_seq,
    is_char_boundary_iff_not_is_continuation_byte,
    is_char_boundary_iff_is_leading_byte,
    valid_utf8_last,
    utf8_byte_ranges_bitwise,
    is_ascii_chars_encode_utf8,
    is_ascii_chars_nat_bound,
    is_ascii_chars_concat,
}

} // verus!
