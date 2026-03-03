use super::prelude::*;
use super::seq::*;

verus! {

broadcast use super::seq::group_seq_axioms;

/* Decoding UTF-8 to chars */

/// True when the given byte conforms to the bit pattern for the first byte of a 1-byte UTF-8 encoding.
/// The byte must have the form 0xxxxxxx.
pub open spec fn is_leading_byte_width_1(byte: u8) -> bool {
    0x00 <= byte <= 0x7f
}

/// True when the given byte conforms to the bit pattern for the first byte of a 2-byte UTF-8 encoding.
/// The byte must have the form 110xxxxx.
pub open spec fn is_leading_byte_width_2(byte: u8) -> bool {
    0xc0 <= byte <= 0xdf
}

/// True when the given byte conforms to the bit pattern for the first byte of a 3-byte UTF-8 encoding.
/// The byte must have the form 1110xxxx.
pub open spec fn is_leading_byte_width_3(byte: u8) -> bool {
    0xe0 <= byte <= 0xef
}

/// True when the given byte conforms to the bit pattern for the first byte of a 4-byte UTF-8 encoding.
/// The byte must have the form 11110xxx.
pub open spec fn is_leading_byte_width_4(byte: u8) -> bool {
    0xf0 <= byte <= 0xf7
}

/// True when the given byte conforms to the bit pattern for a continuation byte of a UTF-8 encoding.
/// The byte must have the form 10xxxxxx.
pub open spec fn is_continuation_byte(byte: u8) -> bool {
    0x80 <= byte <= 0xbf
}

/// Value of the 6 data bits from the given continuation byte.
pub open spec fn continuation_bits(byte: u8) -> u32
    recommends
        is_continuation_byte(byte),
{
    // 0x3f = 0011 1111
    (byte & 0x3f) as u32
}

/// Value of the 7 data bits from the given byte, which is the first (and only) byte in a 1-byte UTF-8 encoding.
pub open spec fn leading_bits_width_1(byte: u8) -> u32
    recommends
        is_leading_byte_width_1(byte),
{
    // 0x7f = 0111 1111
    (byte & 0x7F) as u32
}

/// Value of the 5 data bits from the given byte, which is the first byte in a 2-byte UTF-8 encoding.
pub open spec fn leading_bits_width_2(byte: u8) -> u32
    recommends
        is_leading_byte_width_2(byte),
{
    // 0x1f = 0001 1111
    (byte & 0x1F) as u32
}

/// Value of the 4 data bits from the given byte, which is the first byte in a 3-byte UTF-8 encoding.
pub open spec fn leading_bits_width_3(byte: u8) -> u32
    recommends
        is_leading_byte_width_3(byte),
{
    // 0x0f = 0000 1111
    (byte & 0x0F) as u32
}

/// Value of the 3 data bits from the given byte, which is the first byte in a 4-byte UTF-8 encoding.
pub open spec fn leading_bits_width_4(byte: u8) -> u32
    recommends
        is_leading_byte_width_4(byte),
{
    // 0x07 = 0000 0111
    (byte & 0x07) as u32
}

/// The codepoint encoded in UTF-8 by the given byte.
pub open spec fn codepoint_of_bytes_width_1(byte1: u8) -> u32
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
/// The codepoint encoded in UTF-8 by the given 2 bytes.
pub open spec fn codepoint_of_bytes_width_2(byte1: u8, byte2: u8) -> u32
    recommends
        is_leading_byte_width_2(byte1),
        is_continuation_byte(byte2),
{
    (leading_bits_width_2(byte1) << 6) | continuation_bits(byte2)
}

/// The codepoint encoded in UTF-8 by the given 3 bytes.
pub open spec fn codepoint_of_bytes_width_3(byte1: u8, byte2: u8, byte3: u8) -> u32
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
/// The codepoint encoded in UTF-8 by the given 4 bytes.
pub open spec fn codepoint_of_bytes_width_4(byte1: u8, byte2: u8, byte3: u8, byte4: u8) -> u32
    recommends
        is_leading_byte_width_4(byte1),
        is_continuation_byte(byte2),
        is_continuation_byte(byte3),
        is_continuation_byte(byte4),
{
    (leading_bits_width_4(byte1) << 18) | (continuation_bits(byte2) << 12) | (continuation_bits(byte3) << 6) | continuation_bits(
        byte4,
    )
}

/// True when the given byte sequence begins with a well-formed leading byte and an appropriate number of well-formed continuation bytes.
pub open spec fn valid_first_leading_and_continuation_bytes(bytes: Seq<u8>) -> bool {
    ||| (bytes.len() >= 1 && is_leading_byte_width_1(bytes[0]))
    ||| (bytes.len() >= 2 && is_leading_byte_width_2(bytes[0]) && is_continuation_byte(bytes[1]))
    ||| (bytes.len() >= 3 && is_leading_byte_width_3(bytes[0]) && is_continuation_byte(bytes[1]) && is_continuation_byte(bytes[2]))
    ||| (bytes.len() >= 4 && is_leading_byte_width_4(bytes[0]) && is_continuation_byte(bytes[1]) && is_continuation_byte(bytes[2]) && is_continuation_byte(bytes[3]))
}
 
/// The first codepoint in the given byte sequence, which begins with a well-formed leading byte and continuation bytes.
pub open spec fn first_codepoint(bytes: Seq<u8>) -> u32
    recommends
        valid_first_leading_and_continuation_bytes(bytes),
{
    if is_leading_byte_width_1(bytes[0]) {
        codepoint_of_bytes_width_1(bytes[0])
    } else if is_leading_byte_width_2(bytes[0]) {
        codepoint_of_bytes_width_2(bytes[0], bytes[1])
    } else if is_leading_byte_width_3(bytes[0]) {
        codepoint_of_bytes_width_3(bytes[0], bytes[1], bytes[2])
    } else {
        codepoint_of_bytes_width_4(bytes[0], bytes[1], bytes[2], bytes[3])
    }
}

/// Length in bytes of first codepoint in the given byte sequence, which begins with a well-formed leading byte and continuation bytes.
pub open spec fn length_of_first_codepoint(bytes: Seq<u8>) -> int
    recommends
        valid_first_leading_and_continuation_bytes(bytes)
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

// True when the given codepoint, when encoded in UTF-8 using `len` number of bytes, would not be an "overlong encoding".
pub open spec fn not_overlong_encoding(codepoint: u32, len: int) -> bool {
    &&& (len == 2 ==> 0x80 <= codepoint) 
    &&& (len == 3 ==> 0x800 <= codepoint) 
    &&& (len == 4 ==> 0x10000 <= codepoint <= 0x10ffff)
}

/// True when the given codepoint does not fall into the "surrogate range" of the UTF-8 standard.
pub open spec fn not_surrogate(codepoint: u32) -> bool {
    !(0xD800 <= codepoint <= 0xDFFF)
}

/// True when the given byte sequence begins with a well-formed UTF-8 encoding of a single scalar.
pub open spec fn valid_first_scalar(bytes: Seq<u8>) -> bool
    recommends
        bytes.len() > 0,
{
    &&& valid_first_leading_and_continuation_bytes(bytes) 
    &&& not_overlong_encoding(
        first_codepoint(bytes),
        length_of_first_codepoint(bytes),
    )
    &&& not_surrogate(first_codepoint(bytes))
}

/// The first scalar in the given byte sequence, which begins with a single UTF-8 scalar encoding.
pub open spec fn first_scalar(bytes: Seq<u8>) -> u32
    recommends
        valid_first_scalar(bytes),
{
    first_codepoint(bytes)
}

/// Length in bytes of first scalar in the given byte sequence, which begins with a single UTF-8 scalar encoding.
pub open spec fn length_of_first_scalar(bytes: Seq<u8>) -> int
    recommends
        valid_first_scalar(bytes)
{
    length_of_first_codepoint(bytes)
}

proof fn lemma_pop_first_scalar_decreases(bytes: Seq<u8>)
    requires
        valid_first_scalar(bytes),
    ensures
        pop_first_scalar(bytes).len() < bytes.len(),
{
    assert(length_of_first_scalar(bytes) <= bytes.len() as int);
    assert(pop_first_scalar(bytes).len() == bytes.len() as int - length_of_first_scalar(
        bytes,
    )) by { axiom_seq_subrange_len(bytes, length_of_first_scalar(bytes), bytes.len() as int) };
}

/// Remove the first scalar from the given byte sequence, which begins with a single UTF-8 scalar encoding, and return the remainder.
pub open spec fn pop_first_scalar(bytes: Seq<u8>) -> Seq<u8>
    recommends
        valid_first_scalar(bytes),
{
    bytes.subrange(
        length_of_first_scalar(bytes),
        bytes.len() as int,
    )
}

/// Take only the first scalar from the given byte sequence, which begins with a single UTF-8 scalar encoding.
pub open spec fn take_first_scalar(bytes: Seq<u8>) -> Seq<u8>
    recommends
        valid_first_scalar(bytes),
{
    bytes.subrange(0, length_of_first_scalar(bytes))
}

/// True when the given bytes form a valid UTF-8 byte sequence.
pub open spec fn valid_utf8(bytes: Seq<u8>) -> bool
    decreases bytes.len(),
{
    bytes.len() != 0 ==> valid_first_scalar(bytes) && valid_utf8(pop_first_scalar(bytes))
}

/// Interpretation of a UTF-8 byte sequence as a sequence of unicode scalars.
pub open spec fn decode_utf8(bytes: Seq<u8>) -> Seq<char>
    recommends
        valid_utf8(bytes),
    decreases bytes.len(),
    when valid_utf8(bytes)
{
    if bytes.len() == 0 {
        seq![]
    } else {
        seq![first_scalar(bytes) as char] + decode_utf8(pop_first_scalar(bytes))
    }
}

/* Encoding chars as UTF-8 */

/// True when the given scalar value has a 1-byte UTF-8 encoding.
pub open spec fn has_width_1_encoding(scalar: u32) -> bool {
    0 <= scalar <= 0x7F
}

/// True when the given scalar value has a 2-byte UTF-8 encoding.
pub open spec fn has_width_2_encoding(scalar: u32) -> bool {
    0x80 <= scalar <= 0x7FF
}

/// True when the given scalar value has a 3-byte UTF-8 encoding.
pub open spec fn has_width_3_encoding(scalar: u32) -> bool {
    0x800 <= scalar <= 0xFFFF && !(0xD800 <= scalar <= 0xDFFF)
}

/// True when the given scalar value has a 4-byte UTF-8 encoding.
pub open spec fn has_width_4_encoding(scalar: u32) -> bool {
    0x10000 <= scalar <= 0x10FFFF
}

/// The first (and only) byte of the UTF-8 encoding of the given scalar value, which has a 1-byte UTF-8 encoding.
pub open spec fn leading_byte_width_1(scalar: u32) -> u8
    recommends
        has_width_1_encoding(scalar),
{
    (scalar & 0x7F) as u8
}

/// The first byte of the UTF-8 encoding of the given scalar value, which has a 2-byte UTF-8 encoding.
pub open spec fn leading_byte_width_2(scalar: u32) -> u8
    recommends
        has_width_2_encoding(scalar),
{
    0xC0 | ((scalar >> 6) & 0x1F) as u8
}

/// The first byte of the UTF-8 encoding of the given scalar value, which has a 3-byte UTF-8 encoding.
pub open spec fn leading_byte_width_3(scalar: u32) -> u8
    recommends
        has_width_3_encoding(scalar),
{
    0xE0 | ((scalar >> 12) & 0x0F) as u8
}

/// The first byte of the UTF-8 encoding of the given scalar value, which has a 4-byte UTF-8 encoding.
pub open spec fn leading_byte_width_4(scalar: u32) -> u8
    recommends
        has_width_4_encoding(scalar),
{
    0xF0 | ((scalar >> 18) & 0x7) as u8
}

/// The last continuation byte of the UTF-8 encoding of the given scalar value, which has a 2, 3, or 4-byte UTF-8 encoding.
pub open spec fn last_continuation_byte(scalar: u32) -> u8
    recommends
        has_width_2_encoding(scalar) || has_width_3_encoding(scalar) || has_width_4_encoding(scalar),
{
    0x80 | (scalar & 0x3F) as u8
}

/// The second-to-last continuation byte of the UTF-8 encoding of the given scalar value, which has a 3 or 4-byte UTF-8 encoding.
pub open spec fn second_last_continuation_byte(scalar: u32) -> u8
    recommends
        has_width_3_encoding(scalar) || has_width_4_encoding(scalar),
{
    0x80 | ((scalar >> 6) & 0x3F) as u8
}

/// The third-to-last continuation byte of the UTF-8 encoding of the given scalar value, which has a 4-byte UTF-8 encoding.
pub open spec fn third_last_continuation_byte(scalar: u32) -> u8
    recommends
        has_width_4_encoding(scalar),
{
    0x80 | ((scalar >> 12) & 0x3F) as u8
}

/// True when the given `u32` can be encoded in UTF-8.
pub open spec fn valid_scalar(scalar: u32) -> bool {
    0 <= scalar <= 0x10ffff && !(0xD800 <= scalar <= 0xDFFF)
}

/// Converts a scalar value to its UTF-8 representation.
pub open spec fn encoding_of_scalar(scalar: u32) -> Seq<u8>
    recommends
        valid_scalar(scalar),
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

/// Converts a sequence of `char`s to the corresponding UTF-8 representation.
pub open spec fn encode_utf8(chars: Seq<char>) -> Seq<u8>
    decreases chars.len(),
{
    if chars.len() == 0 {
        seq![]
    } else {
        encoding_of_scalar(chars[0] as u32) + encode_utf8(chars.drop_first())
    }
}

/* Correspondence between encode_utf8 and decode_utf8 definitions */

proof fn encode_decode_width_1(c: u32)
    by (bit_vector)
    requires
        has_width_1_encoding(c),
    ensures
        ({
            let b1 = leading_byte_width_1(c);
            &&& is_leading_byte_width_1(b1)
            &&& codepoint_of_bytes_width_1(b1) == c
        }),
{
}

proof fn decode_encode_width_1(b1: u8)
    by (bit_vector)
    requires
        is_leading_byte_width_1(b1),
    ensures
        ({
            let c = codepoint_of_bytes_width_1(b1);
            &&& valid_scalar(c)
            &&& has_width_1_encoding(c)
            &&& leading_byte_width_1(c) == b1
        }),
{
}

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
            &&& codepoint_of_bytes_width_2(b1, b2) == c
        }),
{
}

proof fn decode_encode_width_2(b1: u8, b2: u8)
    by (bit_vector)
    requires
        is_leading_byte_width_2(b1),
        is_continuation_byte(b2),
        not_overlong_encoding(codepoint_of_bytes_width_2(b1, b2), 2),
    ensures
        ({
            let c = codepoint_of_bytes_width_2(b1, b2);
            &&& valid_scalar(c)
            &&& has_width_2_encoding(c)
            &&& leading_byte_width_2(c) == b1
            &&& last_continuation_byte(c) == b2
        }),
{
}

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
            &&& codepoint_of_bytes_width_3(b1, b2, b3) == c
        }),
{
}

proof fn decode_encode_width_3(b1: u8, b2: u8, b3: u8)
    by (bit_vector)
    requires
        is_leading_byte_width_3(b1),
        is_continuation_byte(b2),
        is_continuation_byte(b3),
        not_overlong_encoding(codepoint_of_bytes_width_3(b1, b2, b3), 3),
        not_surrogate(codepoint_of_bytes_width_3(b1, b2, b3))
    ensures
        ({
            let c = codepoint_of_bytes_width_3(b1, b2, b3);
            &&& valid_scalar(c)
            &&& has_width_3_encoding(c)
            &&& leading_byte_width_3(c) == b1
            &&& second_last_continuation_byte(c) == b2
            &&& last_continuation_byte(c) == b3
        }),
{
}

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
            &&& codepoint_of_bytes_width_4(b1, b2, b3, b4) == c
        }),
{
}

proof fn decode_encode_width_4(b1: u8, b2: u8, b3: u8, b4: u8)
    by (bit_vector)
    requires
        is_leading_byte_width_4(b1),
        is_continuation_byte(b2),
        is_continuation_byte(b3),
        is_continuation_byte(b4),
        not_overlong_encoding(codepoint_of_bytes_width_4(b1, b2, b3, b4), 4),
    ensures
        ({
            let c = codepoint_of_bytes_width_4(b1, b2, b3, b4);
            &&& valid_scalar(c)
            &&& has_width_4_encoding(c)
            &&& leading_byte_width_4(c) == b1
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

/// Properties of the first scalar from the result of `encode_utf8`.
pub proof fn encode_utf8_first_scalar(chars: Seq<char>)
    requires
        chars.len() > 0,
    ensures
        first_scalar(encode_utf8(chars)) == chars[0] as u32,
        length_of_first_scalar(encode_utf8(chars)) == encoding_of_scalar(chars[0] as u32).len(),
        valid_first_scalar(encode_utf8(chars)),
{
    char_is_valid_scalar(chars[0]);
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

/// Ensures the result of `encode_utf8` always satisfies `valid_utf8`.
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

/// Ensures that performing `encode_utf8` followed by `decode_utf8` results in the original `char` sequence.
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
        char_u32_cast(chars[0], first_scalar(bytes));

        assert(pop_first_scalar(bytes) =~= encode_utf8(chars.drop_first()));
        let rest = chars.drop_first();
        encode_utf8_decode_utf8(rest);
    }
}

/// Properties of the first scalar from the result of `decode_utf8`.
pub proof fn decode_utf8_first_scalar(bytes: Seq<u8>)
    requires
        valid_utf8(bytes),
        bytes.len() > 0,
    ensures
        encoding_of_scalar((first_scalar(bytes) as char) as u32) == take_first_scalar(
            bytes,
        ),
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

/// Ensures that performing `decode_utf8` followed by `encode_utf8` results in the original byte sequence.
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
        let first = first_scalar(bytes) as char;
        let rest = pop_first_scalar(bytes);

        char_is_valid_scalar(first);
        assert(encoding_of_scalar(first as u32) == take_first_scalar(bytes)) by {
            decode_utf8_first_scalar(bytes);
        }

        assert(chars.drop_first() =~= decode_utf8(rest));
        decode_utf8_encode_utf8(rest);
    }
}

/* Partial UTF-8 sequences */

pub open spec fn partial_valid_utf8(bytes: Seq<u8>, i: int) -> bool {
    0 <= i <= bytes.len() && valid_utf8(bytes.subrange(0, i))
}

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
        } else {
        }
    }
}

pub proof fn partial_valid_utf8_split(b1: Seq<u8>, b2: Seq<u8>)
    requires
        valid_utf8(b1),
        valid_utf8(b2),
    ensures
        valid_utf8(b1 + b2),
    decreases b1.len(),
{
    if b1.len() == 0 {
        assert(b1 + b2 == b2) by { Seq::add_empty_left(b1, b2) };
        assert(valid_utf8(b1 + b2));
    } else {
        let rest = pop_first_scalar(b1);
        // so valid_utf8(b1) implies valid_utf8(rest)?
        assert(pop_first_scalar(b1).len() < b1.len()) by {
            lemma_pop_first_scalar_decreases(b1)
        };
        partial_valid_utf8_split(rest, b2);
        // now know valid_utf8(rest+b2)
        assert(pop_first_scalar(b1 + b2) =~= rest + b2);
        assert(valid_utf8(b1 + b2));
    }
}

pub proof fn partial_valid_utf8_extend(bytes: Seq<u8>, i: int)
    requires
        partial_valid_utf8(bytes, i),
        valid_first_scalar(bytes.subrange(i, bytes.len() as int)),
    ensures
        partial_valid_utf8(
            bytes,
            i + length_of_first_scalar(bytes.subrange(i, bytes.len() as int)),
        ),
{
    reveal_with_fuel(valid_utf8, 2);
    let scalar = bytes.subrange(
        i,
        i + length_of_first_scalar(bytes.subrange(i, bytes.len() as int)),
    );
    partial_valid_utf8_split(bytes.subrange(0, i), scalar);
    assert(bytes.subrange(0, i) + scalar =~= bytes.subrange(
        0,
        i + length_of_first_scalar(bytes.subrange(i, bytes.len() as int)),
    ));
}

/* Reasoning about character boundaries */

/// True when the index into the UTF-8 byte sequence falls on a character boundary.
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

proof fn is_char_boundary_len_first_scalar(bytes: Seq<u8>, index: int)
    requires
        valid_utf8(bytes),
        is_char_boundary(bytes, index),
    ensures
        index > 0 ==> index >= length_of_first_scalar(bytes),
{
    reveal_with_fuel(is_char_boundary, 2);
}

pub proof fn is_char_boundary_start_end_of_seq(bytes: Seq<u8>)
    requires
        valid_utf8(bytes)
    ensures
        is_char_boundary(bytes, 0),
        is_char_boundary(bytes, bytes.len() as int)
    decreases
        bytes.len()
{
    if bytes.len() == 0 {
    } else {
        is_char_boundary_start_end_of_seq(pop_first_scalar(bytes));
    }
}

pub proof fn is_char_boundary_iff_not_is_continuation_byte(bytes: Seq<u8>, index: int) 
    requires
        valid_utf8(bytes),
        0 <= index < bytes.len()
    ensures
        is_char_boundary(bytes, index) <==> !is_continuation_byte(bytes[index])
    decreases
        bytes.len()
{
    if 0 <= index < length_of_first_scalar(bytes) {
        reveal_with_fuel(is_char_boundary, 2);
    } else {
        is_char_boundary_iff_not_is_continuation_byte(pop_first_scalar(bytes), index - length_of_first_scalar(bytes));
    } 
}

pub proof fn is_char_boundary_iff_is_leading_byte(bytes: Seq<u8>, index: int) 
    requires
        valid_utf8(bytes),
        0 <= index < bytes.len()
    ensures
        is_char_boundary(bytes, index) <==> (is_leading_byte_width_1(bytes[index]) || is_leading_byte_width_2(bytes[index]) || is_leading_byte_width_3(bytes[index]) || is_leading_byte_width_4(bytes[index]))
    decreases
        bytes.len()
{
    if 0 <= index < length_of_first_scalar(bytes) {
        reveal_with_fuel(is_char_boundary, 2);
    } else {
        is_char_boundary_iff_is_leading_byte(pop_first_scalar(bytes), index - length_of_first_scalar(bytes));
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

pub proof fn valid_utf8_split_char_boundary(bytes: Seq<u8>, index: int)
    requires
        valid_utf8(bytes),
        is_char_boundary(bytes, index),
    ensures
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
        valid_utf8_split_char_boundary(tail, new_offset);
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
            partial_valid_utf8_split(head, n1);
        }
        assert(s2 =~= n2);
    }
}

pub proof fn decode_utf8_split_char_boundary(bytes: Seq<u8>, index: int)
    requires
        valid_utf8(bytes),
        is_char_boundary(bytes, index)
    ensures
        decode_utf8(bytes) =~= decode_utf8(bytes.subrange(0, index)) + decode_utf8(bytes.subrange(index, bytes.len() as int)),
    decreases index,
{
    if index == 0 {
        assert(bytes.subrange(index, bytes.len() as int) =~= bytes);
    } else {
        let first = bytes.subrange(0, index);
        let second = bytes.subrange(index, bytes.len() as int);
        is_char_boundary_len_first_scalar(bytes, index);
        valid_utf8_split_char_boundary(bytes, index);
        let bytes_tail = pop_first_scalar(bytes);
        let first_tail = pop_first_scalar(first);
        let bytes_head = first_scalar(bytes) as char;
        let first_head = first_scalar(first) as char;
        let new_index = (index - length_of_first_scalar(bytes)) as int;
        decode_utf8_split_char_boundary(bytes_tail, new_index);
        assert(second =~= bytes_tail.subrange(new_index, bytes_tail.len() as int));
        assert(first_tail =~= bytes_tail.subrange(0, new_index));
    }
}

/* Bit-level reasoning */

pub broadcast proof fn utf8_char_width_ranges(b: u8)
    by (bit_vector)
    ensures
        #![trigger b & 0x80]
        #![trigger b & 0xf0]
        #![trigger b & 0xf8]
        #![trigger b & 0xe0]
        #![trigger b & 0x7f]
        0x00 <= b <= 0x7f <==> b & 0x80 == 0,
        0xc0 <= b <= 0xdf <==> b & 0xe0 == 0xc0,
        0xe0 <= b <= 0xef <==> b & 0xf0 == 0xe0,
        0xf0 <= b <= 0xf7 <==> b & 0xf8 == 0xf0,
        0x00 <= b < 0x80 <==> b & 0x7f == b,
{}

/* ASCII */

/// True when the given character sequence only contains ASCII characters.
pub open spec fn is_ascii_chars(chars: Seq<char>) -> bool {
    forall|i| 0 <= i < chars.len() ==> '\0' <= #[trigger] chars[i] <= '\x7f'
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
        assert(c0 as u8 == leading_byte_width_1(c0)) by (bit_vector)
            requires
                has_width_1_encoding(c0),
        ;
        is_ascii_chars_encode_utf8(chars.drop_first());
    }
}

pub broadcast proof fn is_ascii_chars_nat_bound(chars: Seq<char>)
    ensures
        #[trigger] is_ascii_chars(chars) ==> forall|i: int|
            0 <= i < chars.len() ==> (chars.index(i) as nat) < 128,
{
}

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

// todo - create broadcast group
} // verus!
