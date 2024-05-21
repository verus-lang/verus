//! Conversions to/from bytes
#![allow(unused_imports)]

use super::pervasive::*;
use super::prelude::*;
use super::seq::*;
use super::seq_lib::*;
use super::slice::*;
use super::view::*;

verus! {

broadcast use group_seq_axioms;
// Conversion between u16 and little-endian byte sequences

pub closed spec fn spec_u16_to_le_bytes(x: u16) -> Seq<u8> {
    #[verusfmt::skip]
    seq![
        (x & 0xff) as u8,
        ((x >> 8) & 0xff) as u8
    ]
}

pub closed spec fn spec_u16_from_le_bytes(s: Seq<u8>) -> u16
    recommends
        s.len() == 2,
{
    (s[0] as u16) | (s[1] as u16) << 8
}

#[verifier::spinoff_prover]
pub proof fn lemma_auto_spec_u16_to_from_le_bytes()
    ensures
        forall|x: u16|
            {
                &&& #[trigger] spec_u16_to_le_bytes(x).len() == 2
                &&& spec_u16_from_le_bytes(spec_u16_to_le_bytes(x)) == x
            },
        forall|s: Seq<u8>|
            s.len() == 2 ==> #[trigger] spec_u16_to_le_bytes(spec_u16_from_le_bytes(s)) == s,
{
    assert forall|x: u16|
        {
            &&& #[trigger] spec_u16_to_le_bytes(x).len() == 2
            &&& spec_u16_from_le_bytes(spec_u16_to_le_bytes(x)) == x
        } by {
        let s = spec_u16_to_le_bytes(x);
        assert({
            &&& x & 0xff < 256
            &&& (x >> 8) & 0xff < 256
        }) by (bit_vector);
        #[verusfmt::skip]
        assert(x == (
        (x & 0xff) |
        ((x >> 8) & 0xff) << 8)
    ) by (bit_vector);
    };
    assert forall|s: Seq<u8>| s.len() == 2 implies #[trigger] spec_u16_to_le_bytes(
        spec_u16_from_le_bytes(s),
    ) == s by {
        let x = spec_u16_from_le_bytes(s);
        let s0 = s[0] as u16;
        let s1 = s[1] as u16;
        #[verusfmt::skip]
        assert(
        (
            (x == s0 | s1 << 8) &&
            (s0 < 256) &&
            (s1 < 256)
        ) ==>
            s0 == (x & 0xff) &&
            s1 == ((x >> 8) & 0xff)
    ) by (bit_vector);
        assert_seqs_equal!(spec_u16_to_le_bytes(spec_u16_from_le_bytes(s)) == s);
    }
}

#[verifier::external_body]
pub exec fn u16_from_le_bytes(s: &[u8]) -> (x: u16)
    requires
        s@.len() == 2,
    ensures
        x == spec_u16_from_le_bytes(s@),
{
    use core::convert::TryInto;
    u16::from_le_bytes(s.try_into().unwrap())
}

#[cfg(feature = "alloc")]
#[verifier::external_body]
pub exec fn u16_to_le_bytes(x: u16) -> (s: alloc::vec::Vec<u8>)
    ensures
        s@ == spec_u16_to_le_bytes(x),
        s@.len() == 2,
{
    x.to_le_bytes().to_vec()
}

// Conversion between u32 and little-endian byte sequences
pub closed spec fn spec_u32_to_le_bytes(x: u32) -> Seq<u8> {
    #[verusfmt::skip]
    seq![
        (x & 0xff) as u8,
        ((x >> 8) & 0xff) as u8,
        ((x >> 16) & 0xff) as u8,
        ((x >> 24) & 0xff) as u8,
    ]
}

pub closed spec fn spec_u32_from_le_bytes(s: Seq<u8>) -> u32
    recommends
        s.len() == 4,
{
    (s[0] as u32) | (s[1] as u32) << 8 | (s[2] as u32) << 16 | (s[3] as u32) << 24
}

pub proof fn lemma_auto_spec_u32_to_from_le_bytes()
    ensures
        forall|x: u32|
            {
                &&& #[trigger] spec_u32_to_le_bytes(x).len() == 4
                &&& spec_u32_from_le_bytes(spec_u32_to_le_bytes(x)) == x
            },
        forall|s: Seq<u8>|
            s.len() == 4 ==> #[trigger] spec_u32_to_le_bytes(spec_u32_from_le_bytes(s)) == s,
{
    assert forall|x: u32|
        {
            &&& #[trigger] spec_u32_to_le_bytes(x).len() == 4
            &&& spec_u32_from_le_bytes(spec_u32_to_le_bytes(x)) == x
        } by {
        let s = spec_u32_to_le_bytes(x);
        assert({
            &&& x & 0xff < 256
            &&& (x >> 8) & 0xff < 256
            &&& (x >> 16) & 0xff < 256
            &&& (x >> 24) & 0xff < 256
        }) by (bit_vector);
        #[verusfmt::skip]
        assert(x == (
        (x & 0xff) |
        ((x >> 8) & 0xff) << 8 |
        ((x >> 16) & 0xff) << 16 |
        ((x >> 24) & 0xff) << 24)
    ) by (bit_vector);
    };
    assert forall|s: Seq<u8>| s.len() == 4 implies #[trigger] spec_u32_to_le_bytes(
        spec_u32_from_le_bytes(s),
    ) == s by {
        let x = spec_u32_from_le_bytes(s);
        let s0 = s[0] as u32;
        let s1 = s[1] as u32;
        let s2 = s[2] as u32;
        let s3 = s[3] as u32;
        #[verusfmt::skip]
        assert(
        (
            (x == s0 | s1 << 8 | s2 << 16 | s3 << 24) &&
            (s0 < 256) &&
            (s1 < 256) &&
            (s2 < 256) &&
            (s3 < 256)
        ) ==>
            s0 == (x & 0xff) &&
            s1 == ((x >> 8) & 0xff) &&
            s2 == ((x >> 16) & 0xff) &&
            s3 == ((x >> 24) & 0xff)
    ) by (bit_vector);
        assert_seqs_equal!(spec_u32_to_le_bytes(spec_u32_from_le_bytes(s)) == s);
    }
}

#[verifier::external_body]
pub exec fn u32_from_le_bytes(s: &[u8]) -> (x: u32)
    requires
        s@.len() == 4,
    ensures
        x == spec_u32_from_le_bytes(s@),
{
    use core::convert::TryInto;
    u32::from_le_bytes(s.try_into().unwrap())
}

#[cfg(feature = "alloc")]
#[verifier::external_body]
pub exec fn u32_to_le_bytes(x: u32) -> (s: alloc::vec::Vec<u8>)
    ensures
        s@ == spec_u32_to_le_bytes(x),
        s@.len() == 4,
{
    x.to_le_bytes().to_vec()
}

// Conversion between u64 and little-endian byte sequences
pub closed spec fn spec_u64_to_le_bytes(x: u64) -> Seq<u8> {
    #[verusfmt::skip]
    seq![
        (x & 0xff) as u8,
        ((x >> 8) & 0xff) as u8,
        ((x >> 16) & 0xff) as u8,
        ((x >> 24) & 0xff) as u8,
        ((x >> 32) & 0xff) as u8,
        ((x >> 40) & 0xff) as u8,
        ((x >> 48) & 0xff) as u8,
        ((x >> 56) & 0xff) as u8,
    ]
}

pub closed spec fn spec_u64_from_le_bytes(s: Seq<u8>) -> u64
    recommends
        s.len() == 8,
{
    #[verusfmt::skip]
    (s[0] as u64) |
    (s[1] as u64) << 8 |
    (s[2] as u64) << 16 |
    (s[3] as u64) << 24 |
    (s[4] as u64) << 32 |
    (s[5] as u64) << 40 |
    (s[6] as u64) << 48 |
    (s[7] as u64) << 56
}

#[verifier::spinoff_prover]
pub proof fn lemma_auto_spec_u64_to_from_le_bytes()
    ensures
        forall|x: u64|
            #![trigger spec_u64_to_le_bytes(x)]
            {
                &&& spec_u64_to_le_bytes(x).len() == 8
                &&& spec_u64_from_le_bytes(spec_u64_to_le_bytes(x)) == x
            },
        forall|s: Seq<u8>|
            #![trigger spec_u64_to_le_bytes(spec_u64_from_le_bytes(s))]
            s.len() == 8 ==> spec_u64_to_le_bytes(spec_u64_from_le_bytes(s)) == s,
{
    assert forall|x: u64|
        {
            &&& #[trigger] spec_u64_to_le_bytes(x).len() == 8
            &&& spec_u64_from_le_bytes(spec_u64_to_le_bytes(x)) == x
        } by {
        let s = spec_u64_to_le_bytes(x);
        assert({
            &&& x & 0xff < 256
            &&& (x >> 8) & 0xff < 256
            &&& (x >> 16) & 0xff < 256
            &&& (x >> 24) & 0xff < 256
            &&& (x >> 32) & 0xff < 256
            &&& (x >> 40) & 0xff < 256
            &&& (x >> 48) & 0xff < 256
            &&& (x >> 56) & 0xff < 256
        }) by (bit_vector);
        #[verusfmt::skip]
        assert(x == (
        (x & 0xff) |
        ((x >> 8) & 0xff) << 8 |
        ((x >> 16) & 0xff) << 16 |
        ((x >> 24) & 0xff) << 24 |
        ((x >> 32) & 0xff) << 32 |
        ((x >> 40) & 0xff) << 40 |
        ((x >> 48) & 0xff) << 48 |
        ((x >> 56) & 0xff) << 56)
    ) by (bit_vector);
    };
    assert forall|s: Seq<u8>| s.len() == 8 implies #[trigger] spec_u64_to_le_bytes(
        spec_u64_from_le_bytes(s),
    ) == s by {
        let x = spec_u64_from_le_bytes(s);
        let s0 = s[0] as u64;
        let s1 = s[1] as u64;
        let s2 = s[2] as u64;
        let s3 = s[3] as u64;
        let s4 = s[4] as u64;
        let s5 = s[5] as u64;
        let s6 = s[6] as u64;
        let s7 = s[7] as u64;
        #[verusfmt::skip]
        assert(
        (
            (x == s0 | s1 << 8 | s2 << 16 | s3 << 24 | s4 << 32 | s5 << 40 | s6 << 48 | s7 << 56) &&
            (s0 < 256) &&
            (s1 < 256) &&
            (s2 < 256) &&
            (s3 < 256) &&
            (s4 < 256) &&
            (s5 < 256) &&
            (s6 < 256) &&
            (s7 < 256)
        ) ==>
            s0 == (x & 0xff) &&
            s1 == ((x >> 8) & 0xff) &&
            s2 == ((x >> 16) & 0xff) &&
            s3 == ((x >> 24) & 0xff) &&
            s4 == ((x >> 32) & 0xff) &&
            s5 == ((x >> 40) & 0xff) &&
            s6 == ((x >> 48) & 0xff) &&
            s7 == ((x >> 56) & 0xff)
    ) by (bit_vector);
        assert_seqs_equal!(spec_u64_to_le_bytes(spec_u64_from_le_bytes(s)) == s);
    }
}

#[verifier::external_body]
pub exec fn u64_from_le_bytes(s: &[u8]) -> (x: u64)
    requires
        s@.len() == 8,
    ensures
        x == spec_u64_from_le_bytes(s@),
{
    use core::convert::TryInto;
    u64::from_le_bytes(s.try_into().unwrap())
}

#[cfg(feature = "alloc")]
#[verifier::external_body]
pub exec fn u64_to_le_bytes(x: u64) -> (s: alloc::vec::Vec<u8>)
    ensures
        s@ == spec_u64_to_le_bytes(x),
        s@.len() == 8,
{
    x.to_le_bytes().to_vec()
}

// Conversion between u128 and little-endian byte sequences
pub closed spec fn spec_u128_to_le_bytes(x: u128) -> Seq<u8> {
    #[verusfmt::skip]
    seq![
        (x & 0xff) as u8,
        ((x >> 8) & 0xff) as u8,
        ((x >> 16) & 0xff) as u8,
        ((x >> 24) & 0xff) as u8,
        ((x >> 32) & 0xff) as u8,
        ((x >> 40) & 0xff) as u8,
        ((x >> 48) & 0xff) as u8,
        ((x >> 56) & 0xff) as u8,
        ((x >> 64) & 0xff) as u8,
        ((x >> 72) & 0xff) as u8,
        ((x >> 80) & 0xff) as u8,
        ((x >> 88) & 0xff) as u8,
        ((x >> 96) & 0xff) as u8,
        ((x >> 104) & 0xff) as u8,
        ((x >> 112) & 0xff) as u8,
        ((x >> 120) & 0xff) as u8,
    ]
}

pub closed spec fn spec_u128_from_le_bytes(s: Seq<u8>) -> u128
    recommends
        s.len() == 16,
{
    #[verusfmt::skip]
    (s[0] as u128) |
    (s[1] as u128) << 8 |
    (s[2] as u128) << 16 |
    (s[3] as u128) << 24 |
    (s[4] as u128) << 32 |
    (s[5] as u128) << 40 |
    (s[6] as u128) << 48 |
    (s[7] as u128) << 56 |
    (s[8] as u128) << 64 |
    (s[9] as u128) << 72 |
    (s[10] as u128) << 80 |
    (s[11] as u128) << 88 |
    (s[12] as u128) << 96 |
    (s[13] as u128) << 104 |
    (s[14] as u128) << 112 |
    (s[15] as u128) << 120
}

#[verifier::spinoff_prover]
pub proof fn lemma_auto_spec_u128_to_from_le_bytes()
    ensures
        forall|x: u128|
            {
                &&& #[trigger] spec_u128_to_le_bytes(x).len() == 16
                &&& spec_u128_from_le_bytes(spec_u128_to_le_bytes(x)) == x
            },
        forall|s: Seq<u8>|
            s.len() == 16 ==> #[trigger] spec_u128_to_le_bytes(spec_u128_from_le_bytes(s)) == s,
{
    assert forall|x: u128|
        {
            &&& #[trigger] spec_u128_to_le_bytes(x).len() == 16
            &&& spec_u128_from_le_bytes(spec_u128_to_le_bytes(x)) == x
        } by {
        let s = spec_u128_to_le_bytes(x);
        assert({
            &&& x & 0xff < 256
            &&& (x >> 8) & 0xff < 256
            &&& (x >> 16) & 0xff < 256
            &&& (x >> 24) & 0xff < 256
            &&& (x >> 32) & 0xff < 256
            &&& (x >> 40) & 0xff < 256
            &&& (x >> 48) & 0xff < 256
            &&& (x >> 56) & 0xff < 256
            &&& (x >> 64) & 0xff < 256
            &&& (x >> 72) & 0xff < 256
            &&& (x >> 80) & 0xff < 256
            &&& (x >> 88) & 0xff < 256
            &&& (x >> 96) & 0xff < 256
            &&& (x >> 104) & 0xff < 256
            &&& (x >> 112) & 0xff < 256
            &&& (x >> 120) & 0xff < 256
        }) by (bit_vector);
        #[verusfmt::skip]
        assert(x == (
        (x & 0xff) |
        ((x >> 8) & 0xff) << 8 |
        ((x >> 16) & 0xff) << 16 |
        ((x >> 24) & 0xff) << 24 |
        ((x >> 32) & 0xff) << 32 |
        ((x >> 40) & 0xff) << 40 |
        ((x >> 48) & 0xff) << 48 |
        ((x >> 56) & 0xff) << 56 |
        ((x >> 64) & 0xff) << 64 |
        ((x >> 72) & 0xff) << 72 |
        ((x >> 80) & 0xff) << 80 |
        ((x >> 88) & 0xff) << 88 |
        ((x >> 96) & 0xff) << 96 |
        ((x >> 104) & 0xff) << 104 |
        ((x >> 112) & 0xff) << 112 |
        ((x >> 120) & 0xff) << 120)
    ) by (bit_vector);
    };
    assert forall|s: Seq<u8>| s.len() == 16 implies #[trigger] spec_u128_to_le_bytes(
        spec_u128_from_le_bytes(s),
    ) == s by {
        let x = spec_u128_from_le_bytes(s);
        let s0 = s[0] as u128;
        let s1 = s[1] as u128;
        let s2 = s[2] as u128;
        let s3 = s[3] as u128;
        let s4 = s[4] as u128;
        let s5 = s[5] as u128;
        let s6 = s[6] as u128;
        let s7 = s[7] as u128;
        let s8 = s[8] as u128;
        let s9 = s[9] as u128;
        let s10 = s[10] as u128;
        let s11 = s[11] as u128;
        let s12 = s[12] as u128;
        let s13 = s[13] as u128;
        let s14 = s[14] as u128;
        let s15 = s[15] as u128;
        #[verusfmt::skip]
        assert(
        (
            (x == s0 | s1 << 8 | s2 << 16 | s3 << 24 | s4 << 32
                     | s5 << 40 | s6 << 48 | s7 << 56 | s8 << 64
                     | s9 << 72 | s10 << 80 | s11 << 88 | s12 << 96
                     | s13 << 104 | s14 << 112 | s15 << 120) &&
            (s0 < 256) &&
            (s1 < 256) &&
            (s2 < 256) &&
            (s3 < 256) &&
            (s4 < 256) &&
            (s5 < 256) &&
            (s6 < 256) &&
            (s7 < 256) &&
            (s8 < 256) &&
            (s9 < 256) &&
            (s10 < 256) &&
            (s11 < 256) &&
            (s12 < 256) &&
            (s13 < 256) &&
            (s14 < 256) &&
            (s15 < 256)
        ) ==>
            s0 == (x & 0xff) &&
            s1 == ((x >> 8) & 0xff) &&
            s2 == ((x >> 16) & 0xff) &&
            s3 == ((x >> 24) & 0xff) &&
            s4 == ((x >> 32) & 0xff) &&
            s5 == ((x >> 40) & 0xff) &&
            s6 == ((x >> 48) & 0xff) &&
            s7 == ((x >> 56) & 0xff) &&
            s8 == ((x >> 64) & 0xff) &&
            s9 == ((x >> 72) & 0xff) &&
            s10 == ((x >> 80) & 0xff) &&
            s11 == ((x >> 88) & 0xff) &&
            s12 == ((x >> 96) & 0xff) &&
            s13 == ((x >> 104) & 0xff) &&
            s14 == ((x >> 112) & 0xff) &&
            s15 == ((x >> 120) & 0xff)
    ) by (bit_vector);
        assert_seqs_equal!(spec_u128_to_le_bytes(spec_u128_from_le_bytes(s)) == s);
    }
}

#[verifier::external_body]
pub exec fn u128_from_le_bytes(s: &[u8]) -> (x: u128)
    requires
        s@.len() == 16,
    ensures
        x == spec_u128_from_le_bytes(s@),
{
    use core::convert::TryInto;
    u128::from_le_bytes(s.try_into().unwrap())
}

#[cfg(feature = "alloc")]
#[verifier::external_body]
pub exec fn u128_to_le_bytes(x: u128) -> (s: alloc::vec::Vec<u8>)
    ensures
        s@ == spec_u128_to_le_bytes(x),
        s@.len() == 16,
{
    x.to_le_bytes().to_vec()
}

} // verus!
