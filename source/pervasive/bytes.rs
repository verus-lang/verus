//! Conversions to/from bytes

#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;

use crate::pervasive::*;
use crate::view::*;
use crate::seq::*;
use crate::seq_lib::*;
use crate::slice::*;

verus! {

pub closed spec fn spec_u64_to_le_bytes(x: u64) -> Seq<u8>
{
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
  recommends s.len() == 8
{
  (s[0] as u64) |
  (s[1] as u64) << 8 |
  (s[2] as u64) << 16 |
  (s[3] as u64) << 24 |
  (s[4] as u64) << 32 |
  (s[5] as u64) << 40 |
  (s[6] as u64) << 48 |
  (s[7] as u64) << 56
}

pub proof fn lemma_auto_spec_u64_to_from_le_bytes()
  ensures
    forall |x: u64|
      #![trigger spec_u64_to_le_bytes(x)]
    {
      &&& spec_u64_to_le_bytes(x).len() == 8
      &&& spec_u64_from_le_bytes(spec_u64_to_le_bytes(x)) == x
    },
    forall |s: Seq<u8>|
      #![trigger spec_u64_to_le_bytes(spec_u64_from_le_bytes(s))]
      s.len() == 8 ==> spec_u64_to_le_bytes(spec_u64_from_le_bytes(s)) == s,
{
  assert forall |x: u64|  {
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

    assert(x == (
      (x & 0xff) |
      ((x >> 8) & 0xff) << 8 |
      ((x >> 16) & 0xff) << 16 |
      ((x >> 24) & 0xff) << 24 |
      ((x >> 32) & 0xff) << 32 |
      ((x >> 40) & 0xff) << 40 |
      ((x >> 48) & 0xff) << 48 |
      ((x >> 56) & 0xff) << 56)) by (bit_vector);
  };

  assert forall |s: Seq<u8>| s.len() == 8 implies #[trigger] spec_u64_to_le_bytes(spec_u64_from_le_bytes(s)) == s by {
    let x = spec_u64_from_le_bytes(s);
    let s0 = s[0] as u64;
    let s1 = s[1] as u64;
    let s2 = s[2] as u64;
    let s3 = s[3] as u64;
    let s4 = s[4] as u64;
    let s5 = s[5] as u64;
    let s6 = s[6] as u64;
    let s7 = s[7] as u64;

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
      s0 == (x & 0xff) && s1 == ((x >> 8) & 0xff) && s2 == ((x >> 16) & 0xff) && s3 == ((x >> 24) & 0xff) && s4 == ((x >> 32) & 0xff) && s5 == ((x >> 40) & 0xff) && s6 == ((x >> 48) & 0xff) && s7 == ((x >> 56) & 0xff)
    ) by (bit_vector);

    assert_seqs_equal!(spec_u64_to_le_bytes(spec_u64_from_le_bytes(s)) == s);
  }
}

#[verifier(external_body)]
pub exec fn u64_from_le_bytes(s: &[u8]) -> (x:u64)
  requires s@.len() == 8,
  ensures x == spec_u64_from_le_bytes(s@),
{
  use core::convert::TryInto;
  u64::from_le_bytes(s.try_into().unwrap())
}


#[verifier(external_body)]
pub exec fn u64_to_le_bytes(x: u64) -> (s: Vec<u8>)
  ensures s@ == spec_u64_to_le_bytes(x),
{
  x.to_le_bytes().to_vec()
}


} // verus!
