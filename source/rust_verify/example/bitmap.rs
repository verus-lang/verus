#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{prelude::*, seq::*, seq_lib::*};

macro_rules! get_bit64_macro {
    ($a:expr, $b:expr) => {{
        (0x1u64 & ($a >> $b)) == 1
    }};
}

// since this wraps with `verus_proof_macro_exprs`, should use the above `get_bit64_macro` if it is going to be executable.
macro_rules! get_bit64 {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(get_bit64_macro!($($a)*))
    }
}

macro_rules! set_bit64_macro {
    ($a:expr,$b:expr, $c:expr) => {{
        if $c {
            $a | 1u64 << $b
        } else {
            $a & (!(1u64 << $b))
        }
    }};
}

// since this wraps with `verus_proof_macro_exprs`, should use the above `set_bit64_macro` if it is going to be executable.
macro_rules! set_bit64 {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(set_bit64_macro!($($a)*))
    }
}

verus! {

spec fn u64_view(u: u64) -> Seq<bool> {
    Seq::new(64, |i: int| get_bit64!(u, i as u64))
}

#[verifier::bit_vector]
proof fn set_bit64_proof(bv_new: u64, bv_old: u64, index: u64, bit: bool)
    requires
        bv_new == set_bit64!(bv_old, index, bit),
        index < 64,
    ensures
        get_bit64!(bv_new, index) == bit,
        forall|loc2: u64|
            (loc2 < 64 && loc2 != index) ==> (get_bit64!(bv_new, loc2) == get_bit64!(bv_old, loc2)),
{
}

#[verifier::bit_vector]
proof fn bit_or_64_proof(bv1: u64, bv2: u64, bv_new: u64)
    requires
        bv_new == bv1 | bv2,
    ensures
        forall|i: u64|
            (i < 64) ==> get_bit64!(bv_new, i) == (get_bit64!(bv1, i) || get_bit64!(bv2, i)),
{
}

proof fn bit_or_64_view_proof(u1: u64, u2: u64, bv_new: u64)
    requires
        bv_new == u1 | u2,
    ensures
        u64_view(bv_new) =~= Seq::new(64, |i: int| u64_view(u1).index(i) || u64_view(u2).index(i)),
{
    bit_or_64_proof(u1, u2, bv_new);
}

spec fn or_u64_relation(u1: u64, u2: u64, or_int: u64) -> bool {
    u64_view(or_int) =~= Seq::new(64, |i: int| u64_view(u1).index(i) || u64_view(u2).index(i))
}

pub struct BitMap {
    bits: Vec<u64>,
}

impl BitMap {
    spec fn view(&self) -> Seq<bool> {
        let width = self.bits@.len() * 64;
        Seq::new(width, |i: int| u64_view(self.bits@[i / 64])[i % 64])
    }

    fn from(v: Vec<u64>) -> BitMap {
        BitMap { bits: v }
    }

    fn get_bit(&self, index: u32) -> (bit: bool)
        requires
            index < self@.len(),
        ensures
            bit == self@[index as int],
    {
        // REVIEW: at this moment, usize is assumed to be 32 or 64.
        // Therefore, if `index` is u64, verification fails due to the possibility of truncation
        // when we begin to consider `usize` smaller than 32, this might fail again.
        let seq_index: usize = (index / 64) as usize;
        let bit_index: u32 = index % 64;
        let bucket: u64 = self.bits[seq_index];
        get_bit64_macro!(bucket, bit_index as u64)
    }

    fn set_bit(&mut self, index: u32, bit: bool)
        requires
            index < old(self)@.len(),
        ensures
            self@ == old(self)@.update(index as int, bit),
    {
        // REVEIW: Same problem here with above regarding `usize`.
        let seq_index: usize = (index / 64) as usize;
        let bit_index: u32 = index % 64;
        let bv_old: u64 = self.bits[seq_index];
        let bv_new: u64 = set_bit64_macro!(bv_old, bit_index as u64, bit);
        proof {
            set_bit64_proof(bv_new, bv_old, bit_index as u64, bit);
        }
        ;
        self.bits.set(seq_index, bv_new);
        proof {
            assert_seqs_equal!(
                self.view(),
                old(self).view().update(index as int, bit)
            );
        }
        ;
    }

    // bitwise-OR for bitmap
    fn or(&self, bm: &BitMap) -> (ret: BitMap)
        requires
            self@.len() == bm@.len(),
        ensures
            self@.len() == ret@.len(),
            forall|i: int| 0 <= i < ret@.len() ==> ret@[i] == (self@[i] || bm@[i]),
    {
        let n: usize = self.bits.len();
        let mut i: usize = 0;
        let mut res_bits: Vec<u64> = Vec::new();
        let mut result = BitMap { bits: res_bits };
        while i < n
            invariant
                i <= n,
                n == self.bits@.len(),
                n == bm.bits@.len(),
                i == result.bits.len(),
                forall|k: int|
                    0 <= k < i ==> or_u64_relation(self.bits@[k], bm.bits@[k], result.bits@[k]),
                forall|k: int| 0 <= k < i * 64 ==> result@[k] == (self@[k] || bm@[k]),
        {
            res_bits = result.bits;
            let u1: u64 = self.bits[i];
            let u2: u64 = bm.bits[i];
            let or_int: u64 = u1 | u2;
            proof {
                bit_or_64_view_proof(u1, u2, or_int);
            }
            res_bits.push(or_int);
            result = BitMap { bits: res_bits };
            i = i + 1;
        }
        result
    }
}

} // verus!
#[verifier::external]
fn main() {}
