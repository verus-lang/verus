#![allow(unused_imports)]

use builtin_macros::*;
use builtin::*;
use vstd::*;
use vstd::modes::*;
use vstd::map::*;
use vstd::seq::*;
use vstd::prelude::*;
use vstd::assert_by_contradiction;
use vstd::calc;
use vstd::std_specs::bits::u64_leading_zeros;

verus!{

global size_of usize == 8;

pub open spec fn smallest_bin_fitting_size(size: int) -> int {
    let bytes_per_word = (usize::BITS / 8) as int;
    let wsize = (size + bytes_per_word - 1) / bytes_per_word;
    if wsize <= 1 {
        1
    } else if wsize <= 8 {
        wsize
    } else if wsize > 524288 {
        BIN_HUGE as int
    } else {
        let w = (wsize - 1) as u64;
        //let lz = w.leading_zeros();
        let lz = u64_leading_zeros(w);
        let b = (usize::BITS - 1 - lz) as u8;
        let shifted = (w >> (b - 2) as u64) as u8;
        let bin_idx = ((b * 4) + (shifted & 0x03)) - 3;
        bin_idx
    }
}

pub open spec fn pow2(i: int) -> nat
    decreases i
{
    if i <= 0 {
        1
    } else {
        pow2(i - 1) * 2
    }
}


/*
fn stuff() {
    assert(0 == 0) by(compute);
    assert(0 == 1) by(compute);

    assert(0 + 3 == 4) by(compute);
}
*/

pub const BIN_HUGE: u64 = 73;

pub open spec fn valid_bin_idx(bin_idx: int) -> bool {
    1 <= bin_idx <= BIN_HUGE
}

pub open spec fn size_of_bin(bin_idx: int) -> nat
    recommends valid_bin_idx(bin_idx)
{
    if 1 <= bin_idx <= 8 {
       (usize::BITS / 8) as nat * (bin_idx as nat)
    } else if bin_idx == BIN_HUGE {
        // the "real" upper bound on this bucket is infinite
        // the lemmas on bin sizes assume each bin has a lower bound and upper bound
        // so we pretend this is the upper bound

        8 * (524288 + 1)
        //8 * (MEDIUM_OBJ_WSIZE_MAX as nat + 1)
    } else {
        let group = (bin_idx - 9) / 4;
        let inner = (bin_idx - 9) % 4;

        ((usize::BITS / 8) * (inner + 5) * pow2(group + 1)) as nat
    }
}

spec fn property_bin(size:int) -> bool
{
    131072 >= size_of_bin(smallest_bin_fitting_size(size)) >= size
}

spec fn check_bin(size_start:int, size_end:int) -> bool
    decreases size_end - size_start + 8,
{
   if size_start >= size_end {
       true
   } else {
          property_bin(size_start)
       && check_bin(size_start + 1, size_end)
   }
}


pub proof fn bin_size_result_mul8(size: usize)
    requires
        size % 8 == 0,
        size <= 131072, //  == MEDIUM_OBJ_SIZE_MAX
        valid_bin_idx(smallest_bin_fitting_size(size as int)),
    //ensures
    //    131072 >= size_of_bin(smallest_bin_fitting_size(size as int) as int) >= size,
{
  reveal(u64_leading_zeros);
	assert(check_bin(0, 131072)) by (compute);
}







fn main() { }

}
