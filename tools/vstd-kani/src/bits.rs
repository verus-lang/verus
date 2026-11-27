//! Harnesses for vstd's bit-count specifications (`vstd/std_specs/bits.rs`).
//!
//! `trailing_zeros`, `leading_zeros`, `trailing_ones`, `leading_ones` and `count_ones` are
//! specified through recursive spec functions (`u8_trailing_zeros`, ..., `nat_count_ones`),
//! which the generator does not translate (they are named functions). The functions below
//! transcribe those definitions; each harness checks the transcription against std for every
//! input.

#![allow(clippy::all)]

/// `nat_count_ones(n)`: `n` if `n < 2`, else `n % 2 + nat_count_ones(n / 2)`.
pub fn spec_nat_count_ones(n: u128) -> u32 {
    if n < 2 {
        n as u32
    } else {
        (n % 2) as u32 + spec_nat_count_ones(n / 2)
    }
}

macro_rules! bit_specs {
    ($m:ident, $t:ty, $bits:expr) => {
        pub mod $m {
            /// `<t>_trailing_zeros(i)`: `BITS` for 0, 0 if the low bit is set, else
            /// `1 + <t>_trailing_zeros(i / 2)`.
            pub fn spec_trailing_zeros(i: $t) -> u32 {
                if i == 0 {
                    $bits
                } else if (i & 1) != 0 {
                    0
                } else {
                    1 + spec_trailing_zeros(i / 2)
                }
            }

            /// `<t>_leading_zeros(i)`: `BITS` for 0, else `<t>_leading_zeros(i / 2) - 1`
            /// (computed in `i64`, as the spec computes in `int`).
            pub fn spec_leading_zeros(i: $t) -> i64 {
                if i == 0 {
                    $bits
                } else {
                    spec_leading_zeros(i / 2) - 1
                }
            }

            /// `<t>_trailing_ones(i)` is `<t>_trailing_zeros(!i)`.
            pub fn spec_trailing_ones(i: $t) -> u32 {
                spec_trailing_zeros(!i)
            }

            /// `<t>_leading_ones(i)` is `<t>_leading_zeros(!i)`.
            pub fn spec_leading_ones(i: $t) -> i64 {
                spec_leading_zeros(!i)
            }
        }
    };
}

bit_specs!(u8_spec, u8, 8);
bit_specs!(u16_spec, u16, 16);
bit_specs!(u32_spec, u32, 32);
bit_specs!(u64_spec, u64, 64);
bit_specs!(u128_spec, u128, 128);
bit_specs!(usize_spec, usize, 64);

// One harness per type and operation that vstd specifies. The recursion depth is at most
// the bit width, hence the unwinding bounds.
macro_rules! bit_harnesses {
    ($m:ident, $t:ty, $unwind:expr, [$($tz:ident)?], [$($lz:ident)?], [$($to:ident)?],
     [$($lo:ident)?], $co:ident) => {
        $(
            #[cfg(kani)]
            #[kani::proof]
            #[kani::unwind($unwind)]
            fn $tz() {
                let i: $t = kani::any();
                assert_eq!(i.trailing_zeros(), $m::spec_trailing_zeros(i));
            }
        )?
        $(
            #[cfg(kani)]
            #[kani::proof]
            #[kani::unwind($unwind)]
            fn $lz() {
                let i: $t = kani::any();
                assert_eq!(i.leading_zeros() as i64, $m::spec_leading_zeros(i));
            }
        )?
        $(
            #[cfg(kani)]
            #[kani::proof]
            #[kani::unwind($unwind)]
            fn $to() {
                let i: $t = kani::any();
                assert_eq!(i.trailing_ones(), $m::spec_trailing_ones(i));
            }
        )?
        $(
            #[cfg(kani)]
            #[kani::proof]
            #[kani::unwind($unwind)]
            fn $lo() {
                let i: $t = kani::any();
                assert_eq!(i.leading_ones() as i64, $m::spec_leading_ones(i));
            }
        )?
        #[cfg(kani)]
        #[kani::proof]
        #[kani::unwind($unwind)]
        fn $co() {
            let i: $t = kani::any();
            assert_eq!(i.count_ones(), spec_nat_count_ones(i as u128));
        }
    };
}

bit_harnesses!(
    u8_spec,
    u8,
    10,
    [u8_trailing_zeros],
    [u8_leading_zeros],
    [u8_trailing_ones],
    [u8_leading_ones],
    u8_count_ones
);
bit_harnesses!(
    u16_spec,
    u16,
    18,
    [u16_trailing_zeros],
    [u16_leading_zeros],
    [u16_trailing_ones],
    [u16_leading_ones],
    u16_count_ones
);
bit_harnesses!(
    u32_spec,
    u32,
    34,
    [u32_trailing_zeros],
    [u32_leading_zeros],
    [u32_trailing_ones],
    [u32_leading_ones],
    u32_count_ones
);
bit_harnesses!(
    u64_spec,
    u64,
    66,
    [u64_trailing_zeros],
    [u64_leading_zeros],
    [u64_trailing_ones],
    [u64_leading_ones],
    u64_count_ones
);
// vstd specifies trailing_zeros, leading_zeros and count_ones for u128 and usize
bit_harnesses!(
    u128_spec,
    u128,
    130,
    [u128_trailing_zeros],
    [u128_leading_zeros],
    [],
    [],
    u128_count_ones
);
bit_harnesses!(
    usize_spec,
    usize,
    66,
    [usize_trailing_zeros],
    [usize_leading_zeros],
    [],
    [],
    usize_count_ones
);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exhaustive_u8_u16_bit_specs_match_std() {
        for i in 0..=u8::MAX {
            assert_eq!(i.trailing_zeros(), u8_spec::spec_trailing_zeros(i));
            assert_eq!(i.leading_zeros() as i64, u8_spec::spec_leading_zeros(i));
            assert_eq!(i.trailing_ones(), u8_spec::spec_trailing_ones(i));
            assert_eq!(i.leading_ones() as i64, u8_spec::spec_leading_ones(i));
            assert_eq!(i.count_ones(), spec_nat_count_ones(i as u128));
        }
        for i in 0..=u16::MAX {
            assert_eq!(i.trailing_zeros(), u16_spec::spec_trailing_zeros(i));
            assert_eq!(i.leading_zeros() as i64, u16_spec::spec_leading_zeros(i));
            assert_eq!(i.trailing_ones(), u16_spec::spec_trailing_ones(i));
            assert_eq!(i.leading_ones() as i64, u16_spec::spec_leading_ones(i));
            assert_eq!(i.count_ones(), spec_nat_count_ones(i as u128));
        }
    }

    #[test]
    fn wide_bit_specs_match_std_on_samples() {
        let samples: [u128; 8] = [0, 1, 2, 3, 0x8000, u64::MAX as u128, 1 << 100, u128::MAX];
        for &s in samples.iter() {
            assert_eq!(s.trailing_zeros(), u128_spec::spec_trailing_zeros(s));
            assert_eq!(s.leading_zeros() as i64, u128_spec::spec_leading_zeros(s));
            assert_eq!(s.count_ones(), spec_nat_count_ones(s));
            let u = s as u64;
            assert_eq!(u.trailing_zeros(), u64_spec::spec_trailing_zeros(u));
            assert_eq!(u.leading_zeros() as i64, u64_spec::spec_leading_zeros(u));
            assert_eq!(u.trailing_ones(), u64_spec::spec_trailing_ones(u));
            assert_eq!(u.leading_ones() as i64, u64_spec::spec_leading_ones(u));
            let w = s as usize;
            assert_eq!(w.trailing_zeros(), usize_spec::spec_trailing_zeros(w));
            assert_eq!(w.leading_zeros() as i64, usize_spec::spec_leading_zeros(w));
        }
    }
}
