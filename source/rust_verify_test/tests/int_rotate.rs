#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] unsigned_rotate verus_code! {
        use vstd::prelude::*;

        fn test_values() {
            let a = 0x12u8.rotate_left(4);
            assert(0x12u8.rotate_left(4) == 0x21u8) by (compute);
            assert(a == 0x21u8);
            let b = 0x8000_0001u32.rotate_right(1);
            assert(0x8000_0001u32.rotate_right(1) == 0xc000_0000u32) by (compute);
            assert(b == 0xc000_0000u32);
            assert(0x0123_4567_89ab_cdefu64.rotate_left(8) == 0x2345_6789_abcd_ef01u64)
                by (compute);
            assert(1u16.rotate_right(1) == 0x8000u16) by (compute);
            assert(1u128.rotate_left(127) == 1u128 << 127u32) by (compute);
        }

        fn test_unfold(v: u64, w: u32) {
            // SipHash-style use: the result unfolds to the two shifts.
            let r = v.rotate_left(13);
            assert(r == (v << 13u32) | (v >> 51u32));
            let s = w.rotate_right(7);
            assert(s == (w >> 7u32) | (w << 25u32));
        }

        fn test_full_width(x: u32, y: usize, z: u8) {
            assert(x.rotate_left(0) == x);
            let a = x.rotate_left(32);
            assert(a == x);
            let b = y.rotate_right(usize::BITS);
            assert(b == y);
            let c = z.rotate_left(8 * 3);
            assert(c == z);
        }

        fn test_round_trip(x: u32, n: u32)
            requires 0 < n < 32,
        {
            let a = x.rotate_left(n);
            let b = a.rotate_right(n);
            assert(a == (x << n) | (x >> ((32 - n) as u32)));
            assert(b == (a >> n) | (a << ((32 - n) as u32)));
            assert(((((x << n) | (x >> sub(32, n))) >> n) | (((x << n) | (x >> sub(32, n))) << sub(32, n))) == x)
                by (bit_vector) requires 0 < n < 32;
            assert(b == x);
        }

        spec fn spec_rotl(x: u16, n: u32) -> u16 {
            x.rotate_left(n)
        }

        proof fn test_spec() {
            assert(spec_rotl(0x1234u16, 4) == 0x2341u16) by (compute);
            assert(spec_rotl(0x1234u16, 16) == 0x1234u16);
        }

        fn test_no_unwind(a: u8, b: u64, c: usize)
            no_unwind
        {
            let _ = a.rotate_left(3);
            let _ = b.rotate_right(64);
            let _ = c.rotate_left(1000);
        }

        fn test_wrong(x: u8) {
            let a = x.rotate_left(1);
            assert(a == x << 1u32); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] signed_rotate verus_code! {
        use vstd::prelude::*;

        fn test_values() {
            // The signed spec casts through the unsigned one, and only bit_vector
            // evaluates a cast of an out-of-range value.
            let a = (-2i8).rotate_left(1);
            assert(a == ((((-2i8) as u8) << 1u32) | (((-2i8) as u8) >> 7u32)) as i8);
            assert(((((-2i8) as u8) << 1u32) | (((-2i8) as u8) >> 7u32)) as i8 == -3i8)
                by (bit_vector);
            assert(a == -3i8);
            let b = 1i32.rotate_right(1);
            assert(b == (((1i32 as u32) >> 1u32) | ((1i32 as u32) << 31u32)) as i32);
            assert((((1i32 as u32) >> 1u32) | ((1i32 as u32) << 31u32)) as i32 == i32::MIN)
                by (bit_vector);
            let c = (-1i64).rotate_left(17);
            assert(c == ((((-1i64) as u64) << 17u32) | (((-1i64) as u64) >> 47u32)) as i64);
            assert(((((-1i64) as u64) << 17u32) | (((-1i64) as u64) >> 47u32)) as i64 == -1i64)
                by (bit_vector);
        }

        fn test_bits(x: i16) {
            // A nonzero rotation goes through the unsigned one; bit_vector sees the casts.
            let a = x.rotate_left(4);
            assert(a == (((x as u16) << 4u32) | ((x as u16) >> 12u32)) as i16);
            assert(a < 0 <==> (x as u16) & 0x0800u16 != 0) by (bit_vector)
                requires a == (((x as u16) << 4u32) | ((x as u16) >> 12u32)) as i16;
        }

        fn test_full_width(x: i16, y: isize) {
            let a = x.rotate_left(16);
            assert(a == x);
            let b = y.rotate_right(0);
            assert(b == y);
        }

        fn test_no_unwind(a: i8, b: i128)
            no_unwind
        {
            let _ = a.rotate_left(3);
            let _ = b.rotate_right(5);
        }

        fn test_wrong(x: i8) {
            let a = x.rotate_left(8);
            assert(a == -x); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
