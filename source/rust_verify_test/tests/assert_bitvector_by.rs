#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        proof fn test1(b1: u32) {
            let b2 = !b1;
            assert(add(b1, b2) == 0xffff_ffff) by(bit_vector)
                requires b2 == !b1;
            assert(add(b1, b2) == 0xffff_ffff);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2 verus_code! {
        fn concat_bits(b1: u32, b2:u32) -> (ret: u64)
            ensures
                ret == (b1 as u64) * 0x100000000 + (b2 as u64)
        {
            let b: u64 = (b1 as u64) << 32u64 | (b2 as u64);
            assert(b == add(mul(b1 as u64, 0x100000000), b2 as u64)) by(bit_vector)
                requires b == (b1 as u64) << 32u64 | (b2 as u64);
            b
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3 verus_code! {
        fn split_bits(b:u64) -> (ret: (u32, u32))
            ensures
                b == (ret.0 as u64) * 0x100000000 + (ret.1 as u64)
        {
            let b1 = (b >> 32u64) as u32;
            let b2 = (b & 0x0000_0000_ffff_ffffu64) as u32;
            assert(b == add(mul(b1 as u64, 0x100000000), b2 as u64)) by(bit_vector)
                requires
                    b1 == (b >> 32u64) as u32,
                    b2 == (b & 0x0000_0000_ffff_ffffu64) as u32;
            (b1, b2)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails verus_code! {
        proof fn test1_fails(b: u32) {
            assert((b << 2) == mul(b, 4)) by(bit_vector);
            assert((b << 2) == mul(b, 4));

            assert((b << 1) == mul(b, 4)) by(bit_vector);  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2_fails verus_code! {
        proof fn test2_fails(b1: u32) {
            assert((b1 << 1) == 0x200) by(bit_vector) requires b1 == 0x100;  // FAILS
            assert((b1 << 1) == 0x200);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test3_fails verus_code! {
        proof fn test3_fails(b1: u32, b2: u32)
            requires b1 != b2
        {
            assert((b1 << 10) == (b2 << 10)) by(bit_vector) requires b1 == b2;  // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
