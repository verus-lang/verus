#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 code! {
        #[proof]
        fn test1(b1: u32) {
            let b2 = !b1;
            assert_bitvector_by({
                requires(b2 == !b1);
                ensures(b1 + b2 == 0xffff_ffff);
            });
            assert(b1 + b2 == 0xffff_ffff);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2 code! {
        fn concat_bits(b1: u32, b2:u32) -> u64 {
            ensures(|ret:u64| ret == (b1 as u64) * 0x100000000 + (b2 as u64));
            let b:u64 = (b1 as u64) << (32 as u64) | (b2 as u64);
            assert_bitvector_by({
                requires(b == (b1 as u64) << (32 as u64) | (b2 as u64));
                ensures(b == (b1 as u64) * 0x100000000 + (b2 as u64));
            });
            b
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3 code! {
        fn split_bits(b:u64) -> (u32, u32) {
            ensures(|ret:(u32, u32)| b ==  (ret.0 as u64) * 0x100000000 + (ret.1 as u64));
            let b1 = (b >> (32 as u64)) as u32;
            let b2 = (b & 0x0000_0000_ffff_ffffu64) as u32;
            assert_bitvector_by({
                requires([
                    b1 == (b >> (32 as u64)) as u32,
                    b2 == (b & 0x0000_0000_ffff_ffffu64) as u32,
                ]);
                ensures(b == (b1 as u64) * 0x100000000 + (b2 as u64));
            });
            (b1,b2)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails code! {
        #[proof]
        fn test1_fails(b: u32) {
            assert_bitvector_by({
                ensures((b << 2) == b*4);
            });
            assert((b << 2) == b*4);

            assert_bitvector_by({
                ensures((b << 1) == b*4);  // FAILS
            });
        }
    } => Err(err) => assert_one_fails(err)
}
