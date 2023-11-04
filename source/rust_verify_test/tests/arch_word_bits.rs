#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_with_no_flag verus_code! {
        fn test() {
            // these are all prelude axioms

            assert(arch_word_bits() == 32 || arch_word_bits() == 64);

            assert(signed_max(8) == 0x7f);
            assert(signed_max(16) == 0x7fff);
            assert(signed_max(32) == 0x7fffffff);
            assert(signed_max(64) == 0x7fffffffffffffff);

            assert(unsigned_max(8) == 0xff);
            assert(unsigned_max(16) == 0xffff);
            assert(unsigned_max(32) == 0xffffffff);
            assert(unsigned_max(64) == 0xffffffffffffffff);

            assert(signed_min(8) == -0x80);
            assert(signed_min(16) == -0x8000);
            assert(signed_min(32) == -0x80000000);
            assert(signed_min(64) == -0x8000000000000000);

            // assert-by-compute should work

            assert(signed_max(8) == 0x7f) by(compute);
            assert(signed_max(16) == 0x7fff) by(compute);
            assert(signed_max(32) == 0x7fffffff) by(compute);
            assert(signed_max(64) == 0x7fffffffffffffff) by(compute);

            assert(unsigned_max(8) == 0xff) by(compute);
            assert(unsigned_max(16) == 0xffff) by(compute);
            assert(unsigned_max(32) == 0xffffffff) by(compute);
            assert(unsigned_max(64) == 0xffffffffffffffff) by(compute);

            assert(signed_min(8) == -0x80) by(compute);
            assert(signed_min(16) == -0x8000) by(compute);
            assert(signed_min(32) == -0x80000000) by(compute);
            assert(signed_min(64) == -0x8000000000000000) by(compute);

            // assert-by-compute computes the exponents directly, so it can get
            // a few that aren't prelude axioms:

            assert(signed_max(0) == 0) by(compute);
            assert(unsigned_max(0) == 0) by(compute);
            assert(signed_min(0) == 0) by(compute);

            assert(signed_max(3) == 3) by(compute);
            assert(unsigned_max(3) == 7) by(compute);
            assert(signed_min(3) == -4) by(compute);
        }

        fn constants() {
            assert(u8::MIN == 0);
            assert(u16::MIN == 0);
            assert(u32::MIN == 0);
            assert(u64::MIN == 0);
            assert(u128::MIN == 0);
            assert(usize::MIN == 0);

            assert(i8::MIN == -0x80);
            assert(i16::MIN == -0x8000);
            assert(i32::MIN == -0x80000000);
            assert(i64::MIN == -0x8000000000000000);
            assert(i128::MIN == -0x80000000000000000000000000000000);
            assert(isize::MIN == -0x80000000 || isize::MIN == -0x8000000000000000);

            assert(u8::MAX == 0xff);
            assert(u16::MAX == 0xffff);
            assert(u32::MAX == 0xffffffff);
            assert(u64::MAX == 0xffffffffffffffff);
            assert(u128::MAX == 0xffffffffffffffffffffffffffffffff);
            assert(usize::MAX == 0xffffffff || usize::MAX == 0xffffffffffffffff);

            assert(i8::MAX == 0x7f);
            assert(i16::MAX == 0x7fff);
            assert(i32::MAX == 0x7fffffff);
            assert(i64::MAX == 0x7fffffffffffffff);
            assert(i128::MAX == 0x7fffffffffffffffffffffffffffffff);
            assert(isize::MAX == 0x7fffffff || isize::MAX == 0x7fffffffffffffff);

            assert(u8::BITS == 8);
            assert(u16::BITS == 16);
            assert(u32::BITS == 32);
            assert(u64::BITS == 64);
            assert(u128::BITS == 128);
            assert(usize::BITS == 32 || usize::BITS == 64);

            assert(i8::BITS == 8);
            assert(i16::BITS == 16);
            assert(i32::BITS == 32);
            assert(i64::BITS == 64);
            assert(i128::BITS == 128);
            assert(isize::BITS == 32 || isize::BITS == 64);

            // Constant should work in exec-mode
            let x = isize::BITS;
            assert(x == 32 || x == 64);
        }

        fn arch_fail_1() {
            assert(arch_word_bits() == 32); // FAILS
        }
        fn arch_fail_2() {
            assert(arch_word_bits() == 64); // FAILS
        }
        fn arch_fail_3() {
            assert(arch_word_bits() == 32) by(compute); // FAILS
        }
        fn arch_fail_4() {
            assert(arch_word_bits() == 64) by(compute); // FAILS
        }
        fn arch_fail_5() {
            assert(isize::MIN == -0x8000000000000000); // FAILS
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file! {
    #[test] test_set_to_32 verus_code! {
        global size_of usize == 4;

        fn test1() {  // ARCH-WORD-BITS-32
            assert(arch_word_bits() == 32);
        }
        fn test2() {
            assert(arch_word_bits() == 32) by(compute);
        }

        fn test_constants() {
            assert(isize::MIN == -0x80000000);
            assert(usize::MAX == 0xffffffff);
            assert(isize::MAX == 0x7fffffff);
            assert(usize::BITS == 32);
            assert(isize::BITS == 32);
        }

        fn fail1() {
            assert(arch_word_bits() == 64); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_set_to_64 verus_code! {
        global size_of usize == 8;

        fn test1() {  // ARCH-WORD-BITS-64
            assert(arch_word_bits() == 64);
        }
        fn test2() {
            assert(arch_word_bits() == 64) by(compute);
        }

        fn test_constants() {
            assert(isize::MIN == -0x8000000000000000);
            assert(usize::MAX == 0xffffffffffffffff);
            assert(isize::MAX == 0x7fffffffffffffff);
            assert(usize::BITS == 64);
            assert(isize::BITS == 64);
        }

        fn fail1() {
            assert(arch_word_bits() == 32); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

// These intrinsics operate on nats so they should be disallowed in 'exec' mode:

test_verify_one_file! {
    #[test] spec_only_unsigned_max verus_code! {
        fn test(y: nat) {
            let x = unsigned_max(y);
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}

test_verify_one_file! {
    #[test] spec_only_signed_max verus_code! {
        fn test(y: nat) {
            let x = signed_max(y);
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}

test_verify_one_file! {
    #[test] spec_only_signed_min verus_code! {
        fn test(y: nat) {
            let x = signed_min(y);
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}

test_verify_one_file! {
    #[test] spec_only_arch_word_bits verus_code! {
        fn test() {
            let x = arch_word_bits();
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}
