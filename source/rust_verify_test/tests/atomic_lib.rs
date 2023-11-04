#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const IMPORTS: &str = code_str! {
    use vstd::pervasive::*;
    use vstd::{atomic::*};
    use vstd::{modes::*};
    use vstd::prelude::*;
};

/// With contradiction_smoke_test, add a final `assert(false)` that is expected to fail at the end
/// of the test, as a cheap way to check that the trusted specs aren't contradictory
fn test_body(tests: &str, contradiction_smoke_test: bool, usize_size: Option<u32>) -> String {
    let usize_size = usize_size.map(|x| format!("    global size_of usize == {};\n", x));
    let usize_size = usize_size.as_ref().map(|x| x.as_str());
    IMPORTS.to_string()
        + "    verus!{ \n"
        + usize_size.unwrap_or("")
        + "    fn test() {"
        + tests
        + if contradiction_smoke_test { "assert(false); // FAILS\n" } else { "" }
        + "    } }"
}

const ATOMIC_U64: &str = code_str! {
    let (at, Tracked(mut perm)) = PAtomicU64::new(5);

    assert(perm.view().value == 5);

    let l = at.load(Tracked(&perm));
    assert(l == 5);

    at.store(Tracked(&mut perm), 6);
    assert(perm.view().value == 6);

    let l = at.swap(Tracked(&mut perm), 9);
    assert(l == 6);
    assert(perm.view().value == 9);

    let l = at.fetch_add_wrapping(Tracked(&mut perm), 0xffff_ffff_ffff_ffff);
    assert(l == 9);
    assert(perm.view().value == 8);

    let l = at.fetch_sub_wrapping(Tracked(&mut perm), 0xffff_ffff_ffff_ffff);
    assert(l == 8);
    assert(perm.view().value == 9);

    let l = at.fetch_or(Tracked(&mut perm), 2);
    assert(l == 9);
    assert((9u64 | 2u64) == 11u64) by(bit_vector);
    assert(perm.view().value == 11);

    let l = at.fetch_and(Tracked(&mut perm), 6);
    assert(l == 11);
    assert((11u64 & 6u64) == 2u64) by(bit_vector);
    assert(perm.view().value == 2);

    let l = at.fetch_xor(Tracked(&mut perm), 3);
    assert(l == 2);
    assert((2u64 ^ 3u64) == 1u64) by(bit_vector);
    assert(perm.view().value == 1);

    let l = at.fetch_max(Tracked(&mut perm), 5);
    assert(l == 1);
    assert(perm.view().value == 5);

    let l = at.fetch_max(Tracked(&mut perm), 4);
    assert(l == 5);
    assert(perm.view().value == 5);

    let l = at.fetch_min(Tracked(&mut perm), 4);
    assert(l == 5);
    assert(perm.view().value == 4);

    let l = at.fetch_min(Tracked(&mut perm), 7);
    assert(l == 4);
    assert(perm.view().value == 4);

    let l = at.compare_exchange_weak(Tracked(&mut perm), 5, 6);
    assert(equal(l, Result::Err(4)));
    assert(perm.view().value == 4);

    let l = at.compare_exchange_weak(Tracked(&mut perm), 4, 6);
    assert(
        (equal(l, Result::Err(4)) && perm.view().value == 4) ||
        (equal(l, Result::Ok(4)) && perm.view().value == 6)
    );

    at.store(Tracked(&mut perm), 4);
    assert(perm.view().value == 4);

    let l = at.compare_exchange(Tracked(&mut perm), 5, 6);
    assert(equal(l, Result::Err(4)));
    assert(perm.view().value == 4);

    let l = at.compare_exchange(Tracked(&mut perm), 4, 6);
    assert(equal(l, Result::Ok(4)));
    assert(perm.view().value == 6);

    let l = at.fetch_nand(Tracked(&mut perm), 3);
    assert(l == 6);
    assert(!(6u64 & 3u64) == 0xffff_ffff_ffff_fffdu64) by(bit_vector);
    assert(perm.view().value == 0xffff_ffff_ffff_fffd);

    at.store(Tracked(&mut perm), 6);
    let l = at.into_inner(Tracked(perm));
    assert(l == 6);
};

test_verify_one_file! {
    #[test] test_atomic_u64_pass test_body(ATOMIC_U64, false, None) => Ok(())
}

test_verify_one_file! {
    #[test] test_atomic_u64_smoke test_body(ATOMIC_U64, true, None) => Err(e) => assert_one_fails(e)
}

const ATOMIC_U32: &str = code_str! {
    let (at, Tracked(mut perm)) = PAtomicU32::new(5);

    assert(perm.view().value == 5);

    let l = at.load(Tracked(&perm));
    assert(l == 5);

    at.store(Tracked(&mut perm), 6);
    assert(perm.view().value == 6);

    let l = at.swap(Tracked(&mut perm), 9);
    assert(l == 6);
    assert(perm.view().value == 9);

    let l = at.fetch_add_wrapping(Tracked(&mut perm), 0xffff_ffff);
    assert(l == 9);
    assert(perm.view().value == 8);

    let l = at.fetch_sub_wrapping(Tracked(&mut perm), 0xffff_ffff);
    assert(l == 8);
    assert(perm.view().value == 9);

    let l = at.fetch_or(Tracked(&mut perm), 2);
    assert(l == 9);
    assert((9u32 | 2u32) == 11u32) by(bit_vector);
    assert(perm.view().value == 11);

    let l = at.fetch_and(Tracked(&mut perm), 6);
    assert(l == 11);
    assert((11u32 & 6u32) == 2u32) by(bit_vector);
    assert(perm.view().value == 2);

    let l = at.fetch_xor(Tracked(&mut perm), 3);
    assert(l == 2);
    assert((2u32 ^ 3u32) == 1u32) by(bit_vector);
    assert(perm.view().value == 1);

    let l = at.fetch_max(Tracked(&mut perm), 5);
    assert(l == 1);
    assert(perm.view().value == 5);

    let l = at.fetch_max(Tracked(&mut perm), 4);
    assert(l == 5);
    assert(perm.view().value == 5);

    let l = at.fetch_min(Tracked(&mut perm), 4);
    assert(l == 5);
    assert(perm.view().value == 4);

    let l = at.fetch_min(Tracked(&mut perm), 7);
    assert(l == 4);
    assert(perm.view().value == 4);

    let l = at.compare_exchange_weak(Tracked(&mut perm), 5, 6);
    assert(equal(l, Result::Err(4)));
    assert(perm.view().value == 4);

    let l = at.compare_exchange_weak(Tracked(&mut perm), 4, 6);
    assert(
        (equal(l, Result::Err(4)) && perm.view().value == 4) ||
        (equal(l, Result::Ok(4)) && perm.view().value == 6)
    );

    at.store(Tracked(&mut perm), 4);
    assert(perm.view().value == 4);

    let l = at.compare_exchange(Tracked(&mut perm), 5, 6);
    assert(equal(l, Result::Err(4)));
    assert(perm.view().value == 4);

    let l = at.compare_exchange(Tracked(&mut perm), 4, 6);
    assert(equal(l, Result::Ok(4)));
    assert(perm.view().value == 6);

    let l = at.fetch_nand(Tracked(&mut perm), 3);
    assert(l == 6);
    assert(!(6u32 & 3u32) == 0xffff_fffdu32) by(bit_vector);
    assert(perm.view().value == 0xffff_fffd);

    at.store(Tracked(&mut perm), 6);
    let l = at.into_inner(Tracked(perm));
    assert(l == 6);
};

test_verify_one_file! {
    #[test] test_atomic_u32_pass test_body(ATOMIC_U32, false, None) => Ok(())
}

test_verify_one_file! {
    #[test] test_atomic_u32_smoke test_body(ATOMIC_U32, true, None) => Err(e) => assert_one_fails(e)
}

const ATOMIC_U16: &str = code_str! {
    let (at, Tracked(mut perm)) = PAtomicU16::new(5);

    assert(perm.view().value == 5);

    let l = at.load(Tracked(&perm));
    assert(l == 5);

    at.store(Tracked(&mut perm), 6);
    assert(perm.view().value == 6);

    let l = at.swap(Tracked(&mut perm), 9);
    assert(l == 6);
    assert(perm.view().value == 9);

    let l = at.fetch_add_wrapping(Tracked(&mut perm), 0xffff);
    assert(l == 9);
    assert(perm.view().value == 8);

    let l = at.fetch_sub_wrapping(Tracked(&mut perm), 0xffff);
    assert(l == 8);
    assert(perm.view().value == 9);

    let l = at.fetch_or(Tracked(&mut perm), 2);
    assert(l == 9);
    assert((9u16 | 2u16) == 11u16) by(bit_vector);
    assert(perm.view().value == 11);

    let l = at.fetch_and(Tracked(&mut perm), 6);
    assert(l == 11);
    assert((11u16 & 6u16) == 2u16) by(bit_vector);
    assert(perm.view().value == 2);

    let l = at.fetch_xor(Tracked(&mut perm), 3);
    assert(l == 2);
    assert((2u16 ^ 3u16) == 1u16) by(bit_vector);
    assert(perm.view().value == 1);

    let l = at.fetch_max(Tracked(&mut perm), 5);
    assert(l == 1);
    assert(perm.view().value == 5);

    let l = at.fetch_max(Tracked(&mut perm), 4);
    assert(l == 5);
    assert(perm.view().value == 5);

    let l = at.fetch_min(Tracked(&mut perm), 4);
    assert(l == 5);
    assert(perm.view().value == 4);

    let l = at.fetch_min(Tracked(&mut perm), 7);
    assert(l == 4);
    assert(perm.view().value == 4);

    let l = at.compare_exchange_weak(Tracked(&mut perm), 5, 6);
    assert(equal(l, Result::Err(4)));
    assert(perm.view().value == 4);

    let l = at.compare_exchange_weak(Tracked(&mut perm), 4, 6);
    assert(
        (equal(l, Result::Err(4)) && perm.view().value == 4) ||
        (equal(l, Result::Ok(4)) && perm.view().value == 6)
    );

    at.store(Tracked(&mut perm), 4);
    assert(perm.view().value == 4);

    let l = at.compare_exchange(Tracked(&mut perm), 5, 6);
    assert(equal(l, Result::Err(4)));
    assert(perm.view().value == 4);

    let l = at.compare_exchange(Tracked(&mut perm), 4, 6);
    assert(equal(l, Result::Ok(4)));
    assert(perm.view().value == 6);

    let l = at.fetch_nand(Tracked(&mut perm), 3);
    assert(l == 6);
    assume(!(6u16 & 3u16) == 0xfffd);
    assert(perm.view().value == 0xfffd);

    at.store(Tracked(&mut perm), 6);
    let l = at.into_inner(Tracked(perm));
    assert(l == 6);
};

test_verify_one_file! {
    #[test] test_atomic_u16_pass test_body(ATOMIC_U16, false, None) => Ok(())
}

test_verify_one_file! {
    #[test] test_atomic_u16_smoke test_body(ATOMIC_U16, true, None) => Err(e) => assert_one_fails(e)
}

const ATOMIC_U8: &str = code_str! {
    let (at, Tracked(mut perm)) = PAtomicU8::new(5);

    assert(perm.view().value == 5);

    let l = at.load(Tracked(&perm));
    assert(l == 5);

    at.store(Tracked(&mut perm), 6);
    assert(perm.view().value == 6);

    let l = at.swap(Tracked(&mut perm), 9);
    assert(l == 6);
    assert(perm.view().value == 9);

    let l = at.fetch_add_wrapping(Tracked(&mut perm), 0xff);
    assert(l == 9);
    assert(perm.view().value == 8);

    let l = at.fetch_sub_wrapping(Tracked(&mut perm), 0xff);
    assert(l == 8);
    assert(perm.view().value == 9);

    let l = at.fetch_or(Tracked(&mut perm), 2);
    assert(l == 9);
    assert((9u8 | 2u8) == 11u8) by(bit_vector);
    assert(perm.view().value == 11);

    let l = at.fetch_and(Tracked(&mut perm), 6);
    assert(l == 11);
    assert((11u8 & 6u8) == 2u8) by(bit_vector);
    assert(perm.view().value == 2);

    let l = at.fetch_xor(Tracked(&mut perm), 3);
    assert(l == 2);
    assert((2u8 ^ 3u8) == 1u8) by(bit_vector);
    assert(perm.view().value == 1);

    let l = at.fetch_max(Tracked(&mut perm), 5);
    assert(l == 1);
    assert(perm.view().value == 5);

    let l = at.fetch_max(Tracked(&mut perm), 4);
    assert(l == 5);
    assert(perm.view().value == 5);

    let l = at.fetch_min(Tracked(&mut perm), 4);
    assert(l == 5);
    assert(perm.view().value == 4);

    let l = at.fetch_min(Tracked(&mut perm), 7);
    assert(l == 4);
    assert(perm.view().value == 4);

    let l = at.compare_exchange_weak(Tracked(&mut perm), 5, 6);
    assert(equal(l, Result::Err(4)));
    assert(perm.view().value == 4);

    let l = at.compare_exchange_weak(Tracked(&mut perm), 4, 6);
    assert(
        (equal(l, Result::Err(4)) && perm.view().value == 4) ||
        (equal(l, Result::Ok(4)) && perm.view().value == 6)
    );

    at.store(Tracked(&mut perm), 4);
    assert(perm.view().value == 4);

    let l = at.compare_exchange(Tracked(&mut perm), 5, 6);
    assert(equal(l, Result::Err(4)));
    assert(perm.view().value == 4);

    let l = at.compare_exchange(Tracked(&mut perm), 4, 6);
    assert(equal(l, Result::Ok(4)));
    assert(perm.view().value == 6);

    let l = at.fetch_nand(Tracked(&mut perm), 3);
    assert(l == 6);
    assume(!(6u8 & 3u8) == 0xfd);
    assert(perm.view().value == 0xfd);

    at.store(Tracked(&mut perm), 6);
    let l = at.into_inner(Tracked(perm));
    assert(l == 6);
};

test_verify_one_file! {
    #[test] test_atomic_u8_pass test_body(ATOMIC_U8, false, None) => Ok(())
}

test_verify_one_file! {
    #[test] test_atomic_u8_smoke test_body(ATOMIC_U8, true, None) => Err(e) => assert_one_fails(e)
}

const ATOMIC_I64: &str = code_str! {
    let (at, Tracked(mut perm)) = PAtomicI64::new(5);

    assert(perm.view().value == 5);

    let l = at.load(Tracked(&perm));
    assert(l == 5);

    at.store(Tracked(&mut perm), 6);
    assert(perm.view().value == 6);

    let l = at.swap(Tracked(&mut perm), 9);
    assert(l == 6);
    assert(perm.view().value == 9);

    let l = at.fetch_add_wrapping(Tracked(&mut perm), 0x7fff_ffff_ffff_ffff);
    assert(l == 9);
    assert(perm.view().value == -(9223372036854775800 as i64));

    let l = at.fetch_sub_wrapping(Tracked(&mut perm), 0x7fff_ffff_ffff_ffff);
    assert(l == -(9223372036854775800 as i64));
    assert(perm.view().value == 9);

    let l = at.fetch_sub_wrapping(Tracked(&mut perm), -0x7fff_ffff_ffff_ffff);
    assert(l == 9);
    assert(perm.view().value == -(9223372036854775800 as i64));

    let l = at.fetch_add_wrapping(Tracked(&mut perm), -0x7fff_ffff_ffff_ffff);
    assert(l == -(9223372036854775800 as i64));
    assert(perm.view().value == 9);

    let l = at.fetch_or(Tracked(&mut perm), 2);
    assert(l == 9);
    assume((9 as i64 | 2 as i64) == 11 as i64);
    assert(perm.view().value == 11);

    let l = at.fetch_and(Tracked(&mut perm), 6);
    assert(l == 11);
    assume((11 as i64 & 6 as i64) == 2 as i64);
    assert(perm.view().value == 2);

    let l = at.fetch_xor(Tracked(&mut perm), 3);
    assert(l == 2);
    assume((2 as i64 ^ 3 as i64) == 1 as i64);
    assert(perm.view().value == 1);

    let l = at.fetch_max(Tracked(&mut perm), 5);
    assert(l == 1);
    assert(perm.view().value == 5);

    let l = at.fetch_max(Tracked(&mut perm), 4);
    assert(l == 5);
    assert(perm.view().value == 5);

    let l = at.fetch_min(Tracked(&mut perm), 4);
    assert(l == 5);
    assert(perm.view().value == 4);

    let l = at.fetch_min(Tracked(&mut perm), 7);
    assert(l == 4);
    assert(perm.view().value == 4);

    let l = at.compare_exchange_weak(Tracked(&mut perm), 5, 6);
    assert(equal(l, Result::Err(4)));
    assert(perm.view().value == 4);

    let l = at.compare_exchange_weak(Tracked(&mut perm), 4, 6);
    assert(
        (equal(l, Result::Err(4)) && perm.view().value == 4) ||
        (equal(l, Result::Ok(4)) && perm.view().value == 6)
    );

    at.store(Tracked(&mut perm), 4);
    assert(perm.view().value == 4);

    let l = at.compare_exchange(Tracked(&mut perm), 5, 6);
    assert(equal(l, Result::Err(4)));
    assert(perm.view().value == 4);

    let l = at.compare_exchange(Tracked(&mut perm), 4, 6);
    assert(equal(l, Result::Ok(4)));
    assert(perm.view().value == 6);

    let l = at.fetch_nand(Tracked(&mut perm), 3);
    assert(l == 6);
    assume(!(6 as i64 & 3 as i64) == -3);
    assert(perm.view().value == -3);

    at.store(Tracked(&mut perm), 6);
    let l = at.into_inner(Tracked(perm));
    assert(l == 6);
};

test_verify_one_file! {
    #[test] test_atomic_i64_pass test_body(ATOMIC_I64, false, None) => Ok(())
}

test_verify_one_file! {
    #[test] test_atomic_i64_smoke test_body(ATOMIC_I64, true, None) => Err(e) => assert_one_fails(e)
}

const ATOMIC_I32: &str = code_str! {
    let (at, Tracked(mut perm)) = PAtomicI32::new(5);

    assert(perm.view().value == 5);

    let l = at.load(Tracked(&perm));
    assert(l == 5);

    at.store(Tracked(&mut perm), 6);
    assert(perm.view().value == 6);

    let l = at.swap(Tracked(&mut perm), 9);
    assert(l == 6);
    assert(perm.view().value == 9);

    let l = at.fetch_add_wrapping(Tracked(&mut perm), 0x7fff_ffff);
    assert(l == 9);
    assert(perm.view().value == -2147483640);

    let l = at.fetch_sub_wrapping(Tracked(&mut perm), 0x7fff_ffff);
    assert(l == -2147483640);
    assert(perm.view().value == 9);

    let l = at.fetch_sub_wrapping(Tracked(&mut perm), -0x7fff_ffff);
    assert(l == 9);
    assert(perm.view().value == -2147483640);

    let l = at.fetch_add_wrapping(Tracked(&mut perm), -0x7fff_ffff);
    assert(l == -2147483640);
    assert(perm.view().value == 9);

    let l = at.fetch_or(Tracked(&mut perm), 2);
    assert(l == 9);
    assume((9 as i32 | 2 as i32) == 11 as i32);
    assert(perm.view().value == 11);

    let l = at.fetch_and(Tracked(&mut perm), 6);
    assert(l == 11);
    assume((11 as i32 & 6 as i32) == 2 as i32);
    assert(perm.view().value == 2);

    let l = at.fetch_xor(Tracked(&mut perm), 3);
    assert(l == 2);
    assume((2 as i32 ^ 3 as i32) == 1 as i32);
    assert(perm.view().value == 1);

    let l = at.fetch_max(Tracked(&mut perm), 5);
    assert(l == 1);
    assert(perm.view().value == 5);

    let l = at.fetch_max(Tracked(&mut perm), 4);
    assert(l == 5);
    assert(perm.view().value == 5);

    let l = at.fetch_min(Tracked(&mut perm), 4);
    assert(l == 5);
    assert(perm.view().value == 4);

    let l = at.fetch_min(Tracked(&mut perm), 7);
    assert(l == 4);
    assert(perm.view().value == 4);

    let l = at.compare_exchange_weak(Tracked(&mut perm), 5, 6);
    assert(equal(l, Result::Err(4)));
    assert(perm.view().value == 4);

    let l = at.compare_exchange_weak(Tracked(&mut perm), 4, 6);
    assert(
        (equal(l, Result::Err(4)) && perm.view().value == 4) ||
        (equal(l, Result::Ok(4)) && perm.view().value == 6)
    );

    at.store(Tracked(&mut perm), 4);
    assert(perm.view().value == 4);

    let l = at.compare_exchange(Tracked(&mut perm), 5, 6);
    assert(equal(l, Result::Err(4)));
    assert(perm.view().value == 4);

    let l = at.compare_exchange(Tracked(&mut perm), 4, 6);
    assert(equal(l, Result::Ok(4)));
    assert(perm.view().value == 6);

    let l = at.fetch_nand(Tracked(&mut perm), 3);
    assert(l == 6);
    assume(!(6 as i32 & 3 as i32) == -3);
    assert(perm.view().value == -3);

    at.store(Tracked(&mut perm), 6);
    let l = at.into_inner(Tracked(perm));
    assert(l == 6);
};

test_verify_one_file! {
    #[test] test_atomic_i32_pass test_body(ATOMIC_I32, false, None) => Ok(())
}

test_verify_one_file! {
    #[test] test_atomic_i32_smoke test_body(ATOMIC_I32, true, None) => Err(e) => assert_one_fails(e)
}

const ATOMIC_I16: &str = code_str! {
    let (at, Tracked(mut perm)) = PAtomicI16::new(5);

    assert(perm.view().value == 5);

    let l = at.load(Tracked(&perm));
    assert(l == 5);

    at.store(Tracked(&mut perm), 6);
    assert(perm.view().value == 6);

    let l = at.swap(Tracked(&mut perm), 9);
    assert(l == 6);
    assert(perm.view().value == 9);

    let l = at.fetch_add_wrapping(Tracked(&mut perm), 0x7fff);
    assert(l == 9);
    assert(perm.view().value == -32760);

    let l = at.fetch_sub_wrapping(Tracked(&mut perm), 0x7fff);
    assert(l == -32760);
    assert(perm.view().value == 9);

    let l = at.fetch_sub_wrapping(Tracked(&mut perm), -0x7fff);
    assert(l == 9);
    assert(perm.view().value == -32760);

    let l = at.fetch_add_wrapping(Tracked(&mut perm), -0x7fff);
    assert(l == -32760);
    assert(perm.view().value == 9);

    let l = at.fetch_or(Tracked(&mut perm), 2);
    assert(l == 9);
    assume((9 as i16 | 2 as i16) == 11 as i16);
    assert(perm.view().value == 11);

    let l = at.fetch_and(Tracked(&mut perm), 6);
    assert(l == 11);
    assume((11 as i16 & 6 as i16) == 2 as i16);
    assert(perm.view().value == 2);

    let l = at.fetch_xor(Tracked(&mut perm), 3);
    assert(l == 2);
    assume((2 as i16 ^ 3 as i16) == 1 as i16);
    assert(perm.view().value == 1);

    let l = at.fetch_max(Tracked(&mut perm), 5);
    assert(l == 1);
    assert(perm.view().value == 5);

    let l = at.fetch_max(Tracked(&mut perm), 4);
    assert(l == 5);
    assert(perm.view().value == 5);

    let l = at.fetch_min(Tracked(&mut perm), 4);
    assert(l == 5);
    assert(perm.view().value == 4);

    let l = at.fetch_min(Tracked(&mut perm), 7);
    assert(l == 4);
    assert(perm.view().value == 4);

    let l = at.compare_exchange_weak(Tracked(&mut perm), 5, 6);
    assert(equal(l, Result::Err(4)));
    assert(perm.view().value == 4);

    let l = at.compare_exchange_weak(Tracked(&mut perm), 4, 6);
    assert(
        (equal(l, Result::Err(4)) && perm.view().value == 4) ||
        (equal(l, Result::Ok(4)) && perm.view().value == 6)
    );

    at.store(Tracked(&mut perm), 4);
    assert(perm.view().value == 4);

    let l = at.compare_exchange(Tracked(&mut perm), 5, 6);
    assert(equal(l, Result::Err(4)));
    assert(perm.view().value == 4);

    let l = at.compare_exchange(Tracked(&mut perm), 4, 6);
    assert(equal(l, Result::Ok(4)));
    assert(perm.view().value == 6);

    let l = at.fetch_nand(Tracked(&mut perm), 3);
    assert(l == 6);
    assume(!(6 as i16 & 3 as i16) == -3);
    assert(perm.view().value == -3);

    at.store(Tracked(&mut perm), 6);
    let l = at.into_inner(Tracked(perm));
    assert(l == 6);
};

test_verify_one_file! {
    #[test] test_atomic_i16_pass test_body(ATOMIC_I16, false, None) => Ok(())
}

test_verify_one_file! {
    #[test] test_atomic_i16_smoke test_body(ATOMIC_I16, true, None) => Err(e) => assert_one_fails(e)
}

const ATOMIC_I8: &str = code_str! {
    let (at, Tracked(mut perm)) = PAtomicI8::new(5);

    assert(perm.view().value == 5);

    let l = at.load(Tracked(&perm));
    assert(l == 5);

    at.store(Tracked(&mut perm), 6);
    assert(perm.view().value == 6);

    let l = at.swap(Tracked(&mut perm), 9);
    assert(l == 6);
    assert(perm.view().value == 9);

    let l = at.fetch_add_wrapping(Tracked(&mut perm), 0x7f);
    assert(l == 9);
    assert(perm.view().value == -120);

    let l = at.fetch_sub_wrapping(Tracked(&mut perm), 0x7f);
    assert(l == -120);
    assert(perm.view().value == 9);

    let l = at.fetch_sub_wrapping(Tracked(&mut perm), -0x7f);
    assert(l == 9);
    assert(perm.view().value == -120);

    let l = at.fetch_add_wrapping(Tracked(&mut perm), -0x7f);
    assert(l == -120);
    assert(perm.view().value == 9);

    let l = at.fetch_or(Tracked(&mut perm), 2);
    assert(l == 9);
    assume((9 as i8 | 2 as i8) == 11 as i8);
    assert(perm.view().value == 11);

    let l = at.fetch_and(Tracked(&mut perm), 6);
    assert(l == 11);
    assume((11 as i8 & 6 as i8) == 2 as i8);
    assert(perm.view().value == 2);

    let l = at.fetch_xor(Tracked(&mut perm), 3);
    assert(l == 2);
    assume((2 as i8 ^ 3 as i8) == 1 as i8);
    assert(perm.view().value == 1);

    let l = at.fetch_max(Tracked(&mut perm), 5);
    assert(l == 1);
    assert(perm.view().value == 5);

    let l = at.fetch_max(Tracked(&mut perm), 4);
    assert(l == 5);
    assert(perm.view().value == 5);

    let l = at.fetch_min(Tracked(&mut perm), 4);
    assert(l == 5);
    assert(perm.view().value == 4);

    let l = at.fetch_min(Tracked(&mut perm), 7);
    assert(l == 4);
    assert(perm.view().value == 4);

    let l = at.compare_exchange_weak(Tracked(&mut perm), 5, 6);
    assert(equal(l, Result::Err(4)));
    assert(perm.view().value == 4);

    let l = at.compare_exchange_weak(Tracked(&mut perm), 4, 6);
    assert(
        (equal(l, Result::Err(4)) && perm.view().value == 4) ||
        (equal(l, Result::Ok(4)) && perm.view().value == 6)
    );

    at.store(Tracked(&mut perm), 4);
    assert(perm.view().value == 4);

    let l = at.compare_exchange(Tracked(&mut perm), 5, 6);
    assert(equal(l, Result::Err(4)));
    assert(perm.view().value == 4);

    let l = at.compare_exchange(Tracked(&mut perm), 4, 6);
    assert(equal(l, Result::Ok(4)));
    assert(perm.view().value == 6);

    let l = at.fetch_nand(Tracked(&mut perm), 3);
    assert(l == 6);
    assume(!(6 as i8 & 3 as i8) == -3);
    assert(perm.view().value == -3);

    at.store(Tracked(&mut perm), 6);
    let l = at.into_inner(Tracked(perm));
    assert(l == 6);
};

test_verify_one_file! {
    #[test] test_atomic_i8_pass test_body(ATOMIC_I8, false, None) => Ok(())
}

test_verify_one_file! {
    #[test] test_atomic_i8_smoke test_body(ATOMIC_I8, true, None) => Err(e) => assert_one_fails(e)
}

const ATOMIC_BOOL: &str = code_str! {
    let (at, Tracked(mut perm)) = PAtomicBool::new(false);

    assert(perm.view().value == false);

    let l = at.load(Tracked(&perm));
    assert(l == false);

    at.store(Tracked(&mut perm), true);
    assert(perm.view().value == true);

    let l = at.swap(Tracked(&mut perm), false);
    assert(l == true);
    assert(perm.view().value == false);

    // fetch_or

    let l = at.fetch_or(Tracked(&mut perm), false);
    assert(l == false);
    assert(perm.view().value == false);

    let l = at.fetch_or(Tracked(&mut perm), true);
    assert(l == false);
    assert(perm.view().value == true);

    let l = at.fetch_or(Tracked(&mut perm), false);
    assert(l == true);
    assert(perm.view().value == true);

    let l = at.fetch_or(Tracked(&mut perm), true);
    assert(l == true);
    assert(perm.view().value == true);

    // fetch_and

    let l = at.fetch_and(Tracked(&mut perm), true);
    assert(l == true);
    assert(perm.view().value == true);

    let l = at.fetch_and(Tracked(&mut perm), false);
    assert(l == true);
    assert(perm.view().value == false);

    let l = at.fetch_and(Tracked(&mut perm), false);
    assert(l == false);
    assert(perm.view().value == false);

    let l = at.fetch_and(Tracked(&mut perm), true);
    assert(l == false);
    assert(perm.view().value == false);

    // fetch_xor

    let l = at.fetch_xor(Tracked(&mut perm), false);
    assert(l == false);
    assert(perm.view().value == false);

    let l = at.fetch_xor(Tracked(&mut perm), true);
    assert(l == false);
    assert(perm.view().value == true);

    let l = at.fetch_xor(Tracked(&mut perm), false);
    assert(l == true);
    assert(perm.view().value == true);

    let l = at.fetch_xor(Tracked(&mut perm), true);
    assert(l == true);
    assert(perm.view().value == false);

    // fetch_nand

    let l = at.fetch_nand(Tracked(&mut perm), false);
    assert(l == false);
    assert(perm.view().value == true);

    let l = at.fetch_nand(Tracked(&mut perm), false);
    assert(l == true);
    assert(perm.view().value == true);

    let l = at.fetch_nand(Tracked(&mut perm), true);
    assert(l == true);
    assert(perm.view().value == false);

    let l = at.fetch_nand(Tracked(&mut perm), true);
    assert(l == false);
    assert(perm.view().value == true);

    // compare_exchange

    let l = at.compare_exchange_weak(Tracked(&mut perm), false, false);
    assert(equal(l, Result::Err(true)));
    assert(perm.view().value == true);

    let l = at.compare_exchange_weak(Tracked(&mut perm), true, false);
    assert(
        (equal(l, Result::Err(true)) && perm.view().value == true) ||
        (equal(l, Result::Ok(true)) && perm.view().value == false)
    );

    at.store(Tracked(&mut perm), false);
    assert(perm.view().value == false);

    let l = at.compare_exchange(Tracked(&mut perm), true, false);
    assert(equal(l, Result::Err(false)));
    assert(perm.view().value == false);

    let l = at.compare_exchange(Tracked(&mut perm), false, true);
    assert(equal(l, Result::Ok(false)));
    assert(perm.view().value == true);

    let l = at.into_inner(Tracked(perm));
    assert(l == true);
};

test_verify_one_file! {
    #[test] test_atomic_bool_pass test_body(ATOMIC_BOOL, false, None) => Ok(())
}

test_verify_one_file! {
    #[test] test_atomic_bool_smoke test_body(ATOMIC_BOOL, true, None) => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_unsigned_add_overflow_fail
    IMPORTS.to_string() + verus_code_str! {
        pub fn do_nothing() {
            let (at, Tracked(mut perm)) = PAtomicU32::new(0xf000_0000);

            at.fetch_add(Tracked(&mut perm), 0xf000_0000); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_unsigned_sub_underflow_fail
    IMPORTS.to_string() + verus_code_str! {
        pub fn do_nothing() {
            let (at, Tracked(mut perm)) = PAtomicU32::new(5);

            at.fetch_sub(Tracked(&mut perm), 6); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_signed_add_overflow_fail
    IMPORTS.to_string() + verus_code_str! {
        pub fn do_nothing() {
            let (at, Tracked(mut perm)) = PAtomicI32::new(0x7000_0000);

            at.fetch_add(Tracked(&mut perm), 0x7000_0000); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_signed_add_underflow_fail
    IMPORTS.to_string() + verus_code_str! {
        pub fn do_nothing() {
            let (at, Tracked(mut perm)) = PAtomicI32::new(-0x7000_0000);

            at.fetch_add(Tracked(&mut perm), -0x7000_0000); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_signed_sub_overflow_fail
    IMPORTS.to_string() + verus_code_str! {
        pub fn do_nothing() {
            let (at, Tracked(mut perm)) = PAtomicI32::new(0x7000_0000);

            at.fetch_sub(Tracked(&mut perm), -0x7000_0000); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_signed_sub_underflow_fail
    IMPORTS.to_string() + verus_code_str! {
        pub fn do_nothing() {
            let (at, Tracked(mut perm)) = PAtomicI32::new(-0x7000_0000);

            at.fetch_sub(Tracked(&mut perm), 0x7000_0000); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// 32-bit

test_verify_one_file! {
    #[test] test_atomic_usize_32_pass test_body(
      &ATOMIC_U32.replace("u32", "usize").replace("PAtomicU32", "PAtomicUsize"),
      false,
      Some(4)) => Ok(())
}
test_verify_one_file! {
    #[test] test_atomic_usize_32_fail  test_body(
      &ATOMIC_U32.replace("u32", "usize").replace("PAtomicU32", "PAtomicUsize"),
      true,
      Some(4)) => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_atomic_isize_32_pass test_body(
      &ATOMIC_I32.replace("i32", "isize").replace("PAtomicI32", "PAtomicIsize"),
      false,
      Some(4)) => Ok(())
}
test_verify_one_file! {
    #[test] test_atomic_isize_32_fail test_body(
      &ATOMIC_I32.replace("i32", "isize").replace("PAtomicI32", "PAtomicIsize"),
      true,
      Some(4)) => Err(e) => assert_one_fails(e)
}

// 64-bit

test_verify_one_file! {
    #[test] test_atomic_usize_64_pass  test_body(
      &ATOMIC_U64.replace("u64", "usize").replace("PAtomicU64", "PAtomicUsize"),
      false,
    Some(8)) => Ok(())
}
test_verify_one_file! {
    #[test] test_atomic_usize_64_fail  test_body(
      &ATOMIC_U64.replace("u64", "usize").replace("PAtomicU64", "PAtomicUsize"),
      true,
    Some(8)) => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_atomic_isize_64_pass  test_body(
      &ATOMIC_I64.replace("i64", "isize").replace("PAtomicI64", "PAtomicIsize"),
      false,
    Some(8)) => Ok(())
}
test_verify_one_file! {
    #[test] test_atomic_isize_64_fail  test_body(
      &ATOMIC_I64.replace("i64", "isize").replace("PAtomicI64", "PAtomicIsize"),
      true,
    Some(8)) => Err(e) => assert_one_fails(e)
}
