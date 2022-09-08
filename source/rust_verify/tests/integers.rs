#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        spec fn add1_int(i: int) -> int {
            i + 1
        }

        spec fn add1_int_left(i: int) -> int {
            1 + i
        }

        spec fn add1_nat(i: nat) -> nat {
            i + 1
        }

        spec fn add1_nat_left(i: nat) -> nat {
            1 + i
        }

        spec fn add_nat_nat(i: nat, j: nat) -> nat {
            i + j
        }

        spec fn add_nat_u8(i: nat, j: u8) -> int {
            i + j
        }

        spec fn add_u8_nat(i: u8, j: nat) -> int {
            i + j
        }

        #[verifier(opaque)]
        spec fn add1_nat_opaque(i: nat) -> nat {
            i + 1
        }

        proof fn test0() -> (n: nat)
            ensures true
        {
            100
        }

        proof fn test0x() -> nat {
            100
        }

        proof fn test1(i: int, n: nat, u: u8) {
            assert(n >= 0);
            assert(u >= 0);
            assert(n + n >= 0);
            assert((add(u, u) as int) < 256);
            assert(u < 100 ==> (add(u, u) as int) < 250);
            assert(add1_int(u as int) == u as int + 1);
            assert(add1_nat(u as nat) == u as nat + 1);
            let n0 = test0();
            assert(n0 >= 0);
            let n0x = test0x();
            assert(n0x >= 0);
            assert(add1_nat_opaque(5) >= 0);
            assert(n / 2 <= n);
            assert(u / 2 <= u);
            assert(u % 10 < 10);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails verus_code! {
        spec fn add1_int(i: int) -> int {
            i + 1
        }

        proof fn test1(i: int, n: nat, u: u8) {
            assert(add1_int(u as int) == add(u, 1) as int); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2_fails verus_code! {
        proof fn test1(i: int, n: nat, u: u8) {
            assert(u < 256 ==> u < ((256 as int) as u8)); // FAILS, because 256 is a u8 in u < 256
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test3_fails verus_code! {
        proof fn test1(i: int, n: nat, u: u8) {
            assert(i / 2 <= n); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_chained verus_code! {
        proof fn test1(n: nat) {
            assert(0 <= n < n as int + 1 < n as int + 2);
            assert(0 <= n as int + 1 < n < n as int + 2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test4 verus_code! {
        proof fn typing(u: u64, i: int, n: nat) -> int {
            let u2 = i as u64;
            let i2 = u as int;
            let i3: int = u as int;
            let i5: int = n as int;
            let n3: nat = 10;
            let i6: int = -10;
            let x = 2int + 2;
            let b1: bool = u <= i; // implicit coercion ok
            let b2: bool = i <= u; // implicit coercion ok
            let b3: bool = u <= i + 1; // implicit coercion ok
            let b4: bool = i + 1 <= u; // implicit coercion ok
            assert(n3 + i6 == 0); // implicit coercion ok
            assert(i6 + n3 == 0); // implicit coercion ok
            assert(n3 > i6); // implicit coercion ok
            assert(i6 < n3); // implicit coercion ok
            x
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test4_fails code! {
        #[proof]
        fn typing(u: u64, i: int, n: nat) {
            let u3: u8 = 300;
            assert(u3 > 100); // FAILS
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test5_fails code! {
        #[proof]
        fn typing(u: u64, i: int, n: nat) {
            let i4: int = u + 1; // implicit coercion disallowed
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test6_fails code! {
        #[proof]
        fn typing(u: u64, i: int, n: nat) {
            let u3: u64 = i; // implicit coercion disallowed
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test7_fails code! {
        #[proof]
        fn typing(u: u64, i: int, n: nat) {
            let n2: nat = i; // implicit coercion disallowed
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test8_fails code! {
        #[proof]
        fn typing(u: u64, i: int, n: nat) {
            let b1: bool = u + 1 <= i; // implicit coercion disallowed
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test9_fails code! {
        #[proof]
        fn typing(u: u64, i: int, n: nat) {
            let b1: bool = i <= u + 1; // implicit coercion disallowed
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test_literals code! {
        #[proof]
        fn f() {
            assert(255u8 == 254u8 + 1);
            assert(-128i8 == -127i8 - 1);
            assert(127i8 == 126i8 + 1);
            assert(0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128 == 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_fffeu128 + 1);
            assert(-0x8000_0000_0000_0000_0000_0000_0000_0000i128 == -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffi128 - 1);
            assert(0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffi128 == 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_fffei128 + 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_literals_fails1 code! {
        #[proof]
        fn f() {
            assert(0u8 == 0u8 - 1 + 1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_literals_fails2 code! {
        #[proof]
        fn f() {
            assert(255u8 == 256u8 - 1); // FAILS
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_literals_fails3 code! {
        #[proof]
        fn f() {
            assert(-128i8 == -129i8 + 1); // FAILS
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_literals_fails4 code! {
        #[proof]
        fn f() {
            assert(127i8 == 128i8 - 1); // FAILS
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_literals_fails5 code! {
        #[proof]
        fn f() {
            assert(-0x8000_0000_0000_0000_0000_0000_0000_0000i128 == -0x8000_0000_0000_0000_0000_0000_0000_0001i128 + 1); // FAILS
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_literals_fails6 code! {
        #[proof]
        fn f() {
            assert(0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffi128 == 0x8000_0000_0000_0000_0000_0000_0000_0000i128 - 1); // FAILS
        }
    } => Err(err) => assert_vir_error(err)
}
