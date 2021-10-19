#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_with_pervasive! {
    #[test] test1 code! {
        #[spec]
        fn add1_int(i: int) -> int {
            i + 1
        }

        #[spec]
        fn add1_nat(i: nat) -> nat {
            i + 1
        }

        #[spec]
        #[opaque]
        fn add1_nat_opaque(i: nat) -> nat {
            i + 1
        }

        #[proof]
        fn test0() -> nat {
            ensures(|n: nat| true);
            100
        }

        #[proof]
        fn test1(i: int, n: nat, u: u8) {
            assert(n >= 0);
            assert(u >= 0);
            assert(n + n >= 0);
            assert(((u + u) as int) < 256);
            assert(imply(u < 100, ((u + u) as int) < 250));
            assert(add1_int(u) == u as int + 1);
            assert(add1_nat(u) == u as nat + 1);
            let n0 = test0();
            assert(n0 >= 0);
            assert(add1_nat_opaque(5) >= 0);
            assert(n / 2 <= n);
            assert(u / 2 <= u);
            assert(u % 10 < 10);
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] test1_fails code! {
        #[spec]
        fn add1_int(i: int) -> int {
            i + 1
        }

        #[proof]
        fn test1(i: int, n: nat, u: u8) {
            assert(add1_int(u) == (u + 1) as int); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    #[test] test2_fails code! {
        #[proof]
        fn test1(i: int, n: nat, u: u8) {
            assert(imply((u as int) < 256, u < 256)); // FAILS, because 256 is a u8 in u < 256
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    #[test] test3_fails code! {
        #[proof]
        fn test1(i: int, n: nat, u: u8) {
            assert(i / 2 <= n); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    #[test] test4 code! {
        #[proof]
        fn typing(u: u64, i: int, n: nat) -> int {
            let u2 = i as u64;
            let i2 = u as int;
            let i3: int = u; // implicit coercion ok
            let i5: int = n; // implicit coercion ok
            let n3: nat = 10;
            let i6: int = -10;
            let u3: u8 = 300;
            let x = 2 + 2;
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

test_verify_with_pervasive! {
    #[test] test4_fails code! {
        #[proof]
        fn typing(u: u64, i: int, n: nat) {
            let u3: u8 = 300;
            assert(u3 > 100); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    #[test] test5_fails code! {
        #[proof]
        fn typing(u: u64, i: int, n: nat) {
            let i4: int = u + 1; // implicit coercion disallowed
        }
    } => Err(_)
}

test_verify_with_pervasive! {
    #[test] test6_fails code! {
        #[proof]
        fn typing(u: u64, i: int, n: nat) {
            let u3: u64 = i; // implicit coercion disallowed
        }
    } => Err(_)
}

test_verify_with_pervasive! {
    #[test] test7_fails code! {
        #[proof]
        fn typing(u: u64, i: int, n: nat) {
            let n2: nat = i; // implicit coercion disallowed
        }
    } => Err(_)
}

test_verify_with_pervasive! {
    #[test] test8_fails code! {
        #[proof]
        fn typing(u: u64, i: int, n: nat) {
            let b1: bool = u + 1 <= i; // implicit coercion disallowed
        }
    } => Err(_)
}

test_verify_with_pervasive! {
    #[test] test9_fails code! {
        #[proof]
        fn typing(u: u64, i: int, n: nat) {
            let b1: bool = i <= u + 1; // implicit coercion disallowed
        }
    } => Err(_)
}
