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
    #[test] test_chained1 verus_code! {
        proof fn test1(n: nat) {
            assert(n as int == n as int + 0 == 0 + n as int);
            assert(2 == 1 + 1 == 3 - 1 < 4);
            assert(n as int == (n as int) * 1 == (n as int) * 1 == 1 * (n as int));
            assert(1 + n as int == n as int + 1 == 1); // FAILS
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
    #[test] test4_fails verus_code! {
        proof fn typing(u: u64, i: int, n: nat) {
            let u3: u8 = 300;
            assert(u3 > 100); // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "integer literal out of range")
}

test_verify_one_file! {
    #[test] test5_fails verus_code! {
        proof fn typing(u: u64, i: int, n: nat) {
            let i4: int = add(u, 1); // implicit coercion disallowed
        }
    } => Err(err) => assert_rust_error_msg(err, "mismatched types")
}

test_verify_one_file! {
    #[test] test6_fails verus_code! {
        proof fn typing(u: u64, i: int, n: nat) {
            let u3: u64 = i; // implicit coercion disallowed
        }
    } => Err(err) => assert_rust_error_msg(err, "mismatched types")
}

test_verify_one_file! {
    #[test] test7_fails verus_code! {
        proof fn typing(u: u64, i: int, n: nat) {
            let n2: nat = i; // implicit coercion disallowed
        }
    } => Err(err) => assert_rust_error_msg(err, "mismatched types")
}

test_verify_one_file! {
    #[test] test8_fails verus_code! {
        proof fn typing(u: u64, i: int, n: nat) {
            let b1: bool = add(u, 1) <= i; // comparison allowed between differing integer types
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test9_fails verus_code! {
        proof fn typing(u: u64, i: int, n: nat) {
            let b1: bool = i <= add(u, 1); // comparison allowed between differing integer types
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_literals verus_code! {
        proof fn f() {
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
    #[test] test_literals_fails1 verus_code! {
        proof fn f() {
            assert(0u8 == add(sub(0u8, 1), 1)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_literals_fails2 verus_code! {
        proof fn f() {
            assert(255u8 == 256u8 - 1); // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "integer literal out of range")
}

test_verify_one_file! {
    #[test] test_literals_fails3 verus_code! {
        proof fn f() {
            assert(-128i8 == -129i8 + 1); // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "integer literal out of range")
}

test_verify_one_file! {
    #[test] test_literals_fails4 verus_code! {
        proof fn f() {
            assert(127i8 == 128i8 - 1); // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "integer literal out of range")
}

test_verify_one_file! {
    #[test] test_literals_fails5 verus_code! {
        proof fn f() {
            assert(-0x8000_0000_0000_0000_0000_0000_0000_0000i128 == -0x8000_0000_0000_0000_0000_0000_0000_0001i128 + 1); // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "integer literal out of range")
}

test_verify_one_file! {
    #[test] test_literals_fails6 verus_code! {
        proof fn f() {
            assert(0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffi128 == 0x8000_0000_0000_0000_0000_0000_0000_0000i128 - 1); // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "integer literal out of range")
}

test_verify_one_file! {
    #[test] test_step verus_code! {
        use vstd::std_specs::range::*;
        spec fn and_then<A, B>(o: Option<A>, f: spec_fn(A) -> Option<B>) -> Option<B> {
            if let Some(a) = o {
                f(a)
            } else {
                None
            }
        }
        spec fn checked_add_usize(a: usize, b: usize) -> Option<usize> {
            if 0 <= a + b <= usize::MAX { Some((a + b) as usize) } else { None }
        }
        proof fn step_properties_u8(a: u8, b: u8, n: usize, m: usize) {
            // These are specified by `pub trait Step` in Rust's range.rs:
            assert(a.spec_steps_between(b) == Some(n) <==> a.spec_forward_checked(n) == Some(b));
            assert(a.spec_steps_between(b) == Some(n) <==> b.spec_backward_checked(n) == Some(a));
            assert(a.spec_steps_between(b) == Some(n) ==> a <= b);
            assert(a.spec_steps_between(b) == None::<usize> <==> a > b);
            assert(and_then(a.spec_forward_checked(n), |x: u8| x.spec_forward_checked(m))
                == and_then(a.spec_forward_checked(m), |x: u8| x.spec_forward_checked(n)));
            assert(n + m <= usize::MAX ==> and_then(a.spec_forward_checked(n), |x: u8| x.spec_forward_checked(m))
                == a.spec_forward_checked((n + m) as usize));
            assert(n + m > usize::MAX ==> and_then(a.spec_forward_checked(n), |x: u8| x.spec_forward_checked(m))
                == None::<u8>);
            assert(and_then(a.spec_backward_checked(n), |x: u8| x.spec_backward_checked(m))
                == and_then(checked_add_usize(n, m), |x: usize| a.spec_backward_checked(x)));
            assert(and_then(a.spec_backward_checked(n), |x: u8| x.spec_backward_checked(m))
                == and_then(checked_add_usize(n, m), |x: usize|
                    if let Some(z) = checked_add_usize(n, m) { a.spec_backward_checked(z) } else { None }));
            // Additional checks:
            assert(a < 255 ==> a.spec_forward_checked(1) == Some((a + 1) as u8));
            assert(a >= 255 ==> a.spec_forward_checked(1) == None::<u8>);
            assert(a >= 1 ==> a.spec_backward_checked(1) == Some((a - 1) as u8));
            assert(a < 1 ==> a.spec_backward_checked(1) == None::<u8>);
        }
        proof fn step_properties_i8(a: i8, b: i8, n: usize, m: usize) {
            // These are specified by `pub trait Step` in Rust's range.rs:
            assert(a.spec_steps_between(b) == Some(n) <==> a.spec_forward_checked(n) == Some(b));
            assert(a.spec_steps_between(b) == Some(n) <==> b.spec_backward_checked(n) == Some(a));
            assert(a.spec_steps_between(b) == Some(n) ==> a <= b);
            assert(a.spec_steps_between(b) == None::<usize> <==> a > b);
            assert(and_then(a.spec_forward_checked(n), |x: i8| x.spec_forward_checked(m))
                == and_then(a.spec_forward_checked(m), |x: i8| x.spec_forward_checked(n)));
            assert(n + m <= usize::MAX ==> and_then(a.spec_forward_checked(n), |x: i8| x.spec_forward_checked(m))
                == a.spec_forward_checked((n + m) as usize));
            assert(n + m > usize::MAX ==> and_then(a.spec_forward_checked(n), |x: i8| x.spec_forward_checked(m))
                == None::<i8>);
            assert(and_then(a.spec_backward_checked(n), |x: i8| x.spec_backward_checked(m))
                == and_then(checked_add_usize(n, m), |x: usize| a.spec_backward_checked(x)));
            assert(and_then(a.spec_backward_checked(n), |x: i8| x.spec_backward_checked(m))
                == and_then(checked_add_usize(n, m), |x: usize|
                    if let Some(z) = checked_add_usize(n, m) { a.spec_backward_checked(z) } else { None }));
            // Additional checks:
            assert(a < 127 ==> a.spec_forward_checked(1) == Some((a + 1) as i8));
            assert(a >= 127 ==> a.spec_forward_checked(1) == None::<i8>);
            assert(a >= -127 ==> a.spec_backward_checked(1) == Some((a - 1) as i8));
            assert(a < -127 ==> a.spec_backward_checked(1) == None::<i8>);
        }
        proof fn step_properties_u128(a: u128, b: u128, n: usize, m: usize) {
            // These are specified by `pub trait Step` in Rust's range.rs:
            assert(a.spec_steps_between(b) == Some(n) <==> a.spec_forward_checked(n) == Some(b));
            assert(a.spec_steps_between(b) == Some(n) <==> b.spec_backward_checked(n) == Some(a));
            assert(a.spec_steps_between(b) == Some(n) ==> a <= b);
            assert(a.spec_steps_between(b) == None::<usize> <== a > b);
            assert(and_then(a.spec_forward_checked(n), |x: u128| x.spec_forward_checked(m))
                == and_then(a.spec_forward_checked(m), |x: u128| x.spec_forward_checked(n)));
            assert(n + m <= usize::MAX ==> and_then(a.spec_forward_checked(n), |x: u128| x.spec_forward_checked(m))
                == a.spec_forward_checked((n + m) as usize));
            assert(n + m <= usize::MAX ==> and_then(a.spec_backward_checked(n), |x: u128| x.spec_backward_checked(m))
                == and_then(checked_add_usize(n, m), |x: usize| a.spec_backward_checked(x)));
            assert(n + m <= usize::MAX ==> and_then(a.spec_backward_checked(n), |x: u128| x.spec_backward_checked(m))
                == and_then(checked_add_usize(n, m), |x: usize|
                    if let Some(z) = checked_add_usize(n, m) { a.spec_backward_checked(z) } else { None }));
            // Additional checks:
            assert(a < 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff ==> a.spec_forward_checked(1) == Some((a + 1) as u128));
            assert(a >= 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff ==> a.spec_forward_checked(1) == None::<u128>);
            assert(a >= 1 ==> a.spec_backward_checked(1) == Some((a - 1) as u128));
            assert(a < 1 ==> a.spec_backward_checked(1) == None::<u128>);
        }
        proof fn step_properties_i128(a: i128, b: i128, n: usize, m: usize) {
            // These are specified by `pub trait Step` in Rust's range.rs:
            assert(a.spec_steps_between(b) == Some(n) <==> a.spec_forward_checked(n) == Some(b));
            assert(a.spec_steps_between(b) == Some(n) <==> b.spec_backward_checked(n) == Some(a));
            assert(a.spec_steps_between(b) == Some(n) ==> a <= b);
            assert(a.spec_steps_between(b) == None::<usize> <== a > b);
            assert(and_then(a.spec_forward_checked(n), |x: i128| x.spec_forward_checked(m))
                == and_then(a.spec_forward_checked(m), |x: i128| x.spec_forward_checked(n)));
            assert(n + m <= usize::MAX ==> and_then(a.spec_forward_checked(n), |x: i128| x.spec_forward_checked(m))
                == a.spec_forward_checked((n + m) as usize));
            assert(n + m <= usize::MAX ==> and_then(a.spec_backward_checked(n), |x: i128| x.spec_backward_checked(m))
                == and_then(checked_add_usize(n, m), |x: usize| a.spec_backward_checked(x)));
            assert(n + m <= usize::MAX ==> and_then(a.spec_backward_checked(n), |x: i128| x.spec_backward_checked(m))
                == and_then(checked_add_usize(n, m), |x: usize|
                    if let Some(z) = checked_add_usize(n, m) { a.spec_backward_checked(z) } else { None }));
            // Additional checks:
            assert(a < 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff ==> a.spec_forward_checked(1) == Some((a + 1) as i128));
            assert(a >= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff ==> a.spec_forward_checked(1) == None::<i128>);
            assert(a >= -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff ==> a.spec_backward_checked(1) == Some((a - 1) as i128));
            assert(a < -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff ==> a.spec_backward_checked(1) == None::<i128>);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_integer_trait_regression_979_1 verus_code! {
        use vstd::prelude::*;
        pub trait Obligations<T> {
            spec fn reveal_(t: T) -> T
                ;
        }

        struct S<T> {
            t: T
        }

        impl<T> Obligations<T> for S<T> {
            open spec fn reveal_(t: T) -> T
            {
                t
            }
        }

        impl<T: builtin::Integer> S<T> {
            spec fn t_int(t: T) -> int {
                Self::reveal_(t) as int
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_integer_trait_regression_979_2 verus_code! {
        use vstd::prelude::*;
        pub trait Obligations<T> {
            spec fn reveal_(t: T) -> T
                ;
        }

        struct S<T> {
            t: T
        }

        impl<T> Obligations<T> for S<T> {
            open spec fn reveal_(t: T) -> T
            {
                t
            }
        }

        impl<T: builtin::Integer> S<T> {
            spec(checked) fn t_int(t: T) -> nat {
                Self::reveal_(t) as nat
            }
        }
    } => Ok(err) => {
        let mut warnings = err.warnings.into_iter();
        assert!(warnings.next().expect("one warning").message
            .contains("recommendation not met: value may be out of range of the target type"));
        assert!(warnings.next().is_some());
        assert!(warnings.next().is_none());
    }
}

test_verify_one_file! {
    #[test] test_integer_trait_1 verus_code! {
        use vstd::prelude::*;
        pub open spec fn plus_three<T: Integer>(t: T) -> int {
            t as int + 3
        }

        proof fn p() {
            assert(plus_three(1u64) == 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_integer_trait_2 verus_code! {
        use vstd::prelude::*;
        pub open spec fn plus_three<T: Integer>(t: T) -> int {
            t as int + 3
        }

        proof fn p() {
            assert(plus_three(1u64) != 4); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_integer_trait_3 verus_code! {
        use vstd::prelude::*;
        pub open spec fn plus_three<T: Integer>(t: T) -> int {
            t as u64 + 3
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus currently only supports casts from integer types, `char`, and pointer types to integer types")
}

test_verify_one_file! {
    #[test] test_integer_trait_sealed_1 verus_code! {
        use vstd::prelude::*;
        struct S;
        impl Integer for S {}
    } => Err(err) => assert_rust_error_msg(err, "the trait `builtin::Integer` requires an `unsafe impl` declaration")
}

test_verify_one_file! {
    #[test] test_integer_trait_sealed_2 verus_code! {
        use vstd::prelude::*;
        pub open spec fn plus_three<T: Integer>(t: T) -> nat {
            t as nat + 3
        }

        #[derive(Copy, Clone)]
        struct S;
        unsafe impl Integer for S {
            const CONST_DEFAULT: S = S;
        }

        proof fn test() {
            assert(plus_three(S) + 1 == 1 + plus_three(S));
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot implement `sealed` trait")
}

test_verify_one_file! {
    #[test] test_spec_const verus_code! {
        pub open spec fn f() -> int { 30000000000000000000000int + 20000000000000000000000 }

        spec const A: int = 30000000000000000000000int + 20000000000000000000000;
        pub spec const B: int = add(30000000000000000000000int, 20000000000000000000000);

        spec const M: int = 30000000000000000000000int * 20000000000000000000000;
        pub spec const N: int = mul(30000000000000000000000int, 20000000000000000000000);

        spec const X: int = 30000000000000000000000 - 20000000000000000000000;
        pub spec const Y: int = sub(30000000000000000000000, 20000000000000000000000);

        proof fn test() {
            assert(A == f());
            assert(A == B);
            assert(M == N);
            assert(X == Y);
        }
    } => Ok(())
}
