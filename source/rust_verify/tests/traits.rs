#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_not_yet_supported_1 code! {
        trait T1 {}
        trait T2 {
            // need to add A: T1 to termination checking before supporting this
            fn f<A: T1>(a: &A) {
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_not_yet_supported_2 code! {
        trait T1 {}
        // need to add A: T1 to termination checking before supporting this
        trait T2<A: T1> {
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_not_yet_supported_3 code! {
        trait T1 {}
        // might need to add A: T1 to termination checking before supporting this
        struct S2<A: T1> {
            a: A,
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_not_yet_supported_4 code! {
        trait T1 {}
        trait T2 {
            fn f(&self) {
                no_method_body()
            }
        }
        struct S2<A> {
            a: A,
        }
        impl<A: T1> T2 for S2<A> {
            // might need to add A: T1 to termination checking before supporting this
            fn f(&self) {
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_not_yet_supported_5 code! {
        trait T1 {
            // methods without a self argument are still todo
            fn f(b: bool) {
                no_method_body()
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_not_yet_supported_6 code! {
        trait T1 {
            // methods without a self argument are still todo
            fn f(not_named_self: &Self) {
                no_method_body()
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_not_yet_supported_7 code! {
        // might need to add F: Fn(...) to termination checking before supporting this
        struct S<F: Fn(bool) -> bool> {
            f: F,
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_not_yet_supported_8 code! {
        trait T<A> {
            fn f(&self, a: &A) {
                no_method_body()
            }
        }
        struct S<A> { a: A }
        // not yet supported: multiple implementations of same trait for single datatype:
        impl T<u8> for S<u8> {
            fn f(&self, a: &u8) {}
        }
        impl T<bool> for S<bool> {
            fn f(&self, a: &bool) {}
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_ill_formed_1 code! {
        trait T1 {
            fn f(&self); // need to call no_method_body()
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_ill_formed_2 code! {
        trait T1 {
            fn f(&self) {
                // need to call no_method_body()
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_ill_formed_3 code! {
        trait T1 {
            fn f(&self) {
                no_method_body(); // no semicolon allowed
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_ill_formed_4 code! {
        trait T1 {
            fn f(&self) {
                let b = true;
                no_method_body() // can't appear after header
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_ill_formed_5 code! {
        trait T1 {
            fn f(&self) {
                no_method_body();
                let b = true; // no code after no_method_body
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_ill_formed_6 code! {
        fn f() {
            no_method_body() // can't appear in static function
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_ill_formed_7 code! {
        trait T1 {
            fn f(&self) {
                no_method_body()
            }
        }
        struct S {}
        impl T1 for S {
            fn f(&self) {
                no_method_body() // can't appear in implementation
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_ill_formed_8 code! {
        trait T1 {
            fn f(&self) {
                no_method_body()
            }
        }
        struct S {}
        impl T1 for S {
            fn f(&self) {
                requires(true); // no requires allowed
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_ill_formed_9 code! {
        trait T1 {
            fn f(&self) {
                no_method_body()
            }
        }
        struct S {}
        impl T1 for S {
            fn f(&self) {
                ensures(true); // no ensures allowed
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_mode_matches_1 code! {
        trait T1 {
            #[spec]
            fn f(&self) {
                no_method_body()
            }
        }
        struct S {}
        impl T1 for S {
            fn f(&self) {
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_mode_matches_2 code! {
        trait T1 {
            fn f(&self) {
                no_method_body()
            }
        }
        struct S {}
        impl T1 for S {
            #[spec]
            fn f(&self) {
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_mode_matches_3 code! {
        trait T1 {
            fn f(#[spec] &self) {
                no_method_body()
            }
        }
        struct S {}
        impl T1 for S {
            fn f(&self) {
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_mode_matches_4 code! {
        trait T1 {
            fn f(&self) {
                no_method_body()
            }
        }
        struct S {}
        impl T1 for S {
            fn f(#[spec] &self) {
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_mode_matches_5 code! {
        trait T1 {
            fn f(&self, #[spec] b: bool) {
                no_method_body()
            }
        }
        struct S {}
        impl T1 for S {
            fn f(&self, b: bool) {
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_mode_matches_6 code! {
        trait T1 {
            fn f(&self, b: bool) {
                no_method_body()
            }
        }
        struct S {}
        impl T1 for S {
            fn f(&self, #[spec] b: bool) {
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_mode_matches_7 code! {
        trait T1 {
            #[verifier(returns(spec))]
            fn f(&self) -> bool {
                no_method_body()
            }
        }
        struct S {}
        impl T1 for S {
            fn f(&self) -> bool {
                true
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_mode_matches_8 code! {
        trait T1 {
            fn f(&self) -> bool {
                no_method_body()
            }
        }
        struct S {}
        impl T1 for S {
            #[verifier(returns(spec))]
            fn f(&self) -> bool {
                true
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_termination_1 code! {
        trait T {
            #[spec]
            fn f(&self) { no_method_body() }
        }

        #[spec]
        fn rec<A: T>(x: &A) {
            x.f();
        }

        struct S {}

        impl T for S {
            #[spec]
            fn f(&self) {
                rec(self);
            }
        }

        #[proof]
        fn test() {
            let s = S {};
            s.f();
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_termination_2 code! {
        trait T {
            #[spec]
            fn f<A: T>(&self, x: &A);
        }

        struct S {}

        impl T for S {
            #[spec]
            fn f<A: T>(&self, x: &A) {
                x.f(x)
            }
        }

        #[proof]
        fn test() {
            let s = S {};
            s.f(&s);
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_termination_3 code! {
        trait T {
            #[spec]
            fn f(&self) { no_method_body() }
        }

        struct S {}

        impl T for S {
            #[spec]
            fn f(&self) {
                self.f();
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_termination_4_ok code! {
        trait T {
            fn f(&self, x: &Self, n: u64) {
                no_method_body()
            }
        }
        struct S {}
        impl T for S {
            fn f(&self, x: &Self, n: u64) {
                decreases(n);
                if n > 0 {
                    self.f(x, n - 1);
                    x.f(self, n - 1);
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_termination_4_fail_1a code! {
        trait T {
            fn f(&self, x: &Self, n: u64) {
                no_method_body()
            }
        }
        struct S {}
        impl T for S {
            fn f(&self, x: &Self, n: u64) {
                self.f(x, n - 1);
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_termination_4_fail_1b code! {
        trait T {
            fn f(&self, x: &Self, n: u64) {
                no_method_body()
            }
        }
        struct S {}
        impl T for S {
            fn f(&self, x: &Self, n: u64) {
                decreases(n);
                self.f(x, n - 1); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_termination_4_fail_1c code! {
        trait T {
            fn f(&self, x: &Self, n: u64) {
                no_method_body()
            }
        }
        struct S {}
        impl T for S {
            fn f(&self, x: &Self, n: u64) {
                decreases(n);
                g(self, x, n - 1); // FAILS
            }
        }
        fn g(x: &S, y: &S, n: u64) {
            if 0 < n {
                x.f(y, n - 1);
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_termination_4_fail_2a code! {
        trait T {
            fn f(&self, x: &Self, n: u64) {
                no_method_body()
            }
        }
        struct S {}
        impl T for S {
            fn f(&self, x: &Self, n: u64) {
                x.f(self, n - 1);
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_termination_4_fail_2b code! {
        trait T {
            fn f(&self, x: &Self, n: u64) {
                no_method_body()
            }
        }
        struct S {}
        impl T for S {
            fn f(&self, x: &Self, n: u64) {
                decreases(n);
                x.f(self, n - 1); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_1 code! {
        trait T {
            fn f(&self) {
                requires(false);
                no_method_body()
            }
        }
        struct S {}
        impl T for S {
            fn f(&self) {}
        }
        fn test() {
            let s = S {};
            s.f(); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_2 code! {
        trait T {
            fn f(&self) {
                ensures(false); // FAILS
                no_method_body()
            }
        }
        struct S {}
        impl T for S {
            fn f(&self) {}
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_3 code! {
        trait T {
            #[spec]
            fn req(&self) -> bool { no_method_body() }
            fn f(&self) {
                requires(self.req());
                no_method_body()
            }
        }
        struct S {}
        impl T for S {
            #[spec]
            fn req(&self) -> bool { false }
            fn f(&self) {}
        }
        fn test() {
            let s = S {};
            s.f(); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_4 code! {
        trait T {
            #[spec]
            fn ens(&self) -> bool { no_method_body() }
            fn f(&self) {
                ensures(self.ens()); // FAILS
                no_method_body()
            }
        }
        struct S {}
        impl T for S {
            #[spec]
            fn ens(&self) -> bool { false }
            fn f(&self) {}
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_5 code! {
        trait T {
            #[spec]
            fn req(&self) -> bool { no_method_body() }
            fn f(&self) {
                requires(self.req());
                no_method_body()
            }
        }
        struct S {}
        impl T for S {
            #[spec]
            fn req(&self) -> bool { true }
            fn f(&self) {}
        }
        fn test1(s: &S) {
            s.f();
        }
        fn test2<A: T>(a: &A) {
            a.f(); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_6 code! {
        trait T<A> {
            #[spec]
            fn req(&self, a: A) -> bool { no_method_body() }

            #[spec]
            fn ens(&self, a: A, r: A) -> bool { no_method_body() }

            fn f(&self, a: &A) -> A {
                requires(self.req(*a));
                ensures(|ra: A| self.ens(*a, ra)); // FAILS
                no_method_body()
            }
        }

        struct B {
            x: bool,
        }

        struct I {
            x: u64,
        }

        impl T<bool> for B {
            #[spec]
            fn req(&self, a: bool) -> bool {
                a
            }

            #[spec]
            fn ens(&self, a: bool, r: bool) -> bool {
                r == (a && self.x)
            }

            fn f(&self, a: &bool) -> bool {
                *a && self.x
            }
        }

        impl T<u64> for I {
            #[spec]
            fn req(&self, a: u64) -> bool {
                self.x < a && a < 100
            }

            #[spec]
            fn ens(&self, a: u64, r: u64) -> bool {
                self.x <= r && r < 100
            }

            fn f(&self, a: &u64) -> u64 {
                self.x / 2 + a
            }
        }

        fn p<A, Z: T<A>>(a: &A, z: &Z) -> A {
            requires(z.req(*a));
            ensures(|rz: A| z.ens(*a, rz));
            z.f(a)
        }

        fn test() {
            let i = I { x: 30 };
            print_u64(p(&10, &i)); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_multiple code! {
        trait T1 {
            fn f1(&self, u: u64) {
                requires(u > 10);
                no_method_body()
            }
        }
        trait T2 {
            fn f2(&self, u: u64) {
                requires(u > 20);
                no_method_body()
            }
        }
        struct S {}
        impl T1 for S {
            fn f1(&self, u: u64) {}
        }
        impl T2 for S {
            fn f2(&self, u: u64) {}
        }
        fn test<A: T1 + T2>(a: &A) {
            a.f1(25);
            a.f2(25);
            a.f1(15);
            a.f2(15); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_generic_1_ok code! {
        trait T<A> {
            #[spec]
            fn apple(&self, #[spec] b: A) -> bool {
                no_method_body()
            }
        }

        struct S<A, B>(A, B);

        impl<C> T<(C, u16)> for S<bool, C> {
            #[spec]
            fn apple(&self, #[spec] b: (C, u16)) -> bool {
                b.1 > 10
            }
        }

        #[proof]
        fn test() -> bool {
            ensures(|b: bool| b);

            let i: u8 = 10;
            let s = S(true, i);
            let b: bool = s.apple((i, 20));
            b
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_generic_1_fail code! {
        trait T<A> {
            #[spec]
            fn apple(&self, #[spec] b: A) -> bool {
                no_method_body()
            }
            fn banana(&self, b: A) -> A {
                no_method_body()
            }
        }

        struct S<A, B>(A, B);

        impl<C> T<(C, u16)> for S<bool, C> {
            #[spec]
            fn apple(&self, #[spec] b: (C, u16)) -> bool {
                b.1 > 10
            }
            fn banana(&self, b: (C, u16)) -> (C, u16) {
                (b.0, 10)
            }
        }

        #[proof]
        fn test() -> bool {
            ensures(|b: bool| b); // FAILS

            let i: u8 = 10;
            let s = S(true, i);
            let b: bool = s.apple((i, 5));
            b
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_generic_2 code! {
        trait T<A> {
            #[spec]
            fn apple(&self, #[spec] b: A) -> bool {
                no_method_body()
            }
            fn banana(&self, b: A) -> A {
                no_method_body()
            }
        }

        struct S<A, B>(A, B);

        impl T<u8> for S<u16, u32> {
            #[spec]
            fn apple(&self, #[spec] b: u8) -> bool {
                b > 10
            }
            fn banana(&self, b: u8) -> u8 {
                b / 2
            }
        }

        #[proof]
        fn test() -> bool {
            ensures(|b: bool| b); // FAILS

            let s = S(10, 20);
            let b: bool = s.apple(5);
            b
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_generic_3 code! {
        trait T {
            #[spec]
            fn apple(&self, #[spec] b: bool) -> bool {
                no_method_body()
            }

            fn banana(&self) {
                requires(self.apple(true));
                ensures(true);
                no_method_body()
            }
        }

        struct S<A, B>(A, B);

        fn f1<A: T>(a: &A) {
            requires(a.apple(true));
            a.banana();
        }

        impl T for S<bool, bool> {
            #[spec]
            fn apple(&self, #[spec] b: bool) -> bool {
                self.0 && self.1 && b
            }

            fn banana(&self) {
            }
        }

        fn test1() {
            let s = S(true, true);
            s.banana();
            f1(&s);
        }

        fn test2() {
            let s = S(true, false);
            s.banana(); // FAILS
        }

        fn test3() {
            let s = S(true, false);
            f1(&s); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_self_ok code! {
        trait T {
            #[spec]
            fn r<'a>(&'a self, x: &'a Self, b: bool) -> &'a Self { no_method_body() }

            fn f<'a>(&'a self, x: &'a Self, b: bool) -> &'a Self {
                ensures(|r: &'a Self| [
                    b >>= equal(r, self),
                    !b >>= equal(r, x),
                ]);
                no_method_body()
            }
        }

        fn p<A: T>(a1: &A, a2: &A) {
            let a3 = a1.f(a2, true);
            assert(equal(a3, a1));
        }

        struct S(u8);

        impl T for S {
            #[spec]
            fn r<'a>(&'a self, x: &'a Self, b: bool) -> &'a Self {
                if b { self } else { x }
            }

            fn f<'a>(&'a self, x: &'a Self, b: bool) -> &'a Self {
                let x = if b { self } else { x };
                assert(equal(x, self.r(x, b)));
                x
            }
        }

        fn test() {
            let s1 = S(1);
            let s2 = S(2);
            let s3 = s1.f(&s2, true);
            assert(s1.0 == s3.0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_self_fail code! {
        trait T {
            fn f<'a>(&'a self, x: &'a Self, b: bool) -> &'a Self {
                ensures(|r: &'a Self| [
                    b >>= equal(r, self),
                    !b >>= equal(r, x), // FAILS
                ]);
                no_method_body()
            }
        }

        fn p<A: T>(a1: &A, a2: &A) {
            let a3 = a1.f(a2, false);
            assert(equal(a3, a1)); // FAILS
        }

        struct S(u8);

        impl T for S {
            fn f<'a>(&'a self, x: &'a Self, b: bool) -> &'a Self {
                if b { self } else { self }
            }
        }

        fn test() {
            let s1 = S(1);
            let s2 = S(2);
            let s3 = s1.f(&s2, false);
            assert(s1.0 == s3.0); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}
