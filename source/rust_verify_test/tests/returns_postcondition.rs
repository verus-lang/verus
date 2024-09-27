#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] returns_basic verus_code! {
        fn test() -> u8
            returns 20u8,
        {
            20u8
        }

        proof fn proof_test() -> u8
            returns 20u8,
        {
            20u8
        }


        fn test2() {
            let j = test();
            assert(j == 20);
        }

        fn test3() -> u8
            returns 20u8, // FAILS
        {
            19u8
        }

        fn test4() -> u8
            returns 20u8,
        {
            return 19u8; // FAILS
        }

        fn test5(a: u8, b: u8) -> (k: u8)
            requires a + b < 256,
            ensures a + b < 257,
            returns (a + b) as u8,
        {
            return a; // FAILS
        }

        fn test6(a: u8, b: u8) -> (k: u8)
            requires a + b < 256,
            ensures a + b < 250,
            returns (a + b) as u8,
        {
            return a + b; // FAILS
        }

        proof fn proof_test5(a: u8, b: u8) -> (k: u8)
            requires a + b < 256,
            ensures a + b < 257,
            returns (a + b) as u8,
        {
            return a; // FAILS
        }

        proof fn proof_test6(a: u8, b: u8) -> (k: u8)
            requires a + b < 256,
            ensures a + b < 250,
            returns (a + b) as u8,
        {
            return (a + b) as u8; // FAILS
        }

    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file! {
    #[test] wrong_type verus_code! {
        fn test() -> bool
            returns 20u8,
        {
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "type of `returns` clause does not match function return type")
}

test_verify_one_file! {
    #[test] spec_fn_returns verus_code! {
        spec fn f(x: u8) -> bool
            returns x == 3
        {
            x == 3
        }
    } => Err(err) => assert_vir_error_msg(err, "spec functions cannot have `returns` clause")
}

test_verify_one_file! {
    #[test] spec_fn_returns_references_ret_param verus_code! {
        fn test() -> (x: u8)
            returns x,
        {
            20u8
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot find value `x` in this scope")
}

test_verify_one_file! {
    #[test] returning_unit_value verus_code! {
        fn test(x: u8)
            returns (),
        {
        }

        fn test(x: u8)
            ensures false, // FAILS
            returns (),
        {
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] default_trait_fn_with_returns verus_code! {
        trait Tr : Sized {
            fn test(&self) -> &Self
                returns
                    self
            {
                self
            }
        }

        struct X { }

        impl Tr for X { }

        fn test2<T: Tr>(t: T) {
            let t2 = t.test();
            assert(t2 == t);
        }

        fn test3<T: Tr>(t: T) {
            let t2 = t.test();
            assert(t2 == t);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] default_trait_fn_with_returns_override verus_code! {
        trait Tr : Sized {
            fn test(&self) -> &Self
                returns
                    self
            {
                self
            }
        }

        struct X { i: u8 }

        impl Tr for X {
            fn test(&self) -> (some_ret_value: &Self)
                ensures self.i == 5
            {
                if self.i != 5 { loop { } }
                self
            }
        }

        fn test2(x: X) {
            let x2 = x.test();
            assert(x2 == x);
            assert(x.i == 5);
        }

        fn test3(x: X) {
            let x2 = x.test();
            assert(x2 == x);
            assert(x.i == 5);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] default_trait_fn_with_returns_conflict verus_code! {
        trait Tr : Sized {
            fn test(&self) -> &Self
                returns
                    self
            {
                self
            }
        }

        struct X { i: u8 }

        impl Tr for X {
            fn test(&self) -> &Self
                returns &(X { i: 0 })
            {
                &X { i: 0 }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "a `returns` clause cannot be declared on both a trait method impl and its declaration")
}

test_verify_one_file! {
    #[test] default_trait_fn_with_returns2 verus_code! {
        trait Tr : Sized {
            fn some_other(&self) -> &Self;

            fn test(&self) -> &Self
                returns
                    self
            {
                return some_other(self); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] trait_returns_conflict verus_code! {
        trait Tr : Sized {
            spec fn ens(&self, i: u8, s: &Self) -> bool;
            spec fn ret(&self, i: u8) -> Self;

            fn test(&self, i: u8) -> (s: Self)
                ensures self.ens(i, &s),
                returns self.ret(i);
        }

        struct U { j: u8 }

        impl Tr for U {
            spec fn ens(&self, i: u8, s: &Self) -> bool { true }
            spec fn ret(&self, i: u8) -> Self {
                U {
                    j: i
                }
            }

            fn test(&self, i: u8) -> (s: Self)
                returns (U { j: 0 }),
            {
                return U { j: 0 }; // FAILS
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "a `returns` clause cannot be declared on both a trait method impl and its declaration")
}

test_verify_one_file! {
    #[test] trait_returns_on_trait_method_decl verus_code! {
        trait Tr : Sized {
            spec fn ens(&self, i: u8, s: &Self) -> bool;
            spec fn ret(&self, i: u8) -> Self;

            fn test(&self, i: u8) -> (s: Self)
                ensures self.ens(i, &s),
                returns self.ret(i);
        }

        // ok

        struct X { j: u8 }

        impl Tr for X {
            spec fn ens(&self, i: u8, s: &Self) -> bool { self.j + i < 250 }
            spec fn ret(&self, i: u8) -> Self {
                X {
                    j: (self.j + i) as u8
                }
            }

            fn test(&self, i: u8) -> (s: Self) {
                if self.j as u64 + i as u64 >= 250 {
                    loop { }
                }
                X { j: self.j + i }
            }
        }

        // fail inherited ensures

        struct Y { j: u8 }

        impl Tr for Y {
            spec fn ens(&self, i: u8, s: &Self) -> bool { self.j + i < 256 }
            spec fn ret(&self, i: u8) -> Self {
                Y {
                    j: self.j
                }
            }

            fn test(&self, i: u8) -> (s: Self) {
                return Y { j: self.j }; // FAILS
            }
        }

        // fail inherited returns

        struct Z { j: u8 }

        impl Tr for Z {
            spec fn ens(&self, i: u8, s: &Self) -> bool { self.j + i < 256 }
            spec fn ret(&self, i: u8) -> Self {
                Z {
                    j: (self.j + i) as u8
                }
            }

            fn test(&self, i: u8) -> (s: Self) {
                if self.j as u64 + i as u64 >= 256 {
                    loop { }
                }
                return Z { j: self.j }; // FAILS
            }
        }

        // fail inherited returns with extra ensures

        struct W { j: u8 }

        impl Tr for W {
            spec fn ens(&self, i: u8, s: &Self) -> bool { self.j + i < 256 }
            spec fn ret(&self, i: u8) -> Self {
                W {
                    j: (self.j + i) as u8
                }
            }

            fn test(&self, i: u8) -> (s: Self)
                ensures s.j == self.j,
            {
                if self.j as u64 + i as u64 >= 256 {
                    loop { }
                }
                return W { j: self.j }; // FAILS
            }
        }

        // Caller, generic

        fn test_call<T: Tr>(t: T, i: u8) {
            let c = t.test(i);
            assert(t.ens(i, &c));
            assert(c == t.ret(i));
        }

        fn test_call_fail<T: Tr>(t: T, i: u8) {
            let c = t.test(i);
            assert(t.ens(i, &c));
            assert(c == t.ret(i));
            assert(false); // FAILS
        }

        // Caller, specific

        fn test_specific_call(x: X, i: u8) {
            let c = x.test(i);
            assert(x.j + i < 250);
            assert(c == X { j: (x.j + i) as u8 });
        }

        fn test_specific_call_fail(x: X, i: u8) {
            let c = x.test(i);
            assert(x.j + i < 250);
            assert(c == X { j: (x.j + i) as u8 });
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file! {
    #[test] trait_returns_on_trait_method_impl verus_code! {
        trait Tr : Sized {
            spec fn ens(&self, i: u8, s: &Self) -> bool;

            fn test(&self, i: u8) -> (s: Self)
                ensures self.ens(i, &s);
        }

        // ok

        struct X { j: u8 }

        impl Tr for X {
            spec fn ens(&self, i: u8, s: &Self) -> bool { self.j + i < 256 }

            fn test(&self, i: u8) -> (s: Self)
                returns (X { j: (self.j + i) as u8 })
            {
                if self.j as u64 + i as u64 >= 256 {
                    loop { }
                }
                X { j: self.j + i }
            }
        }

        // fail inherited ensures

        struct Y { j: u8 }

        impl Tr for Y {
            spec fn ens(&self, i: u8, s: &Self) -> bool { self.j + i < 256 }

            fn test(&self, i: u8) -> (s: Self)
                returns (Y { j: self.j })
            {
                return Y { j: self.j }; // FAILS
            }
        }

        // fail new returns

        struct Z { j: u8 }

        impl Tr for Z {
            spec fn ens(&self, i: u8, s: &Self) -> bool { self.j + i < 250 }

            fn test(&self, i: u8) -> (s: Self)
                returns (Z { j: (self.j + i) as u8 })
            {
                if self.j as u64 + i as u64 >= 250 {
                    loop { }
                }
                return Z { j: self.j }; // FAILS
            }
        }

        // Caller

        fn test_call(z: Z, i: u8) {
            let z2 = z.test(i);
            assert(z.j + i < 250);
            assert(z2.j == z.j + i);
        }

        fn test_call_fail(z: Z, i: u8) {
            let z2 = z.test(i);
            assert(z.j + i < 250);
            assert(z2.j == z.j + i);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}
