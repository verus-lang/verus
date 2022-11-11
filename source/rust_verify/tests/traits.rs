#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_not_yet_supported_1 verus_code! {
        trait T1 {}
        trait T2 {
            // need to add A: T1 to termination checking before supporting this
            fn f<A: T1>(a: &A) {
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_not_yet_supported_2 verus_code! {
        trait T1 {}
        // need to add A: T1 to termination checking before supporting this
        trait T2<A: T1> {
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_not_yet_supported_3 verus_code! {
        trait T1 {}
        // might need to add A: T1 to termination checking before supporting this
        struct S2<A: T1> {
            a: A,
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_not_yet_supported_4 verus_code! {
        trait T1 {}
        trait T2 {
            fn f(&self);
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
    #[test] test_not_yet_supported_5 verus_code! {
        trait T1 {
            // methods without a self argument are still todo
            fn f(b: bool);
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_not_yet_supported_6 verus_code! {
        trait T1 {
            // methods without a self argument are still todo
            fn f(not_named_self: &Self);
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_not_yet_supported_7 verus_code! {
        // might need to add F: Fn(...) to termination checking before supporting this
        struct S<F: Fn(bool) -> bool> {
            f: F,
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_not_yet_supported_8 verus_code! {
        trait T<A> {
            fn f(&self, a: &A);
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
    #[test] test_not_yet_supported_9 verus_code! {
        trait T<A> {
            fn f(&self, a: A) -> A;
        }
        struct S {}
        // not yet supported: multiple implementations of same trait for single datatype:
        impl T<bool> for S {
            fn f(&self, a: bool) -> bool { !a }
        }
        impl T<u64> for S {
            fn f(&self, a: u64) -> u64 { a / 2 }
        }
        fn test() {
            let s = S {};
            s.f(true);
            s.f(10);
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_not_yet_supported_10 code! {
        trait T {
            #[spec]
            fn f(&self) -> bool { no_method_body() }

            #[proof]
            fn p(&self) {
                ensures(exists(|x: &Self| self.f() != x.f()));
                no_method_body()
            }
        }

        #[proof]
        #[verifier(external_body)]
        #[verifier(broadcast_forall)]
        fn f_not_g<A: T>() {
            ensures(exists(|x: &A, y: &A| x.f() != y.f()));
        }

        struct S {}

        fn test() {
            assert(false);
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test_not_yet_supported_11 code! {
        trait T {
            #[spec]
            fn f(&self) -> bool { no_method_body() }
        }

        trait S : T {
            #[spec]
            fn g(&self) -> bool { no_method_body() }
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test_not_yet_supported_12 code!{
        struct Abc<T> {
            t: T,
        }

        trait SomeTrait {
            #[spec]
            fn f(&self) -> bool { no_method_body() }
        }

        impl<S> Abc<S> {
            fn foo(&self)
                where S: SomeTrait
            {
                assert(self.t.f() == self.t.f());
            }
        }
    } => Err(_)
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
    #[test] test_mode_matches_1 verus_code! {
        trait T1 {
            spec fn f(&self);
        }
        struct S {}
        impl T1 for S {
            fn f(&self) {
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_mode_matches_2 verus_code! {
        trait T1 {
            fn f(&self);
        }
        struct S {}
        impl T1 for S {
            spec fn f(&self) {
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
    #[test] test_mode_matches_5 verus_code! {
        trait T1 {
            proof fn f(&self, tracked b: bool);
        }
        struct S {}
        impl T1 for S {
            proof fn f(&self, b: bool) {
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_mode_matches_6 verus_code! {
        trait T1 {
            proof fn f(&self, b: bool);
        }
        struct S {}
        impl T1 for S {
            proof fn f(&self, tracked b: bool) {
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_mode_matches_7 verus_code! {
        trait T1 {
            proof fn f(&self) -> tracked bool;
        }
        struct S {}
        impl T1 for S {
            proof fn f(&self) -> bool {
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
    #[test] test_termination_1 verus_code! {
        trait T {
            spec fn f(&self);
        }

        spec fn rec<A: T>(x: &A) {
            x.f();
        }

        struct S {}

        impl T for S {
            spec fn f(&self) {
                rec(self);
            }
        }

        proof fn test() {
            let s = S {};
            s.f();
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_termination_2 verus_code! {
        trait T {
            spec fn f<A: T>(&self, x: &A);
        }

        struct S {}

        impl T for S {
            spec fn f<A: T>(&self, x: &A) {
                x.f(x)
            }
        }

        proof fn test() {
            let s = S {};
            s.f(&s);
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_termination_3 verus_code! {
        trait T {
            spec fn f(&self);
        }

        struct S {}

        impl T for S {
            spec fn f(&self) {
                self.f();
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_termination_4_ok verus_code! {
        trait T {
            fn f(&self, x: &Self, n: u64);
        }
        struct S {}
        impl T for S {
            fn f(&self, x: &Self, n: u64)
                decreases n
            {
                if n > 0 {
                    self.f(x, n - 1);
                    x.f(self, n - 1);
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_termination_4_fail_1a verus_code! {
        trait T {
            fn f(&self, x: &Self, n: u64);
        }
        struct S {}
        impl T for S {
            fn f(&self, x: &Self, n: u64)
                decreases 0nat
            {
                self.f(x, n - 1); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_termination_4_fail_1b verus_code! {
        trait T {
            fn f(&self, x: &Self, n: u64);
        }
        struct S {}
        impl T for S {
            fn f(&self, x: &Self, n: u64)
                decreases n
            {
                self.f(x, n - 1); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_termination_4_fail_1c verus_code! {
        trait T {
            fn f(&self, x: &Self, n: u64);
        }
        struct S {}
        impl T for S {
            fn f(&self, x: &Self, n: u64)
                decreases n
            {
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
    #[test] test_termination_4_fail_2a verus_code! {
        trait T {
            fn f(&self, x: &Self, n: u64);
        }
        struct S {}
        impl T for S {
            fn f(&self, x: &Self, n: u64)
                decreases 0nat
            {
                x.f(self, n - 1); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_termination_4_fail_2b verus_code! {
        trait T {
            fn f(&self, x: &Self, n: u64);
        }
        struct S {}
        impl T for S {
            fn f(&self, x: &Self, n: u64)
                decreases n
            {
                x.f(self, n - 1); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_1 verus_code! {
        trait T {
            fn f(&self)
                requires false;
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
    #[test] test_verify_2 verus_code! {
        trait T {
            fn f(&self)
                ensures false; // TRAIT
        }
        struct S {}
        impl T for S {
            fn f(&self) {} // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_3 verus_code! {
        trait T {
            spec fn req(&self) -> bool;
            fn f(&self)
                requires self.req();
        }
        struct S {}
        impl T for S {
            spec fn req(&self) -> bool { false }
            fn f(&self) {}
        }
        fn test() {
            let s = S {};
            s.f(); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_4 verus_code! {
        trait T {
            spec fn ens(&self) -> bool;
            fn f(&self)
                ensures self.ens(); // TRAIT
        }
        struct S {}
        impl T for S {
            spec fn ens(&self) -> bool { false }
            fn f(&self) {} // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verify_5 verus_code! {
        trait T {
            spec fn req(&self) -> bool;
            fn f(&self)
                requires self.req();
        }
        struct S {}
        impl T for S {
            spec fn req(&self) -> bool { true }
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
    #[test] test_verify_6 verus_code! {
        trait T<A> {
            spec fn req(&self, a: A) -> bool;
            spec fn ens(&self, a: A, r: A) -> bool;

            fn f(&self, a: &A) -> (ra: A)
                requires self.req(*a)
                ensures self.ens(*a, ra); // TRAIT
        }

        struct B {
            x: bool,
        }

        struct I {
            x: u64,
        }

        impl T<bool> for B {
            spec fn req(&self, a: bool) -> bool {
                a
            }

            spec fn ens(&self, a: bool, r: bool) -> bool {
                r == (a && self.x)
            }

            fn f(&self, a: &bool) -> bool {
                *a && self.x
            }
        }

        impl T<u64> for I {
            spec fn req(&self, a: u64) -> bool {
                self.x < a && a < 100
            }

            spec fn ens(&self, a: u64, r: u64) -> bool {
                self.x <= r && r < 100
            }

            fn f(&self, a: &u64) -> u64 {
                self.x / 2 + a
            } // FAILS
        }

        fn p<A, Z: T<A>>(a: &A, z: &Z) -> (rz: A)
            requires z.req(*a)
            ensures z.ens(*a, rz)
        {
            z.f(a)
        }

        fn test() {
            let i = I { x: 30 };
            print_u64(p(&10, &i)); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_multiple verus_code! {
        trait T1 {
            fn f1(&self, u: u64)
                requires u > 10;
        }
        trait T2 {
            fn f2(&self, u: u64)
                requires u > 20;
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
    #[test] test_generic_1_ok verus_code! {
        trait T<A> {
            spec fn apple(&self, b: A) -> bool;
        }

        struct S<A, B>(A, B);

        impl<C> T<(C, u16)> for S<bool, C> {
            spec fn apple(&self, b: (C, u16)) -> bool {
                b.1 > 10
            }
        }

        proof fn test() -> (b: bool)
            ensures b
        {

            let i: u8 = 10;
            let s = S(true, i);
            let b: bool = s.apple((i, 20));
            b
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_generic_1_ok_markers verus_code! {
        trait T<A: Sized> : Sized {
            spec fn apple(&self, b: A) -> bool;
        }

        struct S<A: Sized, B: Sized>(A, B);

        impl<C: Sized> T<(C, u16)> for S<bool, C> {
            spec fn apple(&self, b: (C, u16)) -> bool {
                b.1 > 10
            }
        }

        proof fn test() -> (b: bool)
            ensures b
        {

            let i: u8 = 10;
            let s = S(true, i);
            let b: bool = s.apple((i, 20));
            b
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_generic_1_fail verus_code! {
        trait T<A> {
            spec fn apple(&self, b: A) -> bool;
            fn banana(&self, b: A) -> A;
        }

        struct S<A, B>(A, B);

        impl<C> T<(C, u16)> for S<bool, C> {
            spec fn apple(&self, b: (C, u16)) -> bool {
                b.1 > 10
            }
            fn banana(&self, b: (C, u16)) -> (C, u16) {
                (b.0, 10)
            }
        }

        proof fn test() -> (b: bool)
            ensures b // FAILS
        {

            let i: u8 = 10;
            let s = S(true, i);
            let b: bool = s.apple((i, 5));
            b
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_generic_2 verus_code! {
        trait T<A> {
            spec fn apple(&self, b: A) -> bool;
            fn banana(&self, b: A) -> A;
        }

        struct S<A, B>(A, B);

        impl T<u8> for S<u16, u32> {
            spec fn apple(&self, b: u8) -> bool {
                b > 10
            }
            fn banana(&self, b: u8) -> u8 {
                b / 2
            }
        }

        proof fn test() -> (b: bool)
            ensures b // FAILS
        {

            let s = S(10, 20);
            let b: bool = s.apple(5);
            b
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_generic_3 verus_code! {
        trait T {
            spec fn apple(&self, b: bool) -> bool;

            fn banana(&self)
                requires self.apple(true)
                ensures true;
        }

        struct S<A, B>(A, B);

        fn f1<A: T>(a: &A)
            requires a.apple(true)
        {
            a.banana();
        }

        impl T for S<bool, bool> {
            spec fn apple(&self, b: bool) -> bool {
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
    #[test] test_self_ok verus_code! {
        trait T {
            spec fn r<'a>(&'a self, x: &'a Self, b: bool) -> &'a Self;

            fn f<'a>(&'a self, x: &'a Self, b: bool) -> (r: &'a Self)
                ensures
                    b ==> r === self,
                    !b ==> r === x;
        }

        fn p<A: T>(a1: &A, a2: &A) {
            let a3 = a1.f(a2, true);
            assert(a3 === a1);
        }

        struct S(u8);

        impl T for S {
            spec fn r<'a>(&'a self, x: &'a Self, b: bool) -> &'a Self {
                if b { self } else { x }
            }

            fn f<'a>(&'a self, x: &'a Self, b: bool) -> &'a Self {
                let x = if b { self } else { x };
                assert(x === self.r(x, b));
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
    #[test] test_self_fail verus_code! {
        trait T {
            fn f<'a>(&'a self, x: &'a Self, b: bool) -> (r: &'a Self)
                ensures
                    b ==> r === self,
                    !b ==> r === x; // TRAIT
        }

        fn p<A: T>(a1: &A, a2: &A) {
            let a3 = a1.f(a2, false);
            assert(a3 === a1); // FAILS
        }

        struct S(u8);

        impl T for S {
            fn f<'a>(&'a self, x: &'a Self, b: bool) -> &'a Self {
                if b { self } else { self }
            } // FAILS
        }

        fn test() {
            let s1 = S(1);
            let s2 = S(2);
            let s3 = s1.f(&s2, false);
            assert(s1.0 == s3.0); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_ok_where_clause verus_code! {
        trait Tr {
            spec fn f(&self) -> bool;
        }

        spec fn not_f<S>(x: S) -> bool
            where S: Tr
        {
            !x.f()
        }

        proof fn foo<S>(x: S, y: S) where S : Tr
            requires x.f() ==> y.f(),
            ensures not_f(y) ==> not_f(x),
        {
        }

        struct Bar<X>
        {
            x: X,
        }

        impl<X> Bar<X>
            where X: Tr
        {
            spec fn bar_not_f(&self) -> bool {
                not_f(self.x)
            }

            proof fn easy_lemma(bar1: &Self, bar2: &Self)
                requires bar1.x.f() ==> bar2.x.f(),
                ensures not_f(bar2.x) ==> not_f(bar1.x)
            {
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_synthetic_type_params verus_code!{
        spec fn global_type_id<A>() -> int;

        pub trait SomeTrait : Sized {
            spec fn x(&self);
        }

        spec fn type_id<T: SomeTrait>(obj: T) -> int {
            global_type_id::<T>()
        }

        struct Stuff<X> {
            x: X,
        }

        impl<X: SomeTrait> Stuff<X> {
            proof fn test1<Y: SomeTrait>(a: X, b: X) {
                // This passes, since a and b should have the same type
                assert(type_id(a) == type_id(b));
            }

            proof fn test2<Y: SomeTrait>(a: X, b: Y, c: impl SomeTrait, d: impl SomeTrait) {
                // This should fail; although 'c' and 'd' are both 'impl SomeTrait',
                // these are technically different type parameters.
                assert(type_id(c) == type_id(d)); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_explicit_return_stmt verus_code!{
        trait Tr<T> {
            spec fn f(&self) -> T;

            fn compute_f(&self) -> (t: T)
                ensures t === self.f();
        }

        struct X { }

        impl Tr<u64> for X {

            spec fn f(&self) -> u64 {
                2
            }

            fn compute_f(&self) -> (t: u64)
            {
                // test using an explicit 'return' statement rather than
                // an expression-return
                return 2;
            }
        }

        struct Y { }

        impl Tr<u64> for Y {

            spec fn f(&self) -> u64 {
                2
            }

            fn compute_f(&self) -> (t: u64)
            {
                return 3; // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 1)
}
