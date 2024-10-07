#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] supported_1 verus_code! {
        trait T1 {}
        trait T2 {
            fn f<A: T1>(a: &A) {
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_supported_2 verus_code! {
        trait T1 {}
        trait T2<A: T1> {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_unsupported_2 verus_code! {
        trait T1<A: T2<Self> + ?Sized> {}
        trait T2<A: T1<Self> + ?Sized> {}
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_supported_3 verus_code! {
        trait T1 {}
        struct S2<A: T1> {
            a: A,
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_supported_7 verus_code! {
        struct S<F: Fn(bool) -> bool> {
            f: F,
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_supported_8 verus_code! {
        trait T<A> {
            fn f(&self, a: &A);
        }
        struct S<A> { a: A }
        impl T<u8> for S<u8> {
            fn f(&self, a: &u8) {}
        }
        impl T<bool> for S<bool> {
            fn f(&self, a: &bool) {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_supported_9 verus_code! {
        trait T<A> {
            fn f(&self, a: A) -> A;
        }
        struct S {}
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
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_supported_12 verus_code!{
        struct Abc<T> {
            t: T,
        }

        trait SomeTrait {
            spec fn f(&self) -> bool;
        }

        impl<S> Abc<S> {
            fn foo(&self)
                where S: SomeTrait
            {
                assert(self.t.f() == self.t.f());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ill_formed_1 code! {
        trait T1 {
            fn f(&self) {
                no_method_body()
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "no_method_body can only appear in trait method declarations")
}

test_verify_one_file! {
    #[test] test_ill_formed_3 code! {
        trait T1 {
            fn f(&self) {
                no_method_body(); // no semicolon allowed
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "no_method_body() must be a method's final expression, with no semicolon")
}

test_verify_one_file! {
    #[test] test_ill_formed_4 code! {
        trait T1 {
            fn f(&self) {
                let b = true;
                no_method_body() // can't appear after header
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "no statements are allowed before no_method_body()")
}

test_verify_one_file! {
    #[test] test_ill_formed_5 code! {
        trait T1 {
            fn f(&self) {
                no_method_body();
                let b = true; // no code after no_method_body
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "no_method_body() must be a method's final expression, with no semicolon")
}

test_verify_one_file! {
    #[test] test_ill_formed_6 code! {
        fn f() {
            no_method_body() // can't appear in static function
        }
    } => Err(err) => assert_vir_error_msg(err, "no_method_body can only appear in trait method declarations")
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
    } => Err(err) => assert_vir_error_msg(err, "no_method_body can only appear in trait method declarations")
}

test_verify_one_file! {
    #[test] test_ill_formed_8 verus_code! {
        trait T1 {
            fn f(&self);
        }
        struct S {}
        impl T1 for S {
            fn f(&self)
                requires true // no requires allowed
            {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "trait method implementation cannot declare requires")
}

test_verify_one_file! {
    #[test] test_ill_formed_10 code! {
        trait T1 {
            fn VERUS_SPEC__f(&self) { no_method_body() }
        }
    } => Err(err) => assert_vir_error_msg(err, "no matching method found for method specification")
}

test_verify_one_file! {
    #[test] test_ill_formed_11 code! {
        trait T1 {
            fn VERUS_SPEC__f(&self) { }
            fn f(&self);
        }
    } => Err(err) => assert_vir_error_msg(err, "trait method declaration body must end with call to no_method_body()")
}

test_verify_one_file! {
    #[test] test_ill_formed_12 code! {
        trait T1 {
            fn VERUS_SPEC__f(&self, x: bool) { no_method_body() }
            fn f(&self);
        }
    } => Err(err) => assert_vir_error_msg(err, "method specification has different number of parameters from method")
}

test_verify_one_file! {
    #[test] test_ill_formed_13 code! {
        trait T1 {
            fn VERUS_SPEC__f(&self, x: bool) { no_method_body() }
            fn f(&self, x: u16);
        }
    } => Err(err) => assert_vir_error_msg(err, "method specification has different parameters from method")
}

test_verify_one_file! {
    #[test] test_ill_formed_14 code! {
        trait T1 {
            fn VERUS_SPEC__f(&self, x: bool) -> bool { no_method_body() }
            fn f(&self, x: bool) -> u16;
        }
    } => Err(err) => assert_vir_error_msg(err, "method specification has a different return from method")
}

test_verify_one_file! {
    #[test] test_ill_formed_15_todo code! {
        trait T1 {
            fn VERUS_SPEC__f<A>(&self, x: A) -> bool { no_method_body() }
            fn f<B>(&self, x: B) -> bool; // error: A and B have different names
        }
    } => Err(err) => assert_vir_error_msg(err, "method specification has different type parameters from method")
}

test_verify_one_file! {
    #[test] test_ill_formed_16 verus_code! {
        trait T {
            fn f(&self);
        }
        fn test<A: T>(a: &A) {
            a.VERUS_SPEC__f();
        }
    } => Err(err) => assert_vir_error_msg(err, "`crate::T::VERUS_SPEC__f` is not supported")
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
    } => Err(err) => assert_vir_error_msg(err, "function must have mode spec")
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
    } => Err(err) => assert_vir_error_msg(err, "function must have mode exec")
}

test_verify_one_file! {
    #[test] test_mode_matches_3 verus_code! {
        trait T1 {
            fn f(#[verifier::spec] &self);
        }
        struct S {}
        impl T1 for S {
            fn f(&self) {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "parameter must have mode spec")
}

test_verify_one_file! {
    #[test] test_mode_matches_4 verus_code! {
        trait T1 {
            fn f(&self);
        }
        struct S {}
        impl T1 for S {
            fn f(#[verifier::spec] &self) {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "parameter must have mode exec")
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
    } => Err(err) => assert_vir_error_msg(err, "parameter must have mode proof")
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
    } => Err(err) => assert_vir_error_msg(err, "parameter must have mode spec")
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
    } => Err(err) => assert_vir_error_msg(err, "function return value must have mode proof")
}

test_verify_one_file! {
    #[test] test_mode_matches_8 verus_code! {
        trait T1 {
            fn f(&self) -> bool;
        }
        struct S {}
        impl T1 for S {
            #[verifier::returns(spec)] /* vattr */
            fn f(&self) -> bool {
                true
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "function return value must have mode exec")
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
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_1b verus_code! {
        trait T<A> {
            spec fn f() -> int;
        }

        struct S<B>(B);
        impl<A> T<A> for S<A> {
            spec fn f() -> int {
                h() + 1
            }
        }

        spec fn g<X, Y: T<X>>() -> int {
            Y::f() + 1
        }

        spec fn h() -> int {
            g::<bool, S<bool>>() + 1
        }

        proof fn test()
            ensures false
        {
            assert(h() == g::<bool, S<bool>>() + 1);
            assert(h() == h() + 3);
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
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
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_3 verus_code! {
        trait T {
            spec fn f(&self);
        }

        struct S {}

        impl T for S {
            spec fn f(&self) {
                self.f()
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
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
    } => Ok(err) => {
        assert!(err.warnings.iter().find(|x| x.message.contains("decreases checks in exec functions do not guarantee termination of functions with loops or of their callers")).is_some());
    }
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
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2);
        assert!(relevant_error_span(&err.errors[0].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
        assert!(relevant_error_span(&err.errors[1].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
    }
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
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2);
        assert!(relevant_error_span(&err.errors[0].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
        assert!(relevant_error_span(&err.errors[1].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
    }
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
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2);
        assert!(relevant_error_span(&err.errors[0].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
        assert!(relevant_error_span(&err.errors[1].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
    }
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
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2);
        assert!(relevant_error_span(&err.errors[0].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
        assert!(relevant_error_span(&err.errors[1].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
    }
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
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2);
        assert!(relevant_error_span(&err.errors[0].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
        assert!(relevant_error_span(&err.errors[1].spans).text.iter().find(|x| x.text.contains("FAILS")).is_some());
    }
}

test_verify_one_file! {
    #[test] test_termination_5_fail_1 verus_code! {
        trait T { type X; }
        struct Q<A: T>(A::X);
        struct R;
        impl T for R { type X = S; }
        struct S(spec_fn(Q<R>) -> int);
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_5_fail_2 verus_code! {
        trait T { type X; }
        struct Q<A: T>(A::X);
        struct R;
        impl T for R { type X = spec_fn(S) -> int; }
        struct S(Q<R>);
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_5_fail_3 verus_code! {
        trait T { type X; }
        struct Q<A: T>(spec_fn(A::X) -> int);
        struct R;
        impl T for R { type X = S; }
        struct S(Q<R>);
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_5_fail_4 verus_code! {
        trait T { type X; }
        struct Q<A: T>(A::X);
        struct R;
        impl T for R { type X = S; }
        struct S(Q<R>);
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_5_fail_5 verus_code! {
        trait T { type X; }
        struct Q<A: T>(spec_fn(A::X) -> int);
        struct S(Q<S>);
        impl T for S { type X = int; }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_5_fail_6 verus_code! {
        trait T { type X; }
        struct S<W: T>(<W as T>::X);
        struct TT { }
        impl T for TT { type X = S<TT>; }

        spec fn arbitrary<A>() -> A;
        spec fn foo(n: nat) -> S<TT>
            decreases n
        {
            if n > 0 {
                S(foo((n - 1) as nat))
            } else {
                arbitrary()
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_5_fail_7 verus_code! {
        trait T { type X; }
        trait U { type Y; }
        struct P<W: T>(<W as T>::X);
        struct Q<W: U>(<W as U>::Y);
        struct TT { }
        struct UU { }
        impl T for TT { type X = Q<UU>; }
        impl U for UU { type Y = P<TT>; }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_5_fail_8 verus_code! {
        trait T { type A: T; }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_5_fail_9 verus_code! {
        trait T1 { type A: T2; }
        trait T2 { type A: T1; }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_5_fail_10 verus_code! {
        struct S<A>(A);

        trait T1 { proof fn f1() ensures false; }
        trait T2 { type X; }
        trait T3 { proof fn f3() ensures false; }

        impl T1 for bool {
            proof fn f1() {
                <S<int> as T3>::f3();
            }
        }

        impl T2 for int {
            type X = bool;
        }

        impl<A: T2> T3 for S<A> where <A as T2>::X: T1 {
            proof fn f3() {
                <<A as T2>::X as T1>::f1();
            }
        }

        proof fn test() ensures false {
            <S<int> as T3>::f3();
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_6 verus_code! {
        pub trait T {
            spec fn f(n: int) -> int;
        }

        impl T for bool {
            open spec fn f(n: int) -> int
                decreases n
            {
                if n <= 0 { 0 } else { 1 + Self::f(n - 1) }
            }
        }

        impl T for u8 {
            open spec fn f(n: int) -> int
                decreases n
            {
                if n <= 0 { 0 } else { 1 + Self::f(n - 1) }
            }
        }

        proof fn test() {
            reveal_with_fuel(<u8 as T>::f, 3);
            assert(<u8 as T>::f(2) == 2);
            assert(<bool as T>::f(20) == 20); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[ignore] #[test] test_termination_bounds_1 verus_code! {
        trait T {
            spec fn f(&self) -> bool;
        }

        trait U: T {
        }

        spec fn rec<A: U>(x: &A) -> bool {
            x.f()
        }

        struct S {}

        impl T for S {
            spec fn f(&self) -> bool {
                rec(self)
            }
        }

        impl U for S {
        }

        proof fn test() {
            let s = S {};
            s.f();
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_bounds_1b verus_code! {
        trait T<A> {
            spec fn f() -> int;
        }

        trait U<A>: T<A> {
        }

        struct S<B>(B);
        impl<A> T<A> for S<A> {
            spec fn f() -> int {
                h() + 1
            }
        }

        impl<A> U<A> for S<A> {
        }

        spec fn g<X, Y: U<X>>() -> int {
            Y::f() + 1
        }

        spec fn h() -> int {
            g::<bool, S<bool>>() + 1
        }

        proof fn test()
            ensures false
        {
            assert(h() == g::<bool, S<bool>>() + 1);
            assert(h() == h() + 3);
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_bounds_2 verus_code! {
        trait T {
            spec fn f<A: U>(&self, x: &A);
        }

        trait U: T {
        }

        struct S {}

        impl T for S {
            spec fn f<A: U>(&self, x: &A) {
                x.f(x)
            }
        }

        impl U for S {
        }

        proof fn test() {
            let s = S {};
            s.f(&s);
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_bounds_3 verus_code! {
        trait T {
            spec fn f(&self);
        }

        trait U {
            spec fn g(&self);
        }

        struct S {}

        impl T for S where S: U {
            spec fn f(&self) {
                self.g()
            }
        }

        impl U for S {
            spec fn g(&self) {
                self.f()
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition, which may result in nontermination")
}

test_verify_one_file! {
    #[test] test_termination_bounds_unsupported_0 verus_code! {
        trait T {
            fn f(&self, x: &Self, n: u64);
        }
        trait U {
            fn g(&self, x: &Self, n: u64);
        }
        struct S {}
        impl T for S where S: U {
            fn f(&self, x: &Self, n: u64)
                decreases n
            {
                if n > 0 {
                    self.g(x, n - 1);
                    x.g(self, n - 1);
                }
            }
        }
        impl U for S {
            fn g(&self, x: &Self, n: u64)
                decreases n
            {
                if n > 0 {
                    self.f(x, n - 1);
                    x.f(self, n - 1);
                }
            }
        }
    } => Err(err) => {
        // TODO: we could make the recursion rules more precise to allow decreases checking in this example
        assert_vir_error_msg(err, "found a cyclic self-reference in a definition, which may result in nontermination")
    }
}

test_verify_one_file! {
    #[test] test_termination_4_bounds_supported_1 verus_code! {
        trait T {
            proof fn f(&self, n: int);
        }
        trait U: T {
            proof fn g(&self, n: int);
        }
        struct S {}
        impl T for S {
            proof fn f(&self, n: int)
                decreases n
            {
                if 0 < n {
                    h(self, n - 1); // FAILS
                }
            }
        }
        impl U for S {
            proof fn g(&self, n: int)
                decreases n
            {
                if 0 < n {
                    self.f(n - 1); // FAILS
                }
            }
        }
        proof fn h(x: &S, n: int) {
            if 0 < n {
                x.g(n - 1);
            }
        }
    } => Err(err) => {
        assert_vir_error_msg(err, "recursive function must have a decreases clause")
    }
}

test_verify_one_file! {
    #[test] test_termination_4_bounds_supported_2 verus_code! {
        trait T {
            proof fn f(&self, n: int);
        }
        trait U: T {
            proof fn g(&self, n: int);
        }
        struct S {}
        impl T for S {
            proof fn f(&self, n: int)
                decreases n
            {
                if 0 < n {
                    h(self, n - 1); // FAILS
                }
            }
        }
        impl U for S {
            proof fn g(&self, n: int)
                decreases n
            {
                if 0 < n {
                    self.f(n - 1); // FAILS
                }
            }
        }
        proof fn h(x: &S, n: int)
            decreases n
        {
            if 0 < n {
                x.g(n - 1);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_termination_assoc_bounds_fail_1 verus_code! {
        trait Z { }
        trait T { type X: Z; }
        struct Q<A: T>(A::X);
        struct R;
        impl T for R { type X = S; }
        struct S(spec_fn(Q<R>) -> int);
        impl Z for S { }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_termination_assoc_bounds_fail_2 verus_code! {
        trait Z { type Y; }
        trait T { type X: Z; }
        struct Q<A: T>(<<A as T>::X as Z>::Y);
        struct R;
        impl T for R { type X = S; }
        struct S(spec_fn(Q<R>) -> int);
        impl Z for S {
            type Y = S;
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_assoc_bounds_2_pass verus_code! {
        trait Z { type Y; }
        trait T {
            type X: Z;

            fn val() -> <Self::X as Z>::Y;
        }
        struct ZZ { }
        impl Z for ZZ {
            type Y = u64;
        }
        struct TT { }
        impl T for TT {
            type X = ZZ;

            fn val() -> <Self::X as Z>::Y {
                3
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_assoc_bounds_regression_955 verus_code! {
        use vstd::prelude::View;

        pub trait A {
            type Input: View;
            type Output: View;
        }

        pub trait B {
            type MyA: A;

            fn foo(input: <Self::MyA as A>::Input) -> <Self::MyA as A>::Output;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_termination_assoc_bounds_fail_3 verus_code! {
        trait Z { type Y; }
        trait T { type X: Z; }

        struct S<W: T>(<<W as T>::X as Z>::Y);

        struct ZZ { }
        impl Z for ZZ { type Y = S<TT>; }

        struct TT { }
        impl T for TT { type X = ZZ; }

        spec fn arbitrary<A>() -> A;

        spec fn foo(n: nat) -> S<TT>
            decreases n
        {
            if n > 0 {
                S(foo((n - 1) as nat))
            } else {
                arbitrary()
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_assoc_bounds_4_pass verus_code! {
        trait U<'a> {
            type X;
        }

        trait T<'a> {
            type Y: U<'a>;
        }

        proof fn f<'a, A: T<'a>>(
            x: <<A as T<'a>>::Y as U<'a>>::X
        ) {
        }

        struct S<A, 'a> {
            s: &'a A,
        }

        fn g<'a>(s: S<u8, 'a>) {
            let x = s.s;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_assoc_bounds_holes verus_code! {
        // tests "holes" generated by vir::traits::hide_projections
        // https://github.com/verus-lang/verus/issues/1239
        trait T<A> {
            type X;
        }

        trait U<A, B> {
            spec fn f() -> int;
        }

        struct S<A>(A);

        impl<A, B: T<A>> U<A, B> for S<B::X> {
            spec fn f() -> int decreases 0int { if true { 7 } else { <S<B::X> as U<A, B>>::f() } }
        }

        impl<A> T<A> for bool {
            type X = int;
        }

        proof fn test() {
            assert(<S<int> as U<u8, bool>>::f() == 7);
        }

        proof fn test2() {
            assert(<S<int> as U<u8, bool>>::f() == 8); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_assoc_bounds_holes_default_method verus_code! {
        // tests "holes" generated by vir::traits::hide_projections
        // https://github.com/verus-lang/verus/issues/1239
        trait T {
            type X;
        }

        struct S<A>(A);
        struct R<A>(A);

        impl<A> T for S<A> {
            type X = int;
        }

        trait U<A> {
            spec fn f() -> int {
                7
            }
        }

        impl<A: T> U<A::X> for R<A> {}

        fn test() {
            assert(<R<S<int>> as U<int>>::f() == 7);
        }

        fn test2() {
            assert(<R<S<int>> as U<int>>::f() == 8); // FAILS
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
    #[test] test_verify_3_not_named_self verus_code! {
        trait T {
            spec fn req(not_named_self: &Self) -> bool;
            fn f(not_named_self: &Self)
                requires Self::req(not_named_self);
        }
        struct S {}
        impl T for S {
            spec fn req(not_named_self: &Self) -> bool { false }
            fn f(not_named_self: &Self) {}
        }
        fn test() {
            let s = S {};
            S::f(&s); // FAILS
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
            vstd::pervasive::print_u64(p(&10, &i)); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_verify_6_no_self verus_code! {
        trait T<A> {
            spec fn req(a: A) -> bool;
            spec fn ens(a: A, r: A) -> bool;

            fn f(a: &A) -> (ra: A)
                requires Self::req(*a)
                ensures Self::ens(*a, ra); // TRAIT
        }

        struct B {
            x: bool,
        }

        struct I {
            x: u64,
        }

        impl T<bool> for B {
            spec fn req(a: bool) -> bool {
                a
            }

            spec fn ens(a: bool, r: bool) -> bool {
                r == !a
            }

            fn f(a: &bool) -> bool {
                !*a
            }
        }

        impl T<u64> for I {
            spec fn req(a: u64) -> bool {
                a < 100
            }

            spec fn ens(a: u64, r: u64) -> bool {
                r < 100
            }

            fn f(a: &u64) -> u64 {
                a * 2
            } // FAILS
        }

        fn p<A, Z: T<A>>(a: &A) -> (rz: A)
            requires Z::req(*a)
            ensures Z::ens(*a, rz)
        {
            Z::f(a)
        }

        fn test() {
            vstd::pervasive::print_u64(p::<u64, I>(&105)); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_verify_loop verus_code! {
        trait T {
            spec fn f() -> bool;
        }

        spec fn g<A: T>(i: int) -> int decreases i { 7 }

        fn test<A: T>(b: bool) {
            assert(1 + 1 == 2);
            assert(<A as T>::f() == <A as T>::f());
            assert(g::<A>(5) == 7);
            while b {
                assert(2 + 2 == 4);
                assert(<A as T>::f() == <A as T>::f());
                assert(g::<A>(5) == 7);
            }
        }
    } => Ok(())
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
    #[test] test_generic_4 verus_code! {
        trait U1 {}
        trait U2 {}

        trait T<A0, A1: U1> {
            fn f<A2: U2 + Copy, A3>(a1: &A1, a2: &A2, a3: &A3) -> (r: (A2, A2))
                requires
                    a1 == a1,
                    a2 == a2,
                    a3 == a3,
                ensures
                    r.0 == *a2
                ;
        }

        impl U1 for bool {}
        impl U1 for u64 {}
        impl U2 for u16 {}
        impl U2 for bool {}

        impl T<int, bool> for u8 {
            fn f<A2x: U2 + Copy, A3x>(a1: &bool, a2: &A2x, a3: &A3x) -> (A2x, A2x) {
                (*a2, *a2)
            }
        }

        struct S<B>(B);
        impl<B: U1> T<int, B> for S<B> {
            fn f<A2x: U2 + Copy, A3x>(a1: &B, a2: &A2x, a3: &A3x) -> (A2x, A2x) {
                (*a2, *a2)
            }
        }

        fn test() {
            let (x, y) = <u8 as T<int, bool>>::f::<u16, u32>(&true, &100u16, &200u32);
            assert(x == 100);
            let (x, y) = <S::<u64> as T<int, u64>>::f::<bool, u8>(&300u64, &true, &10u8);
            assert(x);
            assert(y); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
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
    #[test] test_bounds_axioms verus_code! {
        trait T {
            spec fn f() -> int;
        }

        trait U: T {}

        struct S<C>(C);

        impl<C: T> T for S<C> {
            spec fn f() -> int {
                <C as T>::f()
            }
        }

        proof fn test<C: U>(x: &S<C>) {
            assert(<C as T>::f() == <S<C> as T>::f());
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_broadcast_forall1 verus_code! {
        trait T {
            spec fn f(&self) -> bool;

            proof fn p(&self)
                ensures exists|x: &Self| self.f() != x.f();
        }

        spec fn g<A: T>() -> bool {
            exists|x: &A, y: &A| x.f() != y.f()
        }
        spec fn t<A>() -> bool { true }

        #[verifier::external_body]
        broadcast proof fn f_not_g<A: T>()
            ensures
                #[trigger] t::<A>(),
                g::<A>(),
        {
        }

        struct S1 {}
        impl T for S1 {
            spec fn f(&self) -> bool {
                true
            }

            proof fn p(&self) {
                broadcast use f_not_g;
                assert(exists|x: &Self| self.f() != x.f()); // FAILS
            }
        }

        struct S2 {}

        struct S3(bool);
        impl T for S3 {
            spec fn f(&self) -> bool {
                self.0
            }

            proof fn p(&self) {
                broadcast use f_not_g;
                assert(self.f() != S3(!self.0).f())
            }
        }

        fn test1() {
            broadcast use f_not_g;
            assert(t::<S1>());
            assert(false);
        }

        fn test2() {
            broadcast use f_not_g;
            assert(t::<S2>());
            assert(false); // FAILS
        }

        fn test3() {
            broadcast use f_not_g;
            assert(t::<S3>());
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_broadcast_forall2 verus_code! {
        trait T1<A, B> {}
        trait T2<C, D> {}

        struct S<E>(E);

        impl<X> T1<X, bool> for S<X> {}
        impl<Y, Z: T1<int, Y>> T2<Z, u16> for S<(Y, u8)> {}

        spec fn f<A>(i: int) -> bool;

        #[verifier::external_body]
        broadcast proof fn p<A: T2<S<int>, u16>>(i: int)
            ensures f::<A>(i)
        {
        }

        proof fn test1() {
            broadcast use p;
            assert(f::<S<(bool, u8)>>(3));
        }

        proof fn test2() {
            broadcast use p;
            assert(f::<S<(u32, u8)>>(3)); // FAILS
        }

        proof fn test3() {
            broadcast use p;
            assert(f::<S<(bool, u32)>>(3)); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_broadcast_forall_causes_cycle verus_code! {
        mod M {
            pub trait Tr {
                spec fn f() -> bool;

                proof fn bad() ensures false;
            }

            // note the external_body isn't necessary here
            #[verifier::external_body]
            pub broadcast proof fn proves_false_requiring_trait_bound<T: Tr>()
                ensures #[trigger] T::f() == !T::f(),
            {
                T::bad();
            }
        }

        use M::*;

        struct X { }

        impl Tr for X {
            open spec fn f() -> bool
            {
                true
            }

            proof fn bad() {
                other_bad();
            }
        }

        pub proof fn other_bad()
            ensures false, // FAILS
        {
            // It is important that the Trait-Impl-Axiom axiom for "impl Tr for X"
            // (axiom (tr_bound%M.Tr. $ TYPE%X.)
            // appears after "impl Tr for X" and its dependencies.
            // Since "impl Tr for X" depends on other_bad,
            // this ensures that the the Trait-Impl-Axiom axiom for "impl Tr for X"
            // also appears after other_bad.
            // This ensures that the broadcast_forall for proves_false_requiring_trait_bound
            // isn't enabled (its precondition isn't satisfied) for "Tr for X" until
            // after "impl Tr for X" and other_bad are checked.
            // Otherwise, the axiom could be used here in other_bad to prove false.
            let t = X::f();
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_broadcast_forall_causes_cycle_simple verus_code! {
        pub trait Tr {
            spec fn f() -> bool;

            proof fn bad() ensures false; // FAILS
        }

        #[verifier::external_body]
        pub broadcast proof fn proves_false_requiring_trait_bound<T: Tr>()
            ensures
                #[trigger] T::f() == !T::f(),
        { }

        struct X { }

        impl Tr for X {
            open spec fn f() -> bool { true }

            proof fn bad() {
                assert(Self::f());
            }
        }
    } => Err(err) => assert_one_fails(err)
}

const DECREASES_TRAIT_BOUND_COMMON: &str = verus_code_str! {
    trait T {
        proof fn impossible()
            ensures false;
    }

    spec fn f<A: T>(i: int) -> bool
        decreases 0int via f_decreases::<A>
    {
        !f::<A>(i - 0)
    }

    #[verifier::decreases_by]
    proof fn f_decreases<A: T>(i: int) {
        A::impossible();
    }

    struct B { }

    proof fn test1<A: T>(i: int) {
        assert(f::<A>(i) == !f::<A>(i - 0));
        assert(false);
    }
};

// NOTE: running with
// VERUS_EXTRA_ARGS="--log-all" vargo nextest run -p rust_verify_test --vstd-no-verify --test traits -- test_decreases_trait_bound_unsound
// can help debug AIR issues that result in SIGABRT in tests
test_verify_one_file_with_options! {
    #[test] test_decreases_trait_bound_unsound ["-V allow-inline-air"] => DECREASES_TRAIT_BOUND_COMMON.to_string() + verus_code_str! {
        proof fn test2(i: int) {
            // We'd like to test that f's definition axiom only applies to A that implement T.
            // Ideally, we'd test this by applying f to an A that doesn't implement T
            // and seeing that the definition axiom doesn't apply.
            // Unfortunately, it's hard to test this because Rust's type checker already (correctly)
            // stops us from saying f::<ty>(x) for ty that doesn't implement T.

            // So we manually emit the AIR that corresponds to the f::<B>(x) call.
            inline_air_stmt("(assume (tr_bound%T. $ TYPE%B.))");
            inline_air_stmt("(assert (= (f.? $ TYPE%B. (I i!)) (not (f.? $ TYPE%B. (I (Sub i! 0))))))");
            inline_air_stmt("(assume (= (f.? $ TYPE%B. (I i!)) (not (f.? $ TYPE%B. (I (Sub i! 0))))))");
            assert(false);
        }
    } => Ok(())
}

// NOTE: running with
// VERUS_EXTRA_ARGS="--log-all" vargo nextest run -p rust_verify_test --vstd-no-verify --test traits -- test_decreases_trait_bound_unsound
// can help debug AIR issues that result in SIGABRT in tests
test_verify_one_file_with_options! {
    #[test] test_decreases_trait_bound_sound ["-V allow-inline-air"] => DECREASES_TRAIT_BOUND_COMMON.to_string() + verus_code_str! {
        proof fn test2(i: int) {
            // We'd like to test that f's definition axiom only applies to A that implement T.
            // Ideally, we'd test this by applying f to an A that doesn't implement T
            // and seeing that the definition axiom doesn't apply.
            // Unfortunately, it's hard to test this because Rust's type checker already (correctly)
            // stops us from saying f::<ty>(x) for ty that doesn't implement T.

            // So we manually emit the AIR that corresponds to the f::<B>(x) call.
            // inline_air_stmt("(assume (tr_bound%T. $ TYPE%B.))");
            inline_air_stmt("(assert (= (f.? $ TYPE%B. (I i!)) (not (f.? $ TYPE%B. (I (Sub i! 0))))))");
        }
    } => Err(err) => { assert!(err.errors.len() == 1); }
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

test_verify_one_file! {
    #[test] issue311_overlapping_names_ensures verus_code!{
        trait Tr<T> {
            spec fn f(&self) -> T;

            fn compute_f(&self) -> (t: T)
                ensures t === self.f();
        }

        struct Z<T> { a: T, b: T }

        impl<T: Copy> Tr<T> for Z<T> {

            spec fn f(&self) -> T {
                self.a
            }

            fn compute_f(&self) -> (t: T)
            {
                self.a
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] issue311_overlapping_names_requires verus_code!{
        trait Tr<T> {
            spec fn f(&self) -> T;

            fn compute_f(&self, t: T)
                requires t === self.f();
        }

        struct Z<T> { a: T, b: T }

        impl<T: Copy> Tr<T> for Z<T> {

            spec fn f(&self) -> T {
                self.a
            }

            fn compute_f(&self, t: T)
            {
                assert(t === self.f());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impl_trait_bound verus_code! {
        trait T1 {}
        trait T2 {
            fn f(&self);
        }
        struct S2<A> {
            a: A,
        }
        impl<A: T1> T2 for S2<A> {
            fn f(&self) {
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impl_trait_bound_cycle verus_code! {
        spec fn g<A: T1>(a: &A) -> bool {
            true
        }
        struct S1 {
        }
        trait T1 {
            fn r(&self) -> bool
                requires g(&S1{});
        }
        impl T1 for S1 {
            fn r(&self) -> bool {
                true
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition, which may result in nontermination")
}

test_verify_one_file! {
    #[test] test_impl_trait_bound_cycle1 verus_code! {
        trait T {
            spec fn f() -> int;
        }
        struct S<A>(A);
        impl<A: T> T for S<A> {
            spec fn f() -> int { A::f() + 1 }
        }
        impl T for bool {
            // This instantiates A with A = bool, which recursively uses "impl T for bool"
            // to satisfy A: T.
            // For soundness, this must be considered a cycle and prohibited.
            spec fn f() -> int { S::<bool>::f() }
        }
        proof fn test()
            ensures false
        {
            assert(S::<bool>::f() == S::<bool>::f() + 1);
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition, which may result in nontermination")
}

test_verify_one_file! {
    #[test] test_impl_trait_bound_cycle2 verus_code! {
        struct S1 {
        }
        trait T1 {
            fn r(&self, s: &S2<S1>) -> bool
                requires s.f();
        }
        impl T1 for S1 {
            fn r(&self, s: &S2<S1>) -> bool {
                true
            }
        }
        trait T2 {
            spec fn f(&self) -> bool;
        }
        struct S2<A> {
            a: A,
        }
        impl<A: T1> T2 for S2<A> {
            spec fn f(&self) -> bool {
                true
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition, which may result in nontermination")
}

test_verify_one_file! {
    #[test] test_impl_trait_bound_cycle3 verus_code! {
        struct R {}
        struct S {}
        impl U for R {
            fn m() {}
        }
        impl T<R> for S {}
        spec fn g<A: T<R>>() -> bool { true }
        spec fn f() -> bool { g::<S>() }
        trait U {
            fn m() requires f();
        }
        trait T<A: U> {}
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition, which may result in nontermination")
}

test_verify_one_file! {
    #[test] test_impl_trait_bound_cycle4 verus_code! {
        trait T {
            spec fn f() -> bool;
        }

        trait U<A: T> {
            spec fn p() -> bool
                recommends
                    A::f();
        }

        impl T for u8 {
            spec fn f() -> bool decreases 0int {
                <u32 as U<u8>>::p() // FAILS
            }
        }

        impl U<u8> for u32 {
            spec fn p() -> bool decreases 0int { true }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_impl_trait_req_ens_graph_edge verus_code! {
        // https://github.com/verus-lang/verus/issues/1235
        // tests Node::TraitReqEns
        pub trait T {
            spec fn f(&self) -> int;
        }

        pub trait U : T + Sized {
            proof fn p1(v: Self)
                ensures v.f() < 10;

            proof fn p2(&self) {
                Self::p1(*self);
            }
        }

        impl T for u32 {
            open spec fn f(&self) -> int { 5 }
        }

        impl U for u32 {
            proof fn p1(v: Self) {
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_fn_with_0_params verus_code! {
        trait Tr {
            spec fn f() -> int;

            fn exec_f() -> (i: u64)
                ensures i as int == Self::f();
        }

        struct X {}
        struct Y {}

        impl Tr for X {
            spec fn f() -> int { 5 }

            fn exec_f() -> u64 {
                5
            }
        }

        impl Tr for Y {
            spec fn f() -> int { 6 }

            fn exec_f() -> u64 {
                6
            }
        }

        proof fn test() {
            assert(X::f() == 5);
            assert(Y::f() == 6);
        }

        proof fn test2() {
            assert(X::f() == Y::f()); // FAILS
        }

        proof fn test3<A: Tr, B: Tr>() {
            assert(A::f() == B::f()); // FAILS
        }

        fn test4() {
            let x1 = X::exec_f();
            let x2 = X::exec_f();
            assert(x1 == x2);
        }

        fn test5() {
            let x1 = X::exec_f();
            let x2 = Y::exec_f();
            assert(x1 == x2); // FAILS
        }

        fn test6<A: Tr, B: Tr>() {
            let x1 = A::exec_f();
            let x2 = B::exec_f();
            assert(x1 == x2); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] trait_req_ens_poly verus_code! {
        pub trait Key: Sized {
            spec fn lt(self) -> bool;

            proof fn zero_properties()
                ensures
                    forall|k: Self| k.lt();
        }

        struct KeyInt {
            i: usize,
        }

        impl Key for KeyInt {
            closed spec fn lt(self) -> bool { true }
            proof fn zero_properties() {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_implement_all_trait_items verus_code! {
        trait T {
            proof fn unprovable(&self)
                ensures false;
        }
        struct S { }
        impl T for S { }

        proof fn foo<J: T>(t: J)
            ensures false
        {
            t.unprovable();
            assert(false);
        }

        proof fn some_proof() {
            let s = S { };
            foo::<S>(s);
            assert(false);
        }
    } => Err(err) => assert_rust_error_msg(err, "not all trait items implemented, missing: `unprovable`")
}

test_verify_one_file! {
    #[test] proof_fn_spec_self verus_code! {
        trait Bar {
            proof fn bar(&self, other: &Self);
        }

        proof fn consume<V>(v: V) { }

        struct X;
        impl Bar for X {
            proof fn bar(&self, other: &Self)
            {
                consume(*self); // fine, since 'self' is spec-mode
                consume(*self);
            }
        }

        trait Qux {
            proof fn bar(&self, other: &Self)
                ensures self != other; // FAILS
        }

        struct Y { some_int: u8 }
        impl Qux for Y {
            proof fn bar(&self, other: &Self)
            {
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] proof_fn_spec_self_with_proof_arg verus_code! {
        trait Bar {
            proof fn bar(&self, tracked other: &Self);
        }

        proof fn consume<V>(tracked v: V) { }

        struct X;
        impl Bar for X {
            proof fn bar(&self, tracked other: &Self)
            {
                consume(*other);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot move out of `*other` which is behind a shared reference")
}

test_verify_one_file! {
    #[test] test_specialize_self_types verus_code! {
        trait T { spec fn f(&self) -> int; }
        struct S {}
        impl T for S { spec fn f(&self) -> int { 1 } }
        impl T for int { spec fn f(&self) -> int { 2 + *self } }
        impl T for spec_fn(int) -> int { spec fn f(&self) -> int { (*self)(3) } }

        proof fn test(x: int, y: spec_fn(int) -> int) {
            assert(x.f() == x + 2);
            assert(y.f() == y(3));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_specialize_self_types_fail verus_code! {
        trait T { spec fn f(&self) -> int; }
        struct S {}
        impl T for S { spec fn f(&self) -> int { 1 } }
        impl T for int { spec fn f(&self) -> int { 2 + *self } }
        impl T for spec_fn(int) -> int { spec fn f(&self) -> int { (*self)(3) } }

        proof fn test(x: int, y: spec_fn(int) -> int) {
            assert(x.f() == x + 2);
            assert(y.f() == y(3));
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_specialize1 verus_code! {
        trait T { spec fn f(&self) -> bool; }
        struct S<A> { a: A }
        impl T for S<u8> { spec fn f(&self) -> bool { true } }
        impl T for S<bool> { spec fn f(&self) -> bool { false } }
        proof fn test(x: S<u8>, y: S<bool>) {
            assert(x.f());
            assert(!y.f());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_specialize1_fails verus_code! {
        trait T { spec fn f(&self) -> bool; }
        struct S<A> { a: A }
        impl T for S<u8> { spec fn f(&self) -> bool { true } }
        impl T for S<bool> { spec fn f(&self) -> bool { false } }
        proof fn test(x: S<u8>, y: S<bool>) {
            assert(x.f() == y.f()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_specialize2 verus_code! {
        trait T { spec fn f() -> bool; }
        struct S<A> { a: A }
        impl T for S<u8> { spec fn f() -> bool { true } }
        impl T for S<bool> { spec fn f() -> bool { false } }
        proof fn test() {
            assert(S::<u8>::f());
            assert(!S::<bool>::f());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_specialize2_fails verus_code! {
        trait T { spec fn f() -> bool; }
        struct S<A> { a: A }
        impl T for S<u8> { spec fn f() -> bool { true } }
        impl T for S<bool> { spec fn f() -> bool { false } }
        proof fn test() {
            assert(S::<u8>::f() == S::<bool>::f()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_specialize2_decorated_fails verus_code! {
        trait T { spec fn f() -> bool; }
        struct S<A> { a: A }
        impl T for S<u8> { spec fn f() -> bool { true } }
        impl T for S<&u8> { spec fn f() -> bool { false } }
        proof fn test() {
            assert(S::<u8>::f() == S::<&u8>::f()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_specialize3 verus_code! {
        trait T<A> { spec fn f(&self, a: A) -> bool; }
        struct S {}
        impl T<u8> for S { spec fn f(&self, a: u8) -> bool { true } }
        impl T<u16> for S { spec fn f(&self, a: u16) -> bool { false } }
        proof fn test(x: S) {
            assert(x.f(1u8));
            assert(!x.f(1u16));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_specialize3_fails verus_code! {
        trait T<A> { spec fn f(&self, a: A) -> bool; }
        struct S {}
        impl T<u8> for S { spec fn f(&self, a: u8) -> bool { true } }
        impl T<u16> for S { spec fn f(&self, a: u16) -> bool { false } }
        proof fn test(x: S) {
            assert(x.f(1u8) == x.f(1u16)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_specialize4 verus_code! {
        trait T<A> { spec fn f(a: A) -> bool; }
        struct S {}
        impl T<u8> for S { spec fn f(a: u8) -> bool { true } }
        impl T<u16> for S { spec fn f(a: u16) -> bool { false } }
        proof fn test() {
            assert(S::f(1u8));
            assert(!S::f(1u16));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_specialize4_fails verus_code! {
        trait T<A> { spec fn f(a: A) -> bool; }
        struct S {}
        impl T<u8> for S { spec fn f(a: u8) -> bool { true } }
        impl T<u16> for S { spec fn f(a: u16) -> bool { false } }
        proof fn test() {
            assert(S::f(1u8) == S::f(1u16)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_specialize4_decorated_fails verus_code! {
        trait T<A> { spec fn f(a: A) -> bool; }
        struct S {}
        impl T<u8> for S { spec fn f(a: u8) -> bool { true } }
        impl T<&u8> for S { spec fn f(a: &u8) -> bool { false } }
        proof fn test() {
            assert(S::f(1u8) == S::f(&1u8)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_specialize_dispatch_by_bound verus_code! {
        struct S;
        trait U {}

        trait T { spec fn f() -> int; }
        impl T for S { spec fn f() -> int { 100 } }
        impl<A: U> T for A { spec fn f() -> int { 200 } }

        proof fn test() {
            assert(<S as T>::f() == 100);
            assert(<S as T>::f() == 200); // FAILS
            assert(false);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_specialize_dispatch_by_bound_copy verus_code! {
        struct S;
        trait T { spec fn f() -> int; }
        impl T for S { spec fn f() -> int { 200 } }
        impl<A: Copy> T for A { spec fn f() -> int { 100 } }
        proof fn test() {
            assert(<S as T>::f() == 100);
            assert(<S as T>::f() == 200); // FAILS
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "conflicting implementations")
    // TODO: } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_specialize_dispatch_by_bound_tuple verus_code! {
        struct S;
        trait T { spec fn f() -> int; }
        impl T for S { spec fn f() -> int { 200 } }
        impl<A: core::marker::Tuple> T for A { spec fn f() -> int { 100 } }
        proof fn test() {
            assert(<S as T>::f() == 100);
            assert(<S as T>::f() == 200); // FAILS
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "conflicting implementations")
    // TODO: } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_specialize_dispatch_by_bound_sized verus_code! {
        struct S([u8]);
        trait T { spec fn f() -> int; }
        impl T for S { spec fn f() -> int { 200 } }
        impl<A: Sized> T for A { spec fn f() -> int { 100 } }
        proof fn test() {
            assert(<S as T>::f() == 100);
            assert(<S as T>::f() == 200); // FAILS
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "conflicting implementations")
    // TODO: } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_specialize_dispatch_by_bound_send verus_code! {
        struct S;
        impl !Send for S {}
        trait T { spec fn f() -> int; }
        impl T for S { spec fn f() -> int { 200 } }
        impl<A: Send> T for A { spec fn f() -> int { 100 } }
        proof fn test() {
            assert(<S as T>::f() == 100);
            assert(<S as T>::f() == 200); // FAILS
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "conflicting implementations")
    // TODO: } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_specialize_dispatch_by_bound_sync verus_code! {
        struct S;
        impl !Sync for S {}
        trait T { spec fn f() -> int; }
        impl T for S { spec fn f() -> int { 200 } }
        impl<A: Sync> T for A { spec fn f() -> int { 100 } }
        proof fn test() {
            assert(<S as T>::f() == 100);
            assert(<S as T>::f() == 200); // FAILS
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "conflicting implementations")
    // TODO: } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_specialize_dispatch_by_bound_unpin verus_code! {
        struct S;
        impl !Unpin for S {}
        trait T { spec fn f() -> int; }
        impl T for S { spec fn f() -> int { 200 } }
        impl<A: Unpin> T for A { spec fn f() -> int { 100 } }
        proof fn test() {
            assert(<S as T>::f() == 100);
            assert(<S as T>::f() == 200); // FAILS
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "conflicting implementations")
    // TODO: } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_specialize_dispatch_by_bound_defaults verus_code! {
        trait T {
            spec fn f() -> int { 3 }
            proof fn test();
        }

        impl T for bool {
            proof fn test() {
                assert(Self::f() == 3);
            }
        }

        trait U {}
        impl<A: U> T for A {
            proof fn test() {}
        }

        impl T for u8 {
            spec fn f() -> int { 4 }
            proof fn test() {}
        }

        proof fn test() {
            assert(<u8 as T>::f() == 4);
            assert(<u8 as T>::f() == 3); // FAILS
            assert(false);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_trait_inline verus_code! {
        pub trait T<A> { spec fn f(&self) -> int; }
        struct S { }
        impl T<u16> for S {
            #[verifier::inline]
            open spec fn f(&self) -> int { 7 }
        }
        proof fn test(x: &S) {
            assert(x.f() == 7);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_trait_inline_fails verus_code! {
        pub trait T<A> { spec fn f(&self) -> int; }
        struct S { }
        impl T<u16> for S {
            #[verifier::inline]
            open spec fn f(&self) -> int { 7 }
        }
        proof fn test(x: &S) {
            assert(x.f() == 8); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_trait_inline2 verus_code! {
        struct S<A> { a: A }
        trait T<A> { spec fn f(&self, i: int) -> A; }
        spec fn arbitrary<A>() -> A;
        impl<B> T<(B, bool)> for S<B> {
            #[verifier(inline)]
            spec fn f(&self, i: int) -> (B, bool) { arbitrary() }
        }
        proof fn foo(x: S<u64>)
            requires x.f(33) == (19u64, true),
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] recommends_in_ensures_issue370 verus_code! {
        trait Foo  {
            spec fn specfoo(&self)->bool
              recommends true;

            exec fn execfoo(&self)
              ensures self.specfoo(); // FAILS
        }

        struct Bar;
        impl Foo for Bar {
            spec fn specfoo(&self) -> bool {
                false // Just to trigger a verif failure
            }

            exec fn execfoo(&self) {
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] trait_fn_opaqueness verus_code! {
        trait Foo {
            #[verifier::opaque]
            spec fn foo(&self) -> bool;
        }
    } => Err(err) => assert_vir_error_msg(err, "opaque has no effect on a function without a body")
}

test_verify_one_file! {
    #[test] disallow_drop_with_requires verus_code! {
        struct A { v: u64 }

        impl Drop for A {
            fn drop(&mut self)
                requires false
                no_unwind
            {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "requires are not allowed on the implementation for Drop")
}

test_verify_one_file! {
    #[test] allow_drop_without_requires_and_opens_invariants_none verus_code! {
        struct A { v: u64 }

        impl Drop for A {
            fn drop(&mut self)
                opens_invariants none
                no_unwind
            { }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] disallow_external_drop verus_code! {
        struct A { v: u64 }

        impl Drop for A {
            #[verifier::external]
            fn drop(&mut self)
            {
                let x = 1 / 0;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "an item in a trait impl cannot be marked external")
}

test_verify_one_file! {
    #[test] allow_external_body_drop verus_code! {
        struct A { v: u64 }

        impl Drop for A {
            #[verifier::external_body]
            fn drop(&mut self)
                opens_invariants none
                no_unwind
            {
                let x = 1 / 0;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] disallow_external_body_drop_with_requires verus_code! {
        struct A { v: u64 }

        impl Drop for A {
            #[verifier::external_body]
            fn drop(&mut self)
                requires false
            {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "requires are not allowed on the implementation for Drop")
}

test_verify_one_file! {
    #[test] diallow_open_invariants_on_drop verus_code! {
        struct A { v: u64 }

        impl Drop for A {
            fn drop(&mut self)
                no_unwind
            {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "the implementation for Drop must be marked opens_invariants none")
}

test_verify_one_file! {
    #[test] diallow_unwind_on_drop verus_code! {
        struct A { v: u64 }

        impl Drop for A {
            fn drop(&mut self)
                opens_invariants none
            {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "the implementation for Drop must be marked no_unwind")
}

test_verify_one_file! {
    #[test] allow_unwrapping_syntax_for_trait_exec_decls verus_code! {
        tracked struct AType {
            v: nat,
        }

        trait ATrait {
            exec fn afun(Tracked(aparam): Tracked<&mut AType>)
                requires old(aparam) == (AType { v: 41 }),
                ensures aparam == (AType { v: 41 });
        }

        struct AnotherType {}

        impl ATrait for AnotherType {
            exec fn afun(Tracked(aparam): Tracked<&mut AType>) {
                assert(aparam.v == 41);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_argument_names_issue278_1 verus_code! {
        trait T {
            fn f(&self, a: usize) -> (res: usize)
                ensures res == a;
        }

        struct S { }

        impl T for S {
            fn f(&self, b: usize) -> usize {
                b
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_argument_names_issue278_2 verus_code! {
        trait T {
            fn f(&self, a: usize) -> (res: usize)
                ensures res == a;
        }

        struct S { }

        impl T for S {
            fn f(&self, b: usize) -> (result: usize) {
                b
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_argument_names_issue278_3 verus_code! {
        trait T {
            fn f(&self, a: usize) -> (res: usize)
                ensures res == a; // FAILS
        }

        struct S { }

        impl T for S {
            fn f(&self, b: usize) -> (result: usize) {
                0
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] impl_of_non_private_trait_fn_must_be_open_or_closed_1_regression_382 verus_code! {
        mod m1 {
            pub trait SomeTrait {
                spec fn foo(&self) -> bool;
            }

            struct SomeType { b: bool }

            impl SomeTrait for SomeType {
                spec fn foo(&self) -> bool {
                    self.b
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "open/closed is required for implementations of non-private traits")
}

test_verify_one_file! {
    #[test] impl_of_non_private_trait_fn_must_be_open_or_closed_2_regression_382 verus_code! {
        mod m1 {
            pub(super) trait SomeTrait {
                spec fn foo(&self) -> bool;
            }

            struct SomeType { b: bool }

            impl SomeTrait for SomeType {
                spec fn foo(&self) -> bool {
                    self.b
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "open/closed is required for implementations of non-private traits")
}

test_verify_one_file! {
    #[test] disallow_open_on_trait_fn_decl verus_code! {
        pub trait SomeTrait {
            open spec fn foo(&self) -> bool;
        }
    } => Err(err) => assert_vir_error_msg(err, "trait function declarations cannot be open or closed, as they don't have a body")
}

test_verify_one_file! {
    #[test] require_open_closed_on_pub_crate verus_code! {
        mod m1 {
            use vstd::prelude::*;

            pub(crate) trait T {
                spec fn f() -> int;
            }
            pub(crate) struct S;
            impl T for S {
                spec fn f() -> int { 5 }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "open/closed is required for implementations of non-private traits")
}

test_verify_one_file! {
    #[test] trait_return_unit verus_code! {
        struct S;

        pub trait E<V> {
            fn e(&self) -> V;
        }

        impl E<u64> for S {
            fn e(&self) -> u64 {
                7
            }
        }

        impl E<()> for S {
            fn e(&self) {
                ()
            }
        }

        pub trait View<V> {
            spec fn view(&self) -> V;
        }

        impl View<int> for S {
            closed spec fn view(&self) -> int {
                7
            }
        }

        // See https://github.com/verus-lang/verus/issues/682
        impl View<()> for S {
            closed spec fn view(&self) {
                ()
            }
        }

        pub trait T {
            spec fn view(&self);
        }

        impl T for S {
            closed spec fn view(&self) {
                ()
            }
        }

        proof fn test<A: View<()>>(a: A) {
            a.view()
        }

        pub trait U {
            fn ff(&self) ensures 2 + 2 == 4;
        }

        impl U for S {
            fn ff(&self) {
                assert(2 + 2 == 4);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] termination_fail_issue784 verus_code! {
        enum Option<V> { Some(V), None }

        trait Tr {
            spec fn stuff() -> bool;
        }

        struct X { }

        // impl&%0
        impl Tr for X
        {
            spec fn stuff() -> bool {
                alpaca()                                // (1)
            }
        }

        spec fn alpaca() -> bool {
            // depends on the bound `X: Tr`
            // which depends on the above trait impl
            // which in turn depends on `alpaca`
            (P::<X> { t: Option::None }).orange()               // (2)
        }

        struct P<T> {
            t: Option<T>,
        }

        trait Zr {
            spec fn orange(&self) -> bool;
        }

        // impl&%1
        impl<T: Tr> Zr for P<T> {
            spec fn orange(&self) -> bool {
                !T::stuff()                             // (3)
            }
        }

        proof fn paradox() {
            assert(alpaca() == !alpaca());
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] termination_fail_issue784_bigger_impl_chain verus_code! {
        // It appears we have a cycle, (1) -> (2) -> (4) -> (3) -> (1)
        //
        // However, (4), being generic, doesn't actually have a dependency on (3);
        // likewise (3), being generic, doesn't depend on (1).
        // Instead, the cycle shows up because the call at (2) relies on the
        // trait implementation 'impl 0'. Thus we should end up
        // with an edge (2) -> (1) and thus resulting in the cycle:
        //
        // (1) -> (2) -> (1)
        //
        // Also note that the dependence of (2) upon 'impl 0' is indirect.
        // Specifically, it relies on `P<Q<X>>: Zr` obtained from 'impl 2'
        // This in turn relies on `Q<X>: Yr` obtained from 'impl 1'
        // And this in turn relies on `X: Tr` obtained from 'impl 0'.

        enum Option<V> { Some(V), None }

        trait Tr {
            spec fn stuff() -> bool;
        }

        struct X { }

        // impl 0
        impl Tr for X
        {
            spec fn stuff() -> bool {
                alpaca()                                   // (1)
            }
        }

        spec fn alpaca() -> bool {
            // depends on the bound `X: Tr`
            // which depends on the above trait impl
            // which in turn depends on `alpaca`
            (P::<Q<X>> { t: Option::None }).orange()               // (2)
        }

        struct P<T> {
            t: Option<T>,
        }

        struct Q<T> {
            t: Option<T>,
        }

        trait Yr {
            spec fn banana() -> bool;
        }

        trait Zr {
            spec fn orange(&self) -> bool;
        }

        // impl 1
        impl<T: Tr> Yr for Q<T> {
            spec fn banana() -> bool {
                !T::stuff()                               // (3)
            }
        }

        // impl 2
        impl<T: Yr> Zr for P<T> {
            spec fn orange(&self) -> bool {
                T::banana()                               // (4)
            }
        }

        proof fn paradox() {
            assert(alpaca() == !alpaca());
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] trait_bound_query verus_code! {
        // https://github.com/verus-lang/verus/issues/812
        trait T {}

        spec fn t<A>() -> bool { true }

        #[verifier::external_body]
        broadcast proof fn axiom_f<A: T>()
            ensures
                #[trigger] t::<A>(),
        {
        }

        struct S1;

        impl T for S1 {}
        fn test1() {
            assert(t::<S1>());
            let v1: u64 = 0;
            let v2: u64 = 0;
            assert(v1 * v2  >= 0) by(nonlinear_arith);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_bound_delayed verus_code! {
        trait T { proof fn q() ensures false; }

        spec fn f<A>(i: int) -> bool { false }

        #[verifier::external_body]
        broadcast proof fn p<A: T>(i: int)
            ensures f::<A>(i)
        {
        }

        struct S;
        impl T for S {
            proof fn q() {
                assert(f::<S>(7)); // FAILS
                // fails because we can't use the broadcast_forall with A = S
                // until after S: T has been established,
                // which can't happen until after S::q has been proven.
            }
        }

        proof fn test() {
            S::q();
            assert(false);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] trait_impl_bound_regression_833_0 verus_code! {
        mod m1 {
            pub trait MyView {
                type V;
            }
        }

        mod m2 {
            pub trait ViewOption {
                type X;
            }

            struct A<T>(T);

            impl<T: crate::m1::MyView> ViewOption for A<T>
            {
                type X = A<T::V>;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_assoc_type_bound verus_code! {
        trait A {
            type B;
        }

        exec fn foo<T: A>(b: T::B) {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_impl_bound_regression_724 verus_code! {
        use vstd::prelude::*;

        exec fn foo<T: View>(c : T::V)
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_impl_bound_regression_833_1 verus_code! {
        use vstd::prelude::*;

        pub trait ViewOption {
            type X;
        }

        impl<T:View> ViewOption for Option<T>
        {
            type X = Option<T::V>;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_impl_bound_regression_848 verus_code! {
        use vstd::prelude::*;

        pub trait TView { }

        pub trait B<T>
            where T: View, T::V: TView {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_self_bound verus_code! {
        trait A {
            spec fn a(&self) -> bool;

            proof fn foo(&self)
                ensures self.a();
        }

        trait B: A {
            spec fn b(&self) -> bool;

            proof fn bar(&self)
                ensures (self.a() == self.b()) ==> self.b();
        }

        impl A for bool {
            spec fn a(&self) -> bool { true }

            proof fn foo(&self) { }
        }

        impl B for bool {
            spec fn b(&self) -> bool { self.a() || false }

            proof fn bar(&self) { }
        }

        proof fn gen<T: B>(t: T)
            requires t.b() == t.a()
        {
            t.foo();
            assert(t.b());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_default1 verus_code! {
        trait T {
            spec fn f() -> int { 3 }
        }
        struct S1;
        struct S2;
        impl T for S1 { }
        impl T for S2 { spec fn f() -> int { 4 } }
        proof fn test() {
            assert(S1::f() == 3);
            assert(S2::f() == 4);
            assert(S2::f() == 3); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_default2 verus_code! {
        trait T {
            spec fn f() -> int;
            spec fn g() -> int { 3 }
        }
        struct S;
        impl T for S { spec fn f() -> int { Self::g() } }
        proof fn test() {
            assert(S::f() == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_default3 verus_code! {
        trait T {
            spec fn f() -> int;
            spec fn g() -> int { Self::f() }
        }
        struct S;
        impl T for S { spec fn f() -> int { 3 } }
        proof fn test() {
            assert(S::g() == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_default4 verus_code! {
        trait T {
            spec fn f() -> int;
            spec fn g() -> int { Self::f() }
        }
        struct S;
        impl T for S { spec fn f() -> int { Self::g() } }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] test_default5 verus_code! {
        trait T {
            spec fn f(i: int) -> int;
            spec fn g(i: int) -> int decreases i { Self::f(i) }
        }
        struct S;
        impl T for S { spec fn f(i: int) -> int decreases i { Self::g(i) } }
    } => Err(err) => assert_vir_error_msg(err, "trait default methods do not yet support recursion and decreases")
}

test_verify_one_file! {
    #[test] test_default6 verus_code! {
        trait T<A, B> {
            spec fn f(a: A, b: B) -> (A, B) { (a, b) }
            spec fn g(a: A, b: B) -> (A, B);
        }
        struct S<C>(C);
        impl<D> T<bool, D> for S<D> {
            spec fn g(x: bool, y: D) -> (bool, D) { Self::f(x, y) }
        }
        proof fn test() {
            assert(S::g(true, 5int) == (true, 5int));
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_default7 verus_code! {
        trait T {
            proof fn f() {
                assert(false); // FAILS
            }
        }
        struct S1;
        struct S2;
        impl T for S1 {}
        impl T for S2 {}
        proof fn test() {
            S1::f();
            S2::f();
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_default8 verus_code! {
        pub trait T {
            spec fn f() -> int;
            proof fn g() ensures Self::f() > 10;
            proof fn h() ensures Self::f() >= 10 {
                Self::g()
            }
        }
        mod m1 {
            pub struct S;
            impl crate::T for S {
                closed spec fn f() -> builtin::int { 15 }
                proof fn g() {}
            }
        }
        proof fn test() {
            crate::m1::S::h();
            assert(crate::m1::S::f() >= 10);
            assert(crate::m1::S::f() > 10); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_default9 verus_code! {
        struct S;
        trait T {
            proof fn f(tracked s: S) -> (tracked r: (S, S)) {
                (s, s)
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value: `s`")
}

test_verify_one_file! {
    #[test] test_default10 verus_code! {
        trait T {
            proof fn f();
            proof fn g() {}
        }

        proof fn h() {
            <bool as T>::g();
        }

        impl T for bool {
            proof fn f() { h(); }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_default11 verus_code! {
        trait T {
            proof fn f();
            proof fn g() {}
        }

        proof fn h() {
            <bool as T>::f();
        }

        impl T for bool {
            proof fn f() { h(); }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] test_default11b verus_code! {
        trait T {
            proof fn f() ensures false { Self::g() }
            proof fn g() ensures false;
        }

        proof fn h() ensures false {
            <bool as T>::f();
        }

        impl T for bool {
            proof fn g() { h(); }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] test_default12 verus_code! {
        trait T1 {
            proof fn f() ensures false;
        }

        // "trait T2: T1" is equivalent to "trait T2 where Self: T1".
        // We treat "Self: T1" just like we would treat "A: T1" for an explicit type parameter A.
        // This means that Self::f is unconditionally available to call inside g.
        // It also means that in h(), <bool as T2>::g() must provide "impl T1 for bool" for g.
        // This is what causes the cycle.
        // This approach has advantages and disadvantages:
        // - disadvantage: even if g() doesn't call Self::f(), it's still a (spurious) cycle
        // - advantage: "Self: T1" is available for instantiating other bounds; see test_default13
        trait T2: T1 {
            proof fn g() ensures false { Self::f(); }
        }

        impl T1 for bool {
            proof fn f() { h(); }
        }

        impl T2 for bool {
        }

        proof fn h()
             ensures false
        {
            <bool as T2>::g();
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_default13 verus_code! {
        trait T1: Sized {
            proof fn f();
        }

        proof fn m<A: T1>() {
            A::f();
        }

        trait T2: T1 {
            proof fn g() { m::<Self>(); }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_default14 verus_code! {
        trait T: Sized {
            proof fn g()
                ensures false
            {
                // For termination's sake, the "Self: T" bound is not available inside methods,
                // including default methods.
                // In ordinary impl methods, we catch uses of "Self: T" by seeing that impl_paths
                // recursively refer to the current impl whenever "Self: T" is used.
                // In default methods, on the other hand, there's no impl to use in impl_paths,
                // so impl_paths is empty in the following call (f::<Self>()).
                // Therefore, we catch the termination failure a different way:
                // whoever we're calling who needs "Self: T" as a bound (in this case, f)
                // must depend on T itself -- there must be a path from f to T in the call graph.
                // We then make sure that T depends on T's default methods,
                // so that there's a cycle.
                f::<Self>();
            }
        }

        proof fn f<A: T>()
            ensures false
        {
            A::g();
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_default15 verus_code! {
        trait T1: Sized {
            proof fn f1() ensures false;
        }
        trait T2: T1 {
            proof fn f2() ensures false {
                <Self as T1>::f1();
            }
        }
        impl T1 for bool {
            proof fn f1() {
                <Self as T2>::f2();
            }
        }
        impl T2 for bool {
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_default16 verus_code! {
        trait T1: Sized {
            proof fn f1() ensures false;
        }
        trait T2<A: T1> {
            proof fn f2() ensures false {
                A::f1();
            }
        }
        impl T1 for bool {
            proof fn f1() {
                <bool as T2<bool>>::f2();
            }
        }
        impl T2<bool> for bool {
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

test_verify_one_file! {
    #[test] test_default17 verus_code! {
        trait T {
            proof fn f() ensures false { Self::g(); }
            proof fn g() ensures false { Self::f(); }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] test_default18 verus_code! {
        struct S;
        trait T {
            fn f(s: S) -> S { s }
        }
        impl T for bool {
        }
        fn test(s: S) -> S {
            <bool as T>::f(s)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_default19 verus_code! {
        mod m1 {
            #[allow(unused_imports)]use builtin_macros::*;#[allow(unused_imports)]use builtin::*;
            pub trait T {
                open spec fn f() -> int { 3 }
            }
            impl T for bool {}
        }
        mod m2 {
            #[allow(unused_imports)]use builtin_macros::*;#[allow(unused_imports)]use builtin::*;
            use crate::m1::*;
            proof fn test() {
                assert(<bool as T>::f() == 3);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_default20 verus_code! {
        trait T<A> {
            spec fn f(a: &A) -> int { 7 }
        }

        struct S<X, Y, Z>(X, Y, Z);

        impl<X, Y, Z> T<X> for S<X, Y, Z> {
        }

        fn test() {
            assert(<S<u8, u16, bool> as T<u8>>::f(&3u8) == 7);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] associated_type_bound_lifetime_regression_955 verus_code! {
        use vstd::prelude::View;

        pub trait A {
            type Input: View;
            type Output: View;
        }

        pub trait B {
            type MyA: A;

            fn foo(input: <Self::MyA as A>::Input) -> <Self::MyA as A>::Output;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_encoding_soundness_experiments_1 verus_code! {
        mod m1 {
            use super::*;

            pub struct S { v: int }

            pub trait P: Sized {
                spec fn k(self) -> int;
            }

            impl P for S {
                closed spec fn k(self) -> int {
                    200
                }
            }

            impl P for &S {
                closed spec fn k(self) -> int {
                    300
                }
            }

            pub trait Q<TP: P> {
                open spec fn e(tp: TP) -> int {
                    tp.k()
                }
            }

            pub struct QQ { }

            impl Q<S> for QQ { }

            impl Q<&S> for QQ { }

            proof fn p_prop_0<TQ: Q<S>>(s: S)
                ensures #[trigger] TQ::e(s) == 200 {
                assert(s.k() == 200);
                assert(TQ::e(s) == 200); // FAILS
            }

            pub broadcast proof fn p_prop_1(s: S)
                ensures #[trigger] QQ::e(s) == 200 {}

            pub broadcast proof fn p_prop_2(s: S)
                ensures #[trigger] QQ::e(&s) == 300 {}
        }

        mod m2 {
            use super::*;
            use super::m1::*;

            proof fn test1(s: S)
            {
                broadcast use p_prop_1, p_prop_2;
                assert(QQ::e(s) == 200);
                assert(QQ::e(&s) == 300);
            }

            proof fn test2(s: S)
            {
                broadcast use p_prop_1, p_prop_2;
                assert(QQ::e(s) == 300); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}
