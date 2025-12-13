#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_dyn verus_code! {
        use vstd::prelude::*;
        trait T {
            spec fn b(&self) -> u8 { 5 }
            fn f(&self) -> (r: u8) ensures r <= self.b();
        }
        impl T for u8 {
            spec fn b(&self) -> u8 { *self }
            fn f(&self) -> (r: u8) { *self / 2 }
        }
        impl T for u16 {
            spec fn b(&self) -> u8 { (*self / 256) as u8 }
            fn f(&self) -> (r: u8) { (*self / 512) as u8 }
        }
        impl T for u32 {
            fn f(&self) -> (r: u8) { 4 }
        }
        fn test_coerce() {
            let u: u8 = 7;
            let d: &dyn T = &u; // ToDyn coercion
            let r = d.f();
            assert(d.b() == 7);
            assert(r <= 10);

            let x: u32 = 9;
            let d: Box<dyn T> = Box::new(x); // ToDyn coercion
            let r = d.f();
            assert(d.b() == 5);
            assert(r <= 10);

            let y: u16 = 8;
            let d: Box<dyn T> = Box::new(y); // ToDyn coercion
            let r = d.f();
            assert(d.b() == 5); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_dyn_ext verus_code! {
        #[verifier::external]
        trait T {
            fn f(&self) -> u8;
        }

        #[verifier::external_trait_specification]
        #[verifier::external_trait_extension(TSpec via TSpecImpl)]
        trait ExT {
            type ExternalTraitSpecificationFor: T;

            spec fn b(&self) -> u8;
            fn f(&self) -> (r: u8) ensures r <= self.b();
        }

        impl T for u8 {
            fn f(&self) -> (r: u8) { *self / 2 }
        }

        impl TSpecImpl for u8 {
            spec fn b(&self) -> u8 { *self }
        }

        fn test() {
            let u: u8 = 7;
            let d: &dyn T = &u; // ToDyn coercion
            assert(d.b() == 7);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_dyn_generic verus_code! {
        use vstd::prelude::*;

        trait T0 {
        }

        trait T4 {
            fn f(&self);
        }

        fn g0<A: T0 + ?Sized>() {
        }

        fn g1<A: T0 + ?Sized>(a: &A) {
        }

        fn test(x0: &dyn T0, x4: &dyn T4) {
            g0::<dyn T0>();
            g1(x0);
            x4.f();
        }

        fn test2<A0: T0, A4: T4>(a0: &A0, a4: &A4, b4: A4) {
            let x: &dyn T4 = &b4;
            let x: Box<dyn T4> = Box::new(b4);
            test(a0, a4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] dyn_proof_must_be_inhabited1 verus_code! {
        use vstd::prelude::*;
        trait T {
            proof fn bogus(&self)
                ensures
                    false;
        }
        proof fn test() {
            let d: &dyn T = arbitrary();
            d.bogus();
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "not Verus dyn-compatible")
}

test_verify_one_file! {
    #[test] dyn_proof_must_be_inhabited1b verus_code! {
        trait T {
            spec fn f(&self) -> nat;
            proof fn about_f(&self) ensures self.f() < 10;
        }

        broadcast proof fn promote_f<A: T>(a: &A)
            ensures
                #[trigger] a.f() < 10,
        {
            a.about_f();
        }

        proof fn test(s: &dyn T) {
            assert(s.f() < 10);
        }
    } => Err(err) => assert_vir_error_msg(err, "not Verus dyn-compatible")
}

test_verify_one_file! {
    #[test] dyn_proof_must_be_inhabited2 verus_code! {
        use vstd::prelude::*;
        trait T {
            proof fn bogus(tracked &self)
                ensures
                    false;
        }
        proof fn test() {
            let d: &dyn T = arbitrary();
            d.bogus();
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] dyn_proof_must_be_inhabited2b verus_code! {
        trait T {
            spec fn f(&self) -> nat;
            proof fn about_f(tracked &self) ensures self.f() < 10;
        }

        broadcast proof fn promote_f<A: T>(a: &A)
            ensures
                #[trigger] a.f() < 10,
        {
            a.about_f();
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] dyn_proof_must_be_inhabited3 verus_code! {
        use vstd::prelude::*;
        trait T {
            proof fn bogus(tracked &self)
                ensures
                    false;
        }
        proof fn test() {
            let tracked d: &dyn T = arbitrary();
            d.bogus();
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] dyn_proof_must_be_inhabited3b verus_code! {
        trait T {
            spec fn f(&self) -> nat;
            proof fn about_f(tracked &self) ensures self.f() < 10;
        }

        broadcast proof fn promote_f<A: T>(tracked a: &A)
            ensures
                #[trigger] a.f() < 10,
        {
            a.about_f();
        }
    } => Err(err) => assert_vir_error_msg(err, "broadcast function must have spec parameters")
}

test_verify_one_file! {
    #[test] dyn_proof_must_be_inhabited4 verus_code! {
        use vstd::prelude::*;
        trait T {
            spec fn bogus(&self)
                ensures
                    false;
        }
        proof fn test() {
            let d: &dyn T = arbitrary();
            d.bogus();
            assert(false);
        }
        // Note: when we allow spec ensures, this should become a "not Verus dyn-compatible" error
    } => Err(err) => assert_vir_error_msg(err, "spec functions cannot have requires/ensures")
}

test_verify_one_file! {
    #[test] dyn_proof_must_be_inhabited_sized verus_code! {
        use vstd::prelude::*;
        enum Opt<A: ?Sized> {
            None,
            Some(Box<A>),
        }

        spec fn f<A: ?Sized>(a: &Opt<A>) -> bool { true }

        trait False {
            proof fn ensure_false() where Self: Sized ensures false;
        }

        broadcast proof fn promote_false<A: False>(a: Opt<A>)
            ensures
                #[trigger] f::<A>(&a),
                false,
        {
            A::ensure_false();
        }

        proof fn incorrect<A: False + ?Sized>()
            ensures
                false,
        {
            broadcast use promote_false;
            assert(f::<A>(&Opt::None));
            assert(false); // FAILS
        }

        proof fn bad()
            ensures
                false,
        {
            incorrect::<dyn False>();
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] dyn_rust_blanket_unsoundness verus_code! {
        // https://github.com/rust-lang/rust/issues/57893
        trait T {}
        impl<A: ?Sized> T for A {}
        fn test(x: &dyn T) {}
    } => Err(err) => assert_vir_error_msg(err, "it has an unsized blanket impl")
}

test_verify_one_file! {
    #[test] dyn_rust_blanket_unsoundness2 verus_code! {
        // https://github.com/rust-lang/rust/issues/57893
        trait TraitA { type Item: ?Sized; }
        trait TraitB<T> { }
        impl<X: TraitA> TraitB<X> for X::Item { }
        impl TraitA for () { type Item = dyn TraitB<()>; }
    } => Err(err) => assert_vir_error_msg(err, "conflicting implementations of trait")
}

test_verify_one_file! {
    #[test] dyn_in_struct verus_code! {
        use vstd::prelude::*;
        trait T { fn f(&self) {} }
        impl T for u8 {}
        struct S(Box<dyn T>);
        fn test() {
            let u: u8 = 3;
            let s = S(Box::new(u));
            s.0.f();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] dyn_cycle1 verus_code! {
        trait T {
            spec fn f(&self, d: &dyn T) -> int;
        }
        impl T for u8 {
            spec fn f(&self, d: &dyn T) -> int {
                d.f(d) + 1
            }
        }
        proof fn test() {
            let u: u8 = 3;
            let d: &dyn T = &u;
            assert(d.f(d) == d.f(d) + 1);
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference")
}

test_verify_one_file! {
    #[test] dyn_cycle2 verus_code! {
        trait T {
            proof fn f(tracked &self, tracked d: &dyn T)
                ensures
                    false;
        }
        impl T for u8 {
            proof fn f(tracked &self, tracked d: &dyn T) {
                d.f(d)
            }
        }
        proof fn test() {
            let tracked u: u8 = 3;
            let tracked d: &dyn T = &u;
            d.f(d);
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference")
}

test_verify_one_file! {
    #[test] dyn_cycle3 verus_code! {
        trait T {
            spec fn f(&self, d: &S) -> int;
        }
        struct S(Box<dyn T>);
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference")
}

test_verify_one_file! {
    #[test] dyn_cycle4 verus_code! {
        use vstd::prelude::*;
        trait T {
            spec fn f(&self) -> S;
        }
        struct S(Box<dyn T>);

        proof fn p(s: &S)
            ensures
                false,
            decreases s
        {
            p(&(s.0).f())
        }

        proof fn test()
            ensures
                false,
        {
            p(&arbitrary());
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference")
}

test_verify_one_file! {
    #[test] dyn_cycle5 verus_code! {
        use vstd::prelude::*;
        trait T<A> {
            spec fn f(&self) -> A;
        }
        struct S(Box<dyn T<S>>);

        proof fn p(s: &S)
            ensures
                false,
            decreases s
        {
            p(&(s.0).f())
        }

        proof fn test()
            ensures
                false,
        {
            p(&arbitrary());
        }
    } => Err(err) => assert_vir_error_msg(err, "non-positive position")
}

test_verify_one_file! {
    #[test] dyn_unsupported1 verus_code! {
        trait T {}
        fn test(d: &(dyn T + Send)) {
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: dyn with more that one trait")
}

test_verify_one_file! {
    #[test] dyn_unsupported2 verus_code! {
        trait T {}
        fn test(d: &dyn Fn() -> ()) {
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: dyn with more that one trait")
}
