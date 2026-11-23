#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Tests for `#[verus_spec(with ..)]`: extra ghost/tracked inputs and outputs.
//
// A call site written as `proof_with!{..} f(..)` is redirected to the verified
// counterpart of `f` before type checking, so that rustc type checks, borrow
// checks and lifetime checks the extra arguments.
//
// Some positive cases sharing a declaration are grouped into one test, one case
// per module so that names do not clash.

test_verify_one_file! {
    #[test] test_generic_type code! {
        use vstd::prelude::*;

        #[verus_spec(with Ghost(g): Ghost<T>)]
        fn f<T: Copy>(x: T) -> T { x }

        #[verus_spec(with Ghost(g): Ghost<T> -> out: Ghost<T>)]
        fn caller<T: Copy>(x: T) -> T {
            proof_with! { Ghost(g) }
            let value = f(x);
            proof_with! { |= Ghost(g) }
            value
        }
    } => Ok(())
}

test_verify_one_file! {
    // The verified and unverified copies of a call with different arguments are rejected.
    #[test] test_wrong_proof_with_callee code! {
        use vstd::prelude::*;

        #[verus_spec(with Ghost(g): Ghost<u8>)]
        fn f(x: u8) -> u8 { x }

        // Only the verification run redirects the hand-written call.
        #[cfg(verus_keep_ghost_body)]
        #[verus_verify]
        fn caller(x: u8, y: u8) {
            let _ = vstd::prelude::proof_with_callee(f(y, vstd::prelude::ghost_exec(x)), f(x));
        }
    } => Err(e) => assert_vir_error_msg(e, "the two copies of the call must be the same code")
}

test_verify_one_file! {
    #[test] test_hir_conformance_hygienic_copies_rejected code! {
        use vstd::prelude::*;

        #[verus_spec(with Ghost(g): Ghost<u8>)]
        fn f(x: u8) -> u8 { x }

        // Both copies print as `f({ let x = 2; x })`, but `$x` is the caller's `x`.
        macro_rules! forge {
            ($x:ident) => {
                vstd::prelude::proof_with_callee(
                    f({ let x = 2; x }, vstd::prelude::ghost_exec(1u8)),
                    f({ let x = 2; $x }),
                )
            };
        }

        // Only the verification run redirects the hand-written call.
        #[cfg(verus_keep_ghost_body)]
        #[verus_verify]
        fn caller(x: u8) {
            let _ = forge!(x);
        }
    } => Err(e) => assert_vir_error_msg(e, "the two copies of the call must be the same code")
}

test_verify_one_file! {
    #[test] test_hir_conformance_nested_use_rejected code! {
        use vstd::prelude::*;

        #[verus_spec(with Ghost(g): Ghost<u8>)]
        fn f(x: u8) -> u8 { x }

        mod a { pub trait Tr { fn foo(&self) -> u8 { 1 } } impl Tr for u8 {} }
        mod b { pub trait Tr { fn foo(&self) -> u8 { 2 } } impl Tr for u8 {} }

        // Both copies print as `f({ x.foo() })`, but `foo` resolves to different traits.
        // Only the verification run redirects the hand-written call.
        #[cfg(verus_keep_ghost_body)]
        #[verus_verify]
        fn caller(x: u8) {
            let _ = vstd::prelude::proof_with_callee(
                f({ use b::Tr as _; x.foo() }, vstd::prelude::ghost_exec(1u8)),
                f({ use a::Tr as _; x.foo() }),
            );
        }
    } => Err(e) => assert_vir_error_msg(e, "the two copies of the call must be the same code")
}

test_verify_one_file! {
    #[test] test_hir_conformance_compiled_copy_not_a_call_rejected code! {
        use vstd::prelude::*;

        #[verus_spec(with Ghost(g): Ghost<u8>)]
        fn f(x: u8) -> u8 { x }

        // Only the verification run redirects the hand-written call.
        #[cfg(verus_keep_ghost_body)]
        #[verus_verify]
        fn caller(x: u8) {
            let _ = vstd::prelude::proof_with_callee(f(x, vstd::prelude::ghost_exec(x)), { f(x) });
        }
    } => Err(e) => assert_vir_error_msg(e, "ill-formed `proof_with!` call")
}

test_verify_one_file! {
    #[test] test_with_shadow_through_deref_rejected code! {
        use vstd::prelude::*;

        #[verus_verify]
        struct Inner;
        #[verus_verify]
        struct Outer { inner: Inner }

        #[verus_verify]
        impl Inner {
            #[verus_spec(r => with Ghost(g): Ghost<int> ensures r == 1)]
            fn foo(&self) -> u32 { 1 }
        }

        impl core::ops::Deref for Outer {
            type Target = Inner;
            fn deref(&self) -> &Inner { &self.inner }
        }

        #[verus_verify]
        impl Outer {
            fn foo(&self) -> u32 { 2 }
        }

        #[verus_spec(r => ensures r == 1)]
        fn caller(x: &Outer) -> u32 {
            proof_with! { Ghost(0) }
            x.foo()
        }
    } => Err(e) => assert_vir_error_msg(e, "which is not declared with `#[verus_spec(with ..)]`")
}

test_verify_one_file! {
    #[test] test_with_ghost_only_generic_rejected code! {
        use vstd::prelude::*;

        #[verus_spec(with Ghost(g): Ghost<B>)]
        fn f<A, B>(x: A) {}
    } => Err(e) => assert_vir_error_msg(e, "generic parameter `B` is used only by ghost/tracked")
}

test_verify_one_file_with_options! {
    #[test] test_with_conformance_explicit_types ["--compile"] => code! {
        use vstd::prelude::*;

        #[verus_spec(r =>
            with Ghost(g): Ghost<T>
            ensures r == x,
        )]
        fn f<T: Copy>(x: T) -> T { x }

        #[verus_spec(r => ensures r == 1)]
        fn caller(g: Ghost<u8>) -> u8 {
            proof_with! { g }
            f::<u8>(1)
        }
    } => Ok(())
}

// A function `f` that requires its `Tracked` input to equal its argument.

const FN_WITH_TRACKED_EQ: &str = code_str! {
    use vstd::prelude::*;

    #[verus_verify]
    #[verus_spec(r =>
        with Tracked(t): Tracked<u8>
        requires x == t,
        ensures r == x,
    )]
    fn f(x: u8) -> u8 {
        x
    }
};

test_verify_one_file! {
    // A free function with extra Tracked and Ghost inputs.
    #[test] test_attribute_form_free_fn code!{
        use vstd::prelude::*;

        #[verus_spec(
            with Tracked(b): Tracked<u64>, Ghost(c): Ghost<u32>
            requires a == 0, b == 1, c == 2,
        )]
        fn free_fn(a: u64) {}

        #[verus_spec]
        fn call_free() {
            proof_with!{Tracked(1u64), Ghost(2u32)}
            free_fn(0);
        }
    } => Ok(())
}

test_verify_one_file! {
    // An inherent method with extra Tracked and Ghost inputs.
    #[test] test_attribute_form_inherent_method code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct A {
            a: u64,
        }

        impl A {
            #[verus_spec(
                with Tracked(b): Tracked<u64>, Ghost(c): Ghost<u32>
                requires self.a == 0, b == 1, c == 2,
            )]
            fn m(&self) {}
        }

        #[verus_spec]
        fn call_method() {
            let a = A { a: 0 };
            proof_with!{Tracked(1u64), Ghost(2u32)}
            a.m();
        }
    } => Ok(())
}

test_verify_one_file! {
    // The extra Tracked reference may outlive the return with a `'b: 'a` bound.
    #[test] test_attribute_form_outlives_bound code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(c): Tracked<&'a u64>)]
        fn lt<'a>(a: &'a u64, b: u64) -> &'a u64 {
            a
        }

        #[verus_spec]
        fn lt_caller<'a, 'b: 'a>(a: &'a u64, b: u64, c: Tracked<&'b u64>) -> &'a u64 {
            proof_with!{c}
            lt(a, b)
        }
    } => Ok(())
}

test_verify_one_file! {
    // The extra input's type may be a generic parameter.
    #[test] test_attribute_form_generic_input code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(b): Tracked<T>)]
        fn gen<T>(a: T) {}

        #[verus_spec]
        fn call_gen(t: Tracked<u64>) {
            proof_with!{t}
            gen(0u64);
        }
    } => Ok(())
}

test_verify_one_file! {
    // The reserved counterpart name is ordinary when no `with` clause generated it.
    #[test] test_counterpart_name_ordinary code!{
        use vstd::prelude::*;

        #[verus_spec(ret =>
            ensures ret == 7,
        )]
        fn _VERUS_VERIFIED_f() -> u64 {
            7
        }

        #[verus_spec]
        fn caller() {
            let x = _VERUS_VERIFIED_f();
            proof!{ assert(x == 7); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // A call inside a closure body (a separate body of the same owner) is redirected too.
    #[test] test_with_call_inside_closure
        FN_WITH_TRACKED_EQ.to_string() + code_str!{
        #[verus_verify]
        fn call_in_closure() {
            let c = || -> u8 {
                proof_with!{Tracked(3u8)}
                let y = f(3);
                y
            };
            let _v = c();
        }
    } => Ok(())
}

test_verify_one_file! {
    // A wrong extra argument fails the precondition; omitting `proof_with!` hits `requires(false)`.
    #[test] test_proof_with_failed_or_missing code!{
        use vstd::prelude::*;

        #[verus_spec(
            with Tracked(b): Tracked<u64>
            requires b == 1,
        )]
        fn test(a: u64) {
        }

        #[verus_spec]
        fn call_wrong() {
            proof_with!{Tracked(2u64)}
            test(0); // FAILS
        }

        #[verus_spec]
        fn call_missing() {
            test(0); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] test_proof_with_on_non_with_fn code!{
        use vstd::prelude::*;

        fn test(a: u64) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Tracked(1u64)}
            test(0);
        }
    } => Err(e) => {
        let err = e.errors.iter()
            .find(|x| x.message.contains("`test` does not accept extra ghost/tracked arguments"))
            .expect("missing proof_with diagnostic");
        assert!(err.spans.iter().any(|s| s.is_primary && s.text.iter().any(|t| t.text.contains("test(0)"))));
        assert!(err.spans.iter().any(|s| s.is_primary && s.text.iter().any(|t| t.text.contains("fn test(a: u64)"))));
    }
}

// ---- type, mode and lifetime checking is done by rustc ----

// An external function whose `assume_specification` adds a `Tracked` input equal to `x`.

const EXTERNAL_FN_NEGATE_BOOL: &str = code_str! {
    use vstd::prelude::*;

    #[verifier::external]
    fn negate_bool(b: bool, x: u8) -> bool {
        !b
    }

    #[verifier::external_fn_specification]
    #[verus_spec(ret =>
        with Tracked(extra): Tracked<u8>
        requires x == extra,
        ensures ret == !b,
    )]
    fn negate_bool_spec(b: bool, x: u8) -> bool {
        negate_bool(b, x)
    }
};

test_verify_one_file! {
    // a wrong extra type is rejected in every form.
    #[test] test_mismatched_extra_type_rejected
        code_str!{
            use vstd::prelude::*;

            // a wrong type for a `Tracked` input
            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn f1(a: u64) {}

            #[verus_spec]
            fn c1() {
                proof_with!{Tracked(1u32)}
                f1(0);
            }

            // a `Ghost` value where a `Tracked` input is declared
            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn f2(a: u64) {}

            #[verus_spec]
            fn c2() {
                proof_with!{Ghost(1u64)}
                f2(0);
            }

            // a wrong type for a generic `Tracked` input
            #[verus_spec(with Tracked(b): Tracked<T>)]
            fn f3<T>(a: T) {}

            #[verus_spec]
            fn c3() {
                proof_with!{Tracked(1u32)}
                f3(0u64);
            }
        }.to_string()
        // a wrong extra type on a call redirected to an `assume_specification`
        + EXTERNAL_FN_NEGATE_BOOL
        + code_str!{
            #[verus_spec]
            fn call_external() {
                proof_with!{Tracked(1u32)}
                let ret = negate_bool(true, 1);
            }
        }
    => Err(e) => {
        // one error per case, so no case can stop being rejected unnoticed
        assert_eq!(e.errors.len(), 4);
        assert_rust_error_msgs(e, &["mismatched types"; 4]);
    }
}

test_verify_one_file! {
    #[test] test_proof_with_wrong_arity code!{
        use vstd::prelude::*;

        #[verus_spec(with Tracked(b): Tracked<u64>, Tracked(c): Tracked<u64>)]
        fn test(a: u64) {
        }

        #[verus_spec]
        fn call_test() {
            proof_with!{Tracked(1u64)}
            test(0);
        }
    } => Err(e) => assert_rust_error_msg_all(e, "this function takes 3 arguments but 2 arguments were supplied")
}

test_verify_one_file! {
    // The extra `Tracked`/`Ghost` input keeps its lifetime obligations.
    #[test] test_proof_with_lifetime_mismatch
        // through a `Tracked` input
        code_str!{
            mod tracked {
                use vstd::prelude::*;

                #[verus_spec(with Tracked(c): Tracked<&'a u64>)]
                fn test<'a>(a: &'a u64, b: u64) -> &'a u64 {
                    a
                }

                #[verus_spec]
                fn test2<'a, 'b>(a: &'a u64, b: u64, c: Tracked<&'b u64>) -> &'a u64 {
                    proof_with!{c}
                    test(a, b)
                }
            }
        }.to_string()
        // through a `Ghost` input
        + code_str!{
            mod ghost {
                use vstd::prelude::*;

                #[verus_spec(with Ghost(g): Ghost<&'a u64>)]
                fn test<'a>(a: &'a u64) -> &'a u64 {
                    a
                }

                #[verus_spec]
                fn test2<'a, 'b>(a: &'a u64, c: Ghost<&'b u64>) -> &'a u64 {
                    proof_with!{c}
                    test(a)
                }
            }
        }
    => Err(e) => assert_rust_error_msgs(
        e,
        &["lifetime may not live long enough", "lifetime may not live long enough"],
    )
}

test_verify_one_file! {
    #[test] test_proof_with_ownership code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct A;

        #[verus_spec(with Tracked(b): Tracked<&'a mut A>, Ghost(c): Ghost<u32>)]
        fn test<'a>(a: &'a mut A) {
        }

        #[verus_spec]
        fn call_test(mut a: A) {
            proof_with!{Tracked(&mut a), Ghost(2u32)}
            test(&mut a);
        }
    } => Err(e) => assert_rust_error_msg_skip_spec_msgs(e, "cannot borrow `a` as mutable more than once at a time")
}

// ---- extra ghost/tracked outputs ----

test_verify_one_file! {
    #[test] test_one_extra_output code! {
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with -> z: Ghost<u32>
            ensures ret == 1u64, z@ == 2u32,
        )]
        fn one_output() -> u64 {
            proof_with!{|= Ghost(2u32)}
            1
        }

        #[verus_spec]
        fn test() {
            proof_with!{=> Ghost(z)}
            let r = one_output();
            proof!{ assert(r == 1); assert(z == 2); }
            proof_with!{=> _}
            let _ = one_output();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_multiple_extra_outputs code! {
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with -> y: Ghost<u8>, z: Ghost<u32>
            ensures ret == 1u64, y@ == 3u8, z@ == 2u32,
        )]
        fn many_outputs() -> u64 {
            proof_with!{|= (Ghost(3u8), Ghost(2u32))}
            1
        }

        #[verus_spec]
        fn test() {
            proof_with!{=> (Ghost(y), Ghost(z))}
            let r = many_outputs();
            proof!{ assert(r == 1); assert(y == 3); assert(z == 2); }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_extra_inputs_and_output code! {
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with Tracked(y): Tracked<&mut int>, Ghost(w): Ghost<u32> -> z: Ghost<u32>
            requires x < 100, *old(y) < 100,
            ensures *final(y) == x, ret == x, z@ == x,
        )]
        fn inout(x: u32) -> u32 {
            proof!{ *y = x as int; }
            proof_with!{|= Ghost(x)}
            x
        }

        #[verus_spec]
        fn test() {
            proof_decl!{ let tracked mut y = 0int; }
            proof_with!{Tracked(&mut y), Ghost(0u32) => Ghost(z)}
            let r = inout(1);
            proof!{ assert(r == 1); assert(y == 1); assert(z == 1); }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ret_with_ensures_fail code!{
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with -> z: Ghost<u32>
            ensures z@ == 2u32, // FAILS
        )]
        fn test() -> u64 {
            proof_with!{|= Ghost(3u32)}
            1
        }
    } => Err(e) => assert_one_fails(e)
}

// ---- calls through a path or an alias resolve to the same verified function ----

// A function with an extra `Tracked` input in a submodule, and an alias to it.

const MOD_FN_WITH_TRACKED: &str = code_str! {
    use vstd::prelude::*;

    mod m {
        use vstd::prelude::*;
        #[verus_spec(
            with Tracked(b): Tracked<u64>
            requires b == 1,
        )]
        pub fn test(a: u64) {
        }
    }

    use m::test as aliased;
};

test_verify_one_file! {
    #[test] test_proof_with_qualified_path
        MOD_FN_WITH_TRACKED.to_string() + code_str!{
        #[verus_spec]
        fn call_qualified() {
            proof_with!{Tracked(1u64)}
            m::test(0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_proof_with_module_item_alias
        MOD_FN_WITH_TRACKED.to_string() + code_str!{
        #[verus_spec]
        fn call_aliased() {
            proof_with!{Tracked(1u64)}
            aliased(0);
        }
    } => Ok(())
}

test_verify_one_file! {
    // Without `proof_with!`, both the qualified path and the alias reach the stub.
    #[test] test_proof_with_qualified_path_missing
        MOD_FN_WITH_TRACKED.to_string() + code_str!{
        #[verus_spec]
        fn call_qualified() {
            m::test(0); // FAILS
        }

        #[verus_spec]
        fn call_aliased() {
            aliased(0); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    // Without `proof_with!`, a call through a crate alias reaches the `requires(false)` stub.
    #[test] test_proof_with_through_crate_alias_missing code!{
        use vstd::prelude::*;

        #[verus_spec(r =>
            with Ghost(g): Ghost<int>
            requires g == 1, a < 1000,
            ensures r == a + 1,
        )]
        fn with_extra(a: u64) -> u64 {
            a + 1
        }

        use crate::with_extra as with_alias;

        #[verus_spec]
        fn test() {
            let r = with_alias(6); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    // A user-defined `proof_with_callee` is not the builtin marker.
    #[test] test_user_defined_proof_with_is_not_a_marker code!{
        use vstd::prelude::*;

        mod verus_builtin {
            use vstd::prelude::*;
            #[verus_verify]
            pub fn proof_with_callee<A, B>(_a: A, b: B) -> B {
                b
            }
        }

        #[verifier::external_body]
        fn opaque(a: u64) -> u64 {
            a
        }

        #[verus_spec]
        fn call_user_proof_with() -> u64 {
            verus_builtin::proof_with_callee(1u64, opaque(2))
        }
    } => Ok(())
}

// --- `with` on an external function specification (`assume_specification`) ---
//
// The `assume_specification` keeps the exact signature of the external function
// and gains `requires(false)`, so a plain call fails. The verified counterpart
// carries the extra ghost/tracked parameters, and `proof_with!` redirects the
// call to it.

test_verify_one_file! {
    #[test] test_external_fn_with_extra_output code! {
        use vstd::prelude::*;

        #[verifier::external]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier::external_fn_specification]
        #[verus_spec(ret =>
            with Tracked(extra): Tracked<u8> -> z: Ghost<u8>
            requires x == extra,
            ensures ret == !b, z@ == extra,
        )]
        fn negate_bool_spec(b: bool, x: u8) -> bool {
            negate_bool(b, x)
        }

        #[verus_spec]
        fn call_external() {
            proof_with!{Tracked(1u8) => Ghost(z)}
            let ret = negate_bool(true, 1);
            proof!{ assert(!ret); assert(z == 1u8); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Without `proof_with!` the call hits `requires(false)`; a wrong extra argument fails `requires`.
    #[test] test_external_fn_missing_or_failed_requires
        EXTERNAL_FN_NEGATE_BOOL.to_string() + code_str!{
        #[verus_spec]
        fn call_missing() {
            let ret = negate_bool(true, 1); // FAILS
        }

        #[verus_spec]
        fn call_wrong_arg() {
            proof_with!{Tracked(99u8)}
            let ret = negate_bool(true, 1); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    // The counterpart of a trait-method `assume_specification` is a free fn lacking `Self`, so trait calls are rejected.
    #[test] test_external_trait_method_spec_rejected code!{
        use vstd::prelude::*;

        #[verifier::external]
        pub trait Tr { fn m(&self, x: u8) -> u8; }
        #[verifier::external]
        pub struct S;
        #[verifier::external]
        impl Tr for S {
            fn m(&self, x: u8) -> u8 { x }
        }

        verus! {
        #[verifier::external_type_specification]
        pub struct ExS(S);
        }

        #[verifier::external_fn_specification]
        #[verus_spec(ret =>
            with Tracked(extra): Tracked<u8>
            requires x == extra,
            ensures ret == x,
        )]
        pub fn tr_m_spec(s: &S, x: u8) -> u8 {
            <S as Tr>::m(s, x)
        }

        #[verus_spec]
        fn qualified() {
            proof_with!{Tracked(1u8)}
            let r = <S as Tr>::m(&S, 1);
        }

        #[verus_spec]
        fn trait_path() {
            proof_with!{Tracked(1u8)}
            let r = Tr::m(&S, 1);
        }
    } => Err(err) => assert_vir_error_msgs(err, &[
        "this call to `Tr::m` has different type arguments than in the verified program",
        "this call to `Tr::m` has different type arguments than in the verified program",
    ])
}

// --- `with` on a trait method ---
//
// A method that declares extra ghost/tracked parameters cannot be its own
// verified counterpart, so the counterparts are collected into a companion
// trait, `_VERUS_VERIFIED_TRAIT_X`, declared next to `X` as a subtrait of it and
// blanket-implemented for every implementor of `X`. The method of `X` keeps
// `requires(false)`; an overriding implementation puts its body in a second
// companion, `_VERUS_VERIFIED_IMPL_TRAIT_X`. Because the blanket impl covers
// every type, no caller needs an extra bound. None of this is spelled out in the
// source.

// A trait whose method `f` declares a `Ghost` input, and a type `S` to implement it for.

const TRAIT_WITH_GHOST_INPUT: &str = code_str! {
    use vstd::prelude::*;

    #[verus_verify]
    trait X {
        #[verus_spec(ret =>
            with Ghost(g): Ghost<u64>
            requires g@ < 100,
            ensures ret == a,
        )]
        fn f(&self, a: u64) -> u64;
    }

    #[verus_verify]
    struct S;
};

// A trait whose method `f` has a `Ghost` input and output, implemented for `S`.

const TRAIT_WITH_GHOST_OUTPUT: &str = code_str! {
    use vstd::prelude::*;

    #[verus_verify]
    trait X {
        #[verus_spec(ret =>
            with Ghost(g): Ghost<u64> -> g2: Ghost<u64>
            ensures ret == a, g2 == g,
        )]
        fn f(&self, a: u64) -> u64;
    }

    #[verus_verify]
    struct S;

    #[verus_verify]
    impl X for S {
        #[verus_spec(with Ghost(g): Ghost<u64> -> g2: Ghost<u64>)]
        fn f(&self, a: u64) -> u64 {
            proof_with!{|= Ghost(g)}
            a
        }
    }
};

test_verify_one_file! {
    #[test] test_local_trait_supertrait_call
        TRAIT_WITH_GHOST_OUTPUT.to_string() + code_str!{
        #[verus_verify]
        trait Y: X {}

        #[verus_verify]
        impl Y for S {}

        #[verus_spec]
        fn call_via_subtrait<A: Y>(x: &A) {
            proof_with!{Ghost(3u64) => Ghost(g2)}
            let r = x.f(7);
            proof!{ assert(g2 == 3); }
        }

        #[verus_verify]
        fn test() {
            call_via_subtrait(&S);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_local_trait_inherent_impl_bound
        TRAIT_WITH_GHOST_OUTPUT.to_string() + code_str!{
        #[verus_verify]
        struct Wrapper<A>(A);

        #[verus_verify]
        impl<A: X> Wrapper<A> {
            #[verus_spec]
            fn call(&self) {
                proof_with!{Ghost(3u64) => Ghost(g2)}
                let r = self.0.f(7);
                proof!{ assert(g2 == 3); }
            }
        }

        #[verus_verify]
        fn test() {
            Wrapper(S).call();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_local_trait_unrelated_bound
        TRAIT_WITH_GHOST_OUTPUT.to_string() + code_str!{
        #[verus_verify]
        trait Z {
            #[verus_spec(ret => ensures ret == a)]
            fn g(&self, a: u64) -> u64;
        }

        #[verus_spec(r => ensures r == 7)]
        fn call_other<A: Z, B: X>(z: &A, _x: &B) -> u64 {
            z.g(7)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_local_trait_forward_output
        TRAIT_WITH_GHOST_OUTPUT.to_string() + code_str!{
        #[verus_verify]
        struct Fwd<A>(A);

        #[verus_verify]
        impl<A: X> X for Fwd<A> {
            #[verus_spec(with Ghost(g): Ghost<u64> -> g2: Ghost<u64>)]
            fn f(&self, a: u64) -> u64 {
                proof_with!{Ghost(g) => Ghost(inner)}
                let r = self.0.f(a);
                proof_with!{|= Ghost(inner)}
                r
            }
        }

        #[verus_verify]
        fn test() {
            proof_with!{Ghost(3u64) => Ghost(g2)}
            let r = Fwd(S).f(7);
            proof!{ assert(r == 7); assert(g2 == 3); }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_local_trait_generic_arguments code! {
        use vstd::prelude::*;

        #[verus_verify]
        struct S;

        #[verus_verify]
        trait Tr<A> {
            #[verus_spec(with Ghost(g): Ghost<u64>)]
            fn m(&self, a: A);
        }

        #[verus_verify]
        impl Tr<u64> for S {
            #[verus_spec(with Ghost(g): Ghost<u64>)]
            fn m(&self, _a: u64) {}
        }

        #[verus_spec]
        fn call_generic_args<A: Tr<u64>>(x: &A) {
            proof_with!{Ghost(1u64)}
            x.m(1u64);
        }

        #[verus_verify]
        fn test() {
            call_generic_args(&S);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_local_trait_dyn_call
        TRAIT_WITH_GHOST_OUTPUT.to_string() + code_str!{
        #[verus_spec]
        fn call_dyn(x: &dyn X) {
            proof_with!{Ghost(3u64) => Ghost(g2)}
            let r = x.f(7);
            proof!{ assert(r == 7); assert(g2 == 3); }
        }

        #[verus_verify]
        fn test() {
            call_dyn(&S);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_local_trait_associated_type code! {
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            type Item;

            #[verus_spec(ret =>
                with Ghost(g): Ghost<u64> -> g2: Ghost<u64>
                ensures g2 == g,
            )]
            fn f(&self, a: Self::Item) -> Self::Item;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            type Item = u64;

            #[verus_spec(with Ghost(g): Ghost<u64> -> g2: Ghost<u64>)]
            fn f(&self, a: u64) -> u64 {
                proof_with!{|= Ghost(g)}
                a
            }
        }

        #[verus_verify]
        fn test(s: &S) {
            proof_with!{Ghost(3u64) => Ghost(g2)}
            let _r = X::f(s, 7);
            proof!{ assert(g2 == 3); }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_local_trait_mixed_methods code! {
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(r =>
                with Ghost(g): Ghost<int> -> g2: Ghost<int>
                ensures r == a, g2@ == g + 1,
            )]
            fn ghost_method(&self, a: u64) -> u64;

            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                requires b == 1,
                ensures r == 2,
            )]
            fn tracked_method(&self) -> u64;

            #[verus_spec(r => ensures r == 5)]
            fn plain(&self) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<int> -> g2: Ghost<int>)]
            fn ghost_method(&self, a: u64) -> u64 {
                proof_decl!{ let ghost gg: int = g + 1; }
                proof_with!{|= Ghost(gg)}
                a
            }

            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn tracked_method(&self) -> u64 {
                2
            }

            fn plain(&self) -> u64 {
                5
            }
        }

        // one bound gives a generic caller both counterparts at once
        #[verus_verify]
        fn call_all<A: X>(x: &A) {
            proof_with!{Ghost(3int) => Ghost(g2)}
            let r = x.ghost_method(7);
            proof_with!{Tracked(1u64)}
            let q = x.tracked_method();
            let p = x.plain();
            proof!{ assert(r == 7); assert(g2 == 4); assert(q == 2); assert(p == 5); }
        }

        #[verus_verify]
        fn test() {
            call_all(&S);
        }
    } => Ok(())
}

test_verify_one_file! {
    // A plain call hits the stub's `requires(false)`; a bad extra argument fails `requires`.
    #[test] test_trait_with_missing_or_failed_requires
        TRAIT_WITH_GHOST_INPUT.to_string() + code_str!{
        #[verus_verify]
        impl X for S {
            #[verus_spec(with Ghost(g): Ghost<u64>)]
            fn f(&self, a: u64) -> u64 {
                a
            }
        }

        #[verus_spec]
        fn call_missing(s: &S) {
            let r = s.f(3); // FAILS
        }

        #[verus_spec]
        fn call_failed_requires(s: &S) {
            proof_with!{Ghost(300u64)}
            let r = s.f(3); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    // An impl that omits the trait's `with` clause implements no counterpart.
    #[test] test_trait_with_missing_in_impl
        TRAIT_WITH_GHOST_INPUT.to_string() + code_str!{
        #[verus_verify]
        impl X for S {
            fn f(&self, a: u64) -> u64 {
                a
            }
        }

        #[verus_verify]
        fn test(s: &S) {
            proof_with!{Ghost(3u64)}
            let r = s.f(3);
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot be overridden without repeating the `with` clause")
}

test_verify_one_file! {
    // rustc checks the extra parameters of the implementation against the trait.
    #[test] test_trait_with_mismatched_in_impl
        TRAIT_WITH_GHOST_INPUT.to_string() + code_str!{
        #[verus_verify]
        impl X for S {
            #[verus_spec(with Tracked(g): Tracked<u64>)]
            fn f(&self, a: u64) -> u64 {
                a
            }
        }
    } => Err(e) => assert_rust_error_msg_any(e, "incompatible type for trait")
}

test_verify_one_file! {
    // A default body is inherited by non-overriding impls; overriding impls supply their own.
    #[test] test_trait_with_default_body code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait T {
            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                requires b == 1,
                ensures r >= 2,
            )]
            fn g(&self) -> u64 {
                2
            }
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        struct S2;

        #[verus_verify]
        impl T for S {
            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                ensures r == 7,
            )]
            fn g(&self) -> u64 {
                7
            }
        }

        #[verus_verify]
        impl T for S2 {}

        #[verus_verify]
        fn test() {
            proof_with!{Tracked(1u64)}
            let a = S.g();
            proof!{ assert(a == 7); }
            proof_with!{Tracked(1u64)}
            let b = S2.g();
            proof!{ assert(b >= 2); }
        }

        #[verus_verify]
        fn test_generic<A: T>(x: &A) {
            proof_with!{Tracked(1u64)}
            let r = x.g();
            proof!{ assert(r >= 2); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // An override that drops the `with` clause would otherwise inherit the default's contract.
    #[test] test_trait_with_default_body_missing_in_impl code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait T {
            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                ensures r == 1,
            )]
            fn g(&self) -> u64 {
                1
            }
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl T for S {
            fn g(&self) -> u64 {
                2
            }
        }

        #[verus_verify]
        fn test() {
            proof_with!{Tracked(1u64)}
            let r = S.g();
            proof!{ assert(r == 1); }
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot be overridden without repeating the `with` clause")
}

test_verify_one_file! {
    // An override without the `with` clause leaves the counterpart unimplemented.
    #[test] test_trait_with_missing_in_impl_of_several code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait T {
            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn g(&self) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl T for S {
            fn g(&self) -> u64 {
                3
            }
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot be overridden without repeating the `with` clause")
}

// --- calls to a trait `with` method resolve to its counterpart ---

// A trait whose method `m` has a `Tracked` input and ensures `r == 2`, implemented for `S`.

const TRAIT_WITH_TRACKED_INPUT: &str = code_str! {
    use vstd::prelude::*;

    #[verus_verify]
    trait T {
        #[verus_spec(r =>
            with Tracked(b): Tracked<u64>
            ensures r == 2,
        )]
        fn m(&self) -> u64;
    }

    #[verus_verify]
    struct S;

    #[verus_verify]
    impl T for S {
        #[verus_spec(with Tracked(b): Tracked<u64>)]
        fn m(&self) -> u64 {
            2
        }
    }
};

// Like `TRAIT_WITH_TRACKED_INPUT`, but `m` also requires `b == 1`.

const TRAIT_WITH_TRACKED_INPUT_REQUIRES: &str = code_str! {
    use vstd::prelude::*;

    #[verus_verify]
    trait T {
        #[verus_spec(r =>
            with Tracked(b): Tracked<u64>
            requires b == 1,
            ensures r == 2,
        )]
        fn m(&self) -> u64;
    }

    #[verus_verify]
    struct S;

    #[verus_verify]
    impl T for S {
        #[verus_spec(with Tracked(b): Tracked<u64>)]
        fn m(&self) -> u64 {
            2
        }
    }
};

test_verify_one_file! {
    // An inherent method named like the counterpart cannot hijack the call.
    #[test] test_inherent_impostor_does_not_hijack_method_call
        TRAIT_WITH_TRACKED_INPUT.to_string() + code_str!{
        #[verus_verify]
        impl S {
            #[verus_spec(r =>
                ensures r == 7,
            )]
            fn _VERUS_VERIFIED_m(&self, _b: Tracked<u64>) -> u64 {
                7
            }
        }

        #[verus_verify]
        fn test(s: S) {
            proof_with!{Tracked(1u64)}
            let r = s.m();
            proof!{ assert(r == 2); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Rust prefers the inherent `m` (no counterpart), so using the trait contract would be unsound.
    #[test] test_inherent_shadowing_trait_with_method_rejected
        TRAIT_WITH_TRACKED_INPUT.to_string() + code_str!{
        #[verus_verify]
        impl S {
            #[verus_spec(r =>
                ensures r == 5,
            )]
            fn m(&self) -> u64 {
                5
            }
        }

        #[verus_verify]
        fn test(s: S) {
            proof_with!{Tracked(1u64)}
            let r = s.m();
            proof!{ assert(r == 2); }
        }
    } => Err(err) => assert_vir_error_msg(err, "is not declared with `#[verus_spec(with ..)]")
}

test_verify_one_file! {
    // A smart-pointer receiver must not hide the inherent shadowing.
    #[test] test_inherent_shadowing_through_deref_rejected
        TRAIT_WITH_TRACKED_INPUT.to_string() + code_str!{
        #[verus_verify]
        impl S {
            #[verus_spec(r =>
                ensures r == 5,
            )]
            fn m(&self) -> u64 {
                5
            }
        }

        #[verus_verify]
        fn test(s: Box<S>) {
            proof_with!{Tracked(1u64)}
            let r = s.m();
            proof!{ assert(r == 2); }
        }
    } => Err(err) => assert_vir_error_msg(err, "is not declared with `#[verus_spec(with ..)]")
}

test_verify_one_file! {
    // Without shadowing, a dereferenced receiver reaches the counterpart.
    #[test] test_with_call_through_deref_receiver
        TRAIT_WITH_TRACKED_INPUT.to_string() + code_str!{
        #[verus_verify]
        fn test(s: Box<S>) {
            proof_with!{Tracked(1u64)}
            let r = s.m();
            proof!{ assert(r == 2); }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_inherent_shadowing_trait_with_path_call_rejected
        TRAIT_WITH_TRACKED_INPUT.to_string() + code_str!{
        #[verus_verify]
        impl S {
            #[verus_spec(r =>
                ensures r == 5,
            )]
            fn m(&self) -> u64 {
                5
            }
        }

        #[verus_verify]
        fn test(s: S) {
            proof_with!{Tracked(1u64)}
            let r = S::m(&s);
            proof!{ assert(r == 2); }
        }
    } => Err(err) => assert_vir_error_msg(err, "is not declared with `#[verus_spec(with ..)]")
}

test_verify_one_file! {
    #[test] test_qualified_with_call_is_not_shadowed
        TRAIT_WITH_TRACKED_INPUT.to_string() + code_str!{
        #[verus_verify]
        impl S {
            #[verus_spec(r =>
                ensures r == 5,
            )]
            fn m(&self) -> u64 {
                5
            }
        }

        #[verus_verify]
        fn test_qualified(s: S) {
            proof_with!{Tracked(1u64)}
            let r = <S as T>::m(&s);
            proof!{ assert(r == 2); }
        }

        #[verus_verify]
        fn test_trait_path(s: S) {
            proof_with!{Tracked(1u64)}
            let r = T::m(&s);
            proof!{ assert(r == 2); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // An unrelated type's inherent `with` method of the same name does not interfere.
    #[test] test_unrelated_inherent_with_method_of_same_name
        TRAIT_WITH_TRACKED_INPUT.to_string() + code_str!{
        #[verus_verify]
        struct Unrelated;

        #[verus_verify]
        impl T for Unrelated {
            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn m(&self) -> u64 {
                2
            }
        }

        #[verus_verify]
        impl Unrelated {
            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                ensures r == 5,
            )]
            fn m(&self) -> u64 {
                5
            }
        }

        #[verus_verify]
        fn test(s: S, u: Unrelated) {
            proof_with!{Tracked(1u64)}
            let r = s.m();
            proof!{ assert(r == 2); }

            proof_with!{Tracked(1u64)}
            let r2 = u.m();
            proof!{ assert(r2 == 5); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // A callee path through an associated type leaves several segments for type checking.
    #[test] test_with_call_through_associated_type
        TRAIT_WITH_TRACKED_INPUT_REQUIRES.to_string() + code_str!{
        #[verus_verify]
        trait A {
            type B: T;
        }

        #[verus_verify]
        struct SA;

        #[verus_verify]
        impl A for SA {
            type B = S;
        }

        #[verus_verify]
        fn generic<X: A>(b: &X::B) {
            proof_with!{Tracked(1u64)}
            let r = X::B::m(b);
            proof!{ assert(r == 2); }
        }

        #[verus_verify]
        fn qualified(s: &S) {
            proof_with!{Tracked(1u64)}
            let r = <SA as A>::B::m(s);
            proof!{ assert(r == 2); }
        }

        #[verus_verify]
        fn generic_bad<X: A>(b: &X::B) {
            proof_with!{Tracked(2u64)}
            let r = X::B::m(b); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    // `use T::m; m(..)` has no trait segment, so one naming the companion is inserted.
    #[test] test_with_call_through_imported_trait_method ["no-auto-import-verus_builtin"] =>
        // the features must precede the prelude, which is therefore written here
        code_str!{
            #![feature(proc_macro_hygiene)]
            #![feature(import_trait_associated_functions)]
            use verus_builtin::*;
            use verus_builtin_macros::*;
        }.to_string() + TRAIT_WITH_TRACKED_INPUT_REQUIRES + code_str!{
        use T::m;

        #[verus_verify]
        fn good(s: &S) {
            proof_with!{Tracked(1u64)}
            let r = m(s);
            proof!{ assert(r == 2); }
        }

        #[verus_verify]
        fn bad(s: &S) {
            proof_with!{Tracked(2u64)}
            let r = m(s); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// --- `with` on the methods of an external trait ---
//
// An external trait cannot declare the verified counterparts of its methods:
// they take extra parameters, so they are not members of it. Declaring a `with`
// clause on its proxy derives a companion trait, a subtrait of the external
// trait, that declares the counterparts. The method of the external trait keeps
// `requires(false)`, so verified code can only reach it through its
// counterpart, and an implementation of the external trait is split between the
// two traits.

const EXTERNAL_TRAIT: &str = code_str! {
    use vstd::prelude::*;

    #[verifier::external]
    trait T {
        fn f(&self, a: u64) -> u64;
    }

    #[verus_verify]
    struct S;

    #[verus_verify]
    #[verifier::external_trait_specification]
    trait ExT {
        type ExternalTraitSpecificationFor: T;

        #[verus_spec(r =>
            with Ghost(g): Ghost<int> -> g2: Ghost<int>
            ensures r == a, g2@ == g + 1,
        )]
        fn f(&self, a: u64) -> u64;
    }

    #[verus_verify]
    impl T for S {
        #[verus_spec(with Ghost(g): Ghost<int> -> g2: Ghost<int>)]
        fn f(&self, a: u64) -> u64 {
            proof_decl!{ let ghost gg: int = g + 1; }
            proof_with!{|= Ghost(gg)}
            a
        }
    }
};

test_verify_one_file! {
    #[test] test_external_trait_generic_proxy code! {
        use vstd::prelude::*;

        #[verifier::external]
        trait T<A> {
            fn f(&self, a: A) -> A;
        }

        #[verus_verify]
        #[verifier::external_trait_specification]
        trait ExT<A> {
            type ExternalTraitSpecificationFor: T<A>;

            #[verus_spec(r =>
                with Ghost(g): Ghost<int> -> g2: Ghost<int>
                ensures g2@ == g + 1,
            )]
            fn f(&self, a: A) -> A;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl T<u64> for S {
            #[verus_spec(with Ghost(g): Ghost<int> -> g2: Ghost<int>)]
            fn f(&self, a: u64) -> u64 {
                proof_decl!{ let ghost gg: int = g + 1; }
                proof_with!{|= Ghost(gg)}
                a
            }
        }

        #[verus_spec]
        fn call_generic<A: T<u64>>(x: &A) {
            proof_with!{Ghost(3int) => Ghost(g2)}
            let _r = x.f(7);
            proof!{ assert(g2 == 4); }
        }

        #[verus_verify]
        fn test() {
            call_generic(&S);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_external_trait_mixed_methods code! {
        use vstd::prelude::*;

        #[verifier::external]
        trait T {
            fn tracked_method(&self) -> u64;
            fn output_only(&self, a: u64) -> u64;
            fn plain(&self) -> u64;
        }

        #[verus_verify]
        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;

            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                requires b == 1,
                ensures r == 2,
            )]
            fn tracked_method(&self) -> u64;

            #[verus_spec(r =>
                with -> g2: Ghost<int>
                ensures r == a, g2@ == a,
            )]
            fn output_only(&self, a: u64) -> u64;

            #[verus_spec(r => ensures r == 5)]
            fn plain(&self) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl T for S {
            #[verus_spec(with Tracked(b): Tracked<u64>)]
            fn tracked_method(&self) -> u64 {
                2
            }

            #[verus_spec(with -> g2: Ghost<int>)]
            fn output_only(&self, a: u64) -> u64 {
                proof_decl!{ let ghost gg: int = a as int; }
                proof_with!{|= Ghost(gg)}
                a
            }

            fn plain(&self) -> u64 {
                5
            }
        }

        #[verus_verify]
        fn test() {
            proof_with!{Tracked(1u64)}
            let q = S.tracked_method();
            proof_with!{=> Ghost(g2)}
            let o = S.output_only(4);
            let p = S.plain();
            proof!{ assert(q == 2); assert(o == 4); assert(g2 == 4); assert(p == 5); }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // Compile the qualified call after erasing the companion trait.
    #[test] test_external_trait_cross_module_qualified_call ["--compile"] => code! {
        use vstd::prelude::*;

        mod spec {
            use vstd::prelude::*;

            #[verifier::external]
            pub trait T {
                fn f(&self, a: u64) -> u64;
            }

            #[verus_verify]
            #[verifier::external_trait_specification]
            pub trait ExT {
                type ExternalTraitSpecificationFor: T;

                #[verus_spec(r =>
                    with Ghost(g): Ghost<int> -> g2: Ghost<int>
                    ensures r == a, g2@ == g + 1,
                )]
                fn f(&self, a: u64) -> u64;
            }
        }

        mod imp {
            use vstd::prelude::*;

            #[verus_verify]
            pub struct S;

            #[verus_verify]
            impl super::spec::T for S {
                #[verus_spec(with Ghost(g): Ghost<int> -> g2: Ghost<int>)]
                fn f(&self, a: u64) -> u64 {
                    proof_decl!{ let ghost gg: int = g + 1; }
                    proof_with!{|= Ghost(gg)}
                    a
                }
            }
        }

        #[verus_verify]
        fn test() {
            proof_with!{Ghost(3int) => Ghost(g2)}
            let r = spec::T::f(&imp::S, 7);
            proof!{ assert(r == 7); assert(g2 == 4); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // The external trait method itself has `requires(false)`.
    #[test] test_external_trait_with_plain_call
        EXTERNAL_TRAIT.to_string() + code_str!{
        #[verus_verify]
        fn test() {
            let r = S.f(7); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    // The impl is checked against the proxy's spec, which it does not repeat.
    #[test] test_external_trait_with_failed_ensures code! {
        use vstd::prelude::*;

        #[verifier::external]
        trait T {
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;

            #[verus_spec(r =>
                with Ghost(g): Ghost<int> -> g2: Ghost<int>
                ensures r == a, g2@ == g + 1, // FAILS
            )]
            fn f(&self, a: u64) -> u64;
        }

        #[verus_verify]
        impl T for S {
            #[verus_spec(with Ghost(g): Ghost<int> -> g2: Ghost<int>)]
            fn f(&self, a: u64) -> u64 {
                proof_decl!{ let ghost gg: int = g + 2; }
                proof_with!{|= Ghost(gg)}
                a
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    // An inherited foreign default body is assumed to meet the proxy's spec.
    #[test] test_external_trait_with_default_body code!{
        use vstd::prelude::*;

        #[verifier::external]
        trait T {
            fn g(&self) -> u64 {
                2
            }
        }

        #[verus_verify]
        struct S;

        #[verus_verify]
        #[verifier::external_trait_specification]
        trait ExT {
            type ExternalTraitSpecificationFor: T;

            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                requires b == 1,
                ensures r == 2,
            )]
            fn g(&self) -> u64;
        }

        #[verus_verify]
        impl T for S {}

        #[verus_verify]
        fn test() {
            proof_with!{Tracked(1u64)}
            let q = S.g();
            proof!{ assert(q == 2); }
        }
    } => Ok(())
}

// --- The verified counterpart is not callable by hand ---
//
// It is only reachable through the function it belongs to, with `proof_with!`.
// Calling it directly would hand the caller the extra ghost/tracked outputs
// without any obligation to supply the inputs, and the counterpart is not part
// of the compiled program.

test_verify_one_file! {
    #[test] test_counterpart_direct_call_rejected code!{
        use vstd::prelude::*;

        #[verus_spec(r =>
            with Tracked(t): Tracked<u64>
            ensures r == 1,
        )]
        fn f() -> u64 {
            1
        }

        #[verus_spec]
        fn bad() {
            let _x = _VERUS_VERIFIED_f(Tracked::assume_new());
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot be called directly")
}

const STRUCT_WITH_TRACKED_METHOD: &str = code_str! {
    use vstd::prelude::*;

    #[verus_verify]
    struct S;

    #[verus_verify]
    impl S {
        #[verus_spec(r =>
            with Tracked(t): Tracked<u64>
            ensures r == 1,
        )]
        fn m(&self) -> u64 {
            1
        }
    }
};

test_verify_one_file! {
    #[test] test_counterpart_direct_method_call_rejected
        STRUCT_WITH_TRACKED_METHOD.to_string() + code_str!{
        #[verus_spec]
        fn bad(s: &S) {
            let _x = s._VERUS_VERIFIED_m(Tracked::assume_new());
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot be called directly")
}

test_verify_one_file! {
    #[test] test_counterpart_direct_method_call_nested_rejected
        STRUCT_WITH_TRACKED_METHOD.to_string() + code_str!{
        #[verus_spec(r =>
            with Tracked(t): Tracked<u64>
            ensures r == x,
        )]
        fn id(x: u64) -> u64 {
            x
        }

        #[verus_spec]
        fn bad_nested(s: &S) {
            proof_with!{Tracked(1u64)}
            let _x = id(s._VERUS_VERIFIED_m(Tracked::assume_new()));
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot be called directly")
}

test_verify_one_file! {
    #[test] test_with_call_inside_closure_fails_precondition
        FN_WITH_TRACKED_EQ.to_string() + code_str!{
        #[verus_verify]
        fn call_in_closure() {
            let c = || -> u8 {
                proof_with!{Tracked(4u8)}
                let y = f(3); // FAILS
                y
            };
            let _v = c();
        }
    } => Err(e) => assert_one_fails(e)
}
