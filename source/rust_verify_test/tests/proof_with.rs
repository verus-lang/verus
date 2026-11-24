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
    => Err(e) => {
        // one error per case, so no case can stop being rejected unnoticed
        assert_eq!(e.errors.len(), 3);
        assert_rust_error_msgs(e, &["mismatched types"; 3]);
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
