#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Tests for `#[verus_spec(with ..)]`: extra ghost/tracked inputs and outputs.
//
// A call site written as `proof_with!{..} f(..)` is redirected to the verified
// counterpart of `f` on the lowered HIR, before type checking, so that rustc
// type checks, borrow checks and lifetime checks the extra arguments.
//
// Independent positive cases are grouped into a single `=> Ok(())` test, one
// case per module so that names do not clash and a failure points at the case;
// failing cases are kept separate so each keeps its own asserted diagnostic.

// Wrap the source of one case in a named module, keeping the cases of a grouped
// test independent.
fn in_mod(name: &str, body: &str) -> String {
    format!("mod {name} {{\n{body}\n}}\n")
}
test_verify_one_file! {
    #[test] test_attribute_form_group
        code_str!{
            use vstd::prelude::*;

            // free function with extra Tracked and Ghost inputs
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

            // inherent method with extra inputs
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

            // the extra Tracked reference may outlive the return with a `'b: 'a` bound
            #[verus_spec(with Tracked(c): Tracked<&'a u64>)]
            fn lt<'a>(a: &'a u64, b: u64) -> &'a u64 {
                a
            }

            #[verus_spec]
            fn lt_caller<'a, 'b: 'a>(a: &'a u64, b: u64, c: Tracked<&'b u64>) -> &'a u64 {
                proof_with!{c}
                lt(a, b)
            }

            // the extra input's type may be a generic parameter
            #[verus_spec(with Tracked(b): Tracked<T>)]
            fn gen<T>(a: T) {}

            #[verus_spec]
            fn call_gen() {
                proof_with!{Tracked(1u64)}
                gen(0u64);
            }
        }.to_string()
        // the reserved counterpart name is an ordinary function when the macro did
        // not generate it (no `f` here has a `with` clause)
        + &in_mod("counterpart_name_ordinary", code_str!{
            use vstd::prelude::*;

            #[verus_spec(ret =>
                ensures ret == 7,
            )]
            fn _VERUS_WITH_f() -> u64 {
                7
            }

            #[verus_spec]
            fn caller() {
                let x = _VERUS_WITH_f();
                proof!{ assert(x == 7); }
            }
        })
        // a call inside a closure body, a separate body in the same owner, is
        // redirected too
        + &in_mod("closure_call", &(FN_WITH_TRACKED_EQ.to_string() + code_str!{
            #[verus_verify]
            fn call_in_closure() {
                let c = || -> u8 {
                    proof_with!{Tracked(3u8)}
                    let y = f(3);
                    y
                };
                let _v = c();
            }
        }))
    => Ok(())
}

test_verify_one_file! {
    // A wrong extra argument fails the precondition, and omitting `proof_with!`
    // reaches the stub with `requires(false)`.
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
        assert!(e.errors.iter().any(|x| x.message.contains("`test` does not accept extra ghost/tracked arguments")));
    }
}

// ---- type, mode and lifetime checking is done by rustc ----

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
    // The extra `Tracked`/`Ghost` input keeps its lifetime obligations: a
    // shorter-lived reference passed where a longer-lived one is declared is a
    // `lifetime may not live long enough` error.
    #[test] test_proof_with_lifetime_mismatch
        // through a `Tracked` input
        in_mod("tracked", code_str!{
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
        })
        // through a `Ghost` input
        + &in_mod("ghost", code_str!{
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
        })
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
    #[test] test_extra_outputs_group
        code_str!{
            use vstd::prelude::*;

            // one extra Ghost output, produced with `proof_with!{|= ..}`, bound
            // at the call site or ignored with `=> _`
            #[verus_spec(ret =>
                with -> z: Ghost<u32>
                ensures ret == 1u64, z@ == 2u32,
            )]
            fn one_output() -> u64 {
                proof_with!{|= Ghost(2u32)}
                1
            }

            #[verus_spec]
            fn call_bind() {
                proof_with!{=> Ghost(z)}
                let r = one_output();
                proof!{ assert(r == 1); assert(z == 2); }
            }

            #[verus_spec]
            fn call_ignore() {
                proof_with!{=> _}
                let _ = one_output();
            }

            // several extra outputs, produced and bound as a tuple
            #[verus_spec(ret =>
                with -> y: Ghost<u8>, z: Ghost<u32>
                ensures ret == 1u64, y@ == 3u8, z@ == 2u32,
            )]
            fn many_outputs() -> u64 {
                proof_with!{|= (Ghost(3u8), Ghost(2u32))}
                1
            }

            #[verus_spec]
            fn call_many() {
                proof_with!{=> (Ghost(y), Ghost(z))}
                let r = many_outputs();
                proof!{ assert(r == 1); assert(y == 3); assert(z == 2); }
            }

            // extra inputs (including a `Tracked` mutable reference) and an
            // output together
            #[verus_spec(ret =>
                with Tracked(y): Tracked<&mut int>, Ghost(w): Ghost<u32> -> z: Ghost<u32>
                requires x < 100, *old(y) < 100,
                ensures *final(y) == x, ret == x, z@ == x,
            )]
            fn inout(x: u32) -> u32 {
                proof!{
                    *y = x as int;
                }
                proof_with!{|= Ghost(x)}
                x
            }

            #[verus_spec]
            fn call_inout() {
                proof_decl!{
                    let tracked mut y = 0int;
                }
                proof_with!{Tracked(&mut y), Ghost(0u32) => Ghost(z)}
                let r = inout(1);
                proof!{ assert(r == 1); assert(y == 1); assert(z == 1); }
            }
        }.to_string()
    => Ok(())
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

// A function with an extra `Tracked` input, in a submodule, and an alias to it.

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
    #[test] test_paths_and_aliases_group
        // a qualified path and a module-item alias both reach the counterpart
        in_mod("qualified_paths", &(MOD_FN_WITH_TRACKED.to_string() + code_str!{
            #[verus_spec]
            fn call_qualified() {
                proof_with!{Tracked(1u64)}
                m::test(0);
            }

            #[verus_spec]
            fn call_aliased() {
                proof_with!{Tracked(1u64)}
                aliased(0);
            }
        }))
        // a function defined in another module is reached from the call site
        + &in_mod("cross_module", code_str!{
            use vstd::prelude::*;

            mod inner {
                use vstd::prelude::*;

                #[verus_spec(ret =>
                    with Ghost(extra): Ghost<u64>
                    requires a < 100 && extra@ < 100,
                    ensures ret == a,
                )]
                pub fn copy_u64(a: u64) -> u64 {
                    a
                }
            }

            #[verus_spec]
            fn test_call_cross_module() {
                use inner::copy_u64;
                proof_with!{Ghost(5u64)}
                let ret = copy_u64(10);
                proof!{ assert(ret == 10); }
            }
        })
    => Ok(())
}

test_verify_one_file! {
    // The same call without `proof_with!` reaches the unverified stub, both
    // through the qualified path and through the alias.
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
    // Without `proof_with!`, the call goes to the unverified stub, whose
    // `requires(false)` no caller can satisfy, through an alias just the same.
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
    // A user-defined function named `proof_with` is not the builtin marker and must
    // not trigger the call redirect.
    #[test] test_user_defined_proof_with_is_not_a_marker code!{
        use vstd::prelude::*;

        mod verus_builtin {
            use vstd::prelude::*;
            #[verus_verify]
            pub fn proof_with<A, B>(_a: A, b: B) -> B {
                b
            }
        }

        #[verifier::external_body]
        fn opaque(a: u64) -> u64 {
            a
        }

        #[verus_spec]
        fn call_user_proof_with() -> u64 {
            verus_builtin::proof_with(1u64, opaque(2))
        }
    } => Ok(())
}

// --- `with` on an external function specification (`assume_specification`) ---
//
// The `assume_specification` keeps the exact signature of the external function
// and gains `requires(false)`, so a plain call fails. The verified counterpart
// carries the extra ghost/tracked parameters, and `proof_with!` redirects the
// call to it.

// An external function and its `assume_specification`, which gives it an extra
// `Tracked` input constrained to equal its `x` argument.

test_verify_one_file_with_options! {
    // The verified counterpart is named after the function the user wrote, so
    // `--verify-function` selects it and messages do not mention the twin.
    #[test] test_verify_function_selects_counterpart
        ["--verify-function test", "--verify-root"] => code!{
        use vstd::prelude::*;

        #[verus_spec(r =>
            with Tracked(b): Tracked<u64>
            requires b == 1,
            ensures r == 3u64,
        )]
        fn test(a: u64) -> u64 {
            a
        }
    } => Err(err) => assert_eq!(err.errors.len(), 1)
}

test_verify_one_file_with_options! {
    // The counterpart of a method takes the name of the method the user wrote in
    // the friendly name too, which is what `--verify-function` matches on.
    #[test] test_verify_function_selects_method_counterpart
        ["--verify-function S::f", "--verify-root"] => code!{
        use vstd::prelude::*;

        #[verus_verify]
        struct S;

        #[verus_verify]
        impl S {
            #[verus_spec(r =>
                with Tracked(b): Tracked<u64>
                requires b == 1,
                ensures r == 3u64,
            )]
            fn f(&self, a: u64) -> u64 {
                a
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "postcondition not satisfied")
}

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
            let _x = _VERUS_WITH_f(Tracked::assume_new());
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot be called directly")
}

// A trait whose method `m` declares a `Tracked` input and ensures `r == 2`, with
// the implementation for `S`. The shadowing tests below add an inherent method
// of the same name to probe how the call resolves.

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
