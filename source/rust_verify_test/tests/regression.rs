#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_189a verus_code! {
        use vstd::set::*;

        proof fn test_sets_1() {
            let s1: Set<i32> = Set::empty().insert(1);
            let s2: Set<i32> = Set::empty();
            assert(!s2.contains(1));
            // assert(!s1.ext_equal(s2));
            assert(s1 !== s2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_189b verus_code! {
        use vstd::set::*;

        spec fn different_set<V>(s: Set<V>) -> Set<V> { s }

        proof fn test_sets_1() {
            let s1: Set<i32> = Set::empty().insert(1);

            assert (exists|s3: Set<i32>| different_set(s3) !== s1) by {
                assert(!different_set(Set::empty()).contains(1i32));
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_verifier_truncate_allowed_on_cast verus_code! {
        fn test(a: u64) -> u8 {
            #[verifier(truncate)] (a as u8)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_hygienic_identifiers_regression_279 verus_code! {
        macro_rules! assert_with_binding {
            ($s1:expr) => {
                let s1 = $s1;
                vstd::pervasive::assert(s1);
            }
        }

        proof fn test() {
            let s1: nat = 0;
            assert_with_binding!(true);
            assert(s1 === 0);
        }

        macro_rules! recursor {
            () => { };
            ($e:expr, $($tail:tt)*) => {
                let s: u8 = $e;
                recursor!($($tail)*);   // this recursive call defines a *distinct* variable called `s`
                assert_(s == $e);       // this `s` should refer to the decl from 2 lines above
            };
        }

        macro_rules! iterer {
            ($($e:expr),*) => {
                $( let s: u8 = $e; )*   // This makes two let statements, but rustc treats them as the same identifier
                assert_(s == 3);        // So this always refers to the last `s` that was declared
            };
        }

        proof fn test_more_complex() {
            let s: u8 = 20;

            recursor!(5, 6,);
            iterer!(2, 3);

            assert_(s == 20);

            let s: u8 = 19;
            assert_(s == 19);
        }

        macro_rules! closure {
            ($e:expr) => {
                closure_to_fn_spec(|s: u8| { $e })
            };
        }

        proof fn test_closure_param_names() {
            let foo = |s: u8| {
                closure!(s)(20) // when we pass `s` into the macro, it should refer to the `s` in the line above
            };

            assert_(foo(5) == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] test_bad_span_for_postcondition_failure_regression_281 verus_code! {
        #[is_variant]
        enum Enum {
            A,
            B,
        }


        fn test(a: u32) -> (res: Enum)
            ensures (match res {
                Enum::A => a <= 10,
                Enum::B => a > 10, // FAILS
            }) {

            Enum::B
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] fields_from_macros_not_treated_as_distinct_identifiers verus_code! {
        struct Foo(pub u64);

        // Internally, the use of .0 in the macro creates an identifier `0`
        // with some extra info that is used for macro hygeine purposes.
        // However, that info needs to be ignored: the field access .0
        // should be treated like any other .0 access.

        macro_rules! some_macro {
            ($foo:ident) => {
                vstd::pervasive::assert($foo.0 == 20);
            }
        }

        proof fn some_func() {
            let foo = Foo(20);
            assert(foo.0 == 20);

            some_macro!(foo);
        }

        struct Bar { val: u64 }

        macro_rules! some_macro2 {
            ($bar:ident) => {
                vstd::pervasive::assert($bar.val == 30);
            }
        }

        proof fn some_func2() {
            let bar = Bar { val: 30 };
            assert(bar.val == 30);

            some_macro2!(bar);

        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] parse_named_return_type_with_comma_in_type_args verus_code! {
        use vstd::map::*;

        proof fn some_proof() -> (m: Map<int, int>)
            ensures m === Map::empty()
        {
            Map::empty()
        }

        proof fn cats() {
            let m = some_proof();
            assert(m === Map::empty());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] forall_in_ensures_with_return_keyword_regression_216 verus_code! {
        #[verifier::spec]
        fn f(a: nat) -> bool {
            true
        }

        fn g() -> (res: bool)
            ensures forall|i: nat| f(i)
        {
            return true;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] reveal_func_unused_from_other_module_issue_411 verus_code! {
        mod X {
            #[verifier(opaque)]
            pub open spec fn foo() -> bool { true }
        }

        proof fn test() {
            reveal(X::foo);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] reveal_exec_fn_issue_411 verus_code! {
        pub fn foo() -> bool { true }

        proof fn test() {
            reveal(foo);
        }
    } => Err(err) => assert_vir_error_msg(err, "reveal/fuel statements require a spec-mode function")
}

test_verify_one_file! {
    #[test] reveal_proof_fn_issue_411 verus_code! {
        pub proof fn foo() -> bool { true }

        proof fn test() {
            reveal(foo);
        }
    } => Err(err) => assert_vir_error_msg(err, "reveal/fuel statements require a spec-mode function")
}

test_verify_one_file! {
    #[test] let_with_parens_issue_260 verus_code! {
        fn f() {
            let (x):usize = 0;
            assert(x == 0);
        }

        fn g() {
            let (x):usize = 0;
            assert(x == 1); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] use_statement_of_spec_fn_issue293 verus_code! {
        mod Y {
            #![allow(dead_code)] // this was needed for the original crash

            use builtin::*;
            use builtin_macros::*;

            verus!{
                mod X {
                    pub open spec fn foo();
                }

                proof fn some_proof_fn() {
                    let x = foo();
                }
            }

            use X::foo; // this was needed for the original crash
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] is_variant_in_exec_issue_341 verus_code! {
        pub struct Lock {}

        #[is_variant]
        pub enum OptionX<T> {
            NoneX,
            SomeX(T)
        }

        pub fn what_is_wrong() -> bool
        {
            let opt_lock = OptionX::SomeX(Lock{});
            let lock = opt_lock.get_SomeX_0();   // This line triggers panic
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot get variant in exec mode")
}

test_verify_one_file! {
    #[ignore] #[test] trait_argument_names_issue278 verus_code! {
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
    #[test] reveal_non_opaque_issue236_1 verus_code! {
        spec fn is_true(a: bool) -> bool { a }

        proof fn foo() {
            hide(is_true);
            assert(is_true(true)); // FAILS
            reveal(is_true);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] reveal_non_opaque_issue236_2 verus_code! {
        spec fn is_true(a: bool) -> bool { a }

        proof fn foo() {
            hide(is_true);
            reveal(is_true);
            assert(is_true(true));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] reveal_with_fuel_non_opaque_non_recursive_issue236_373_pass verus_code! {
        spec fn is_true(a: bool) -> bool { a }

        proof fn foo() {
            reveal_with_fuel(is_true, 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] reveal_with_fuel_non_opaque_non_recursive_issue236_373_fail verus_code! {
        spec fn is_true(a: bool) -> bool { a }

        proof fn foo() {
            reveal_with_fuel(is_true, 2);
        }
    } => Err(err) => assert_vir_error_msg(err, "reveal_with_fuel statements require a function with a decreases clause")
}

test_verify_one_file_with_options! {
    #[test] call_spec_fn_from_external_body_issue_257 ["--compile"] => verus_code! {
        #[verifier(external_body)]
        fn f(x: usize) -> usize {
            id(x)
        }

        pub open spec fn id(x: usize) -> usize {
            x
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] air_function_names_issue_376 verus_code! {
        enum Nat {
            Zero,
            Succ(Box<Nat>),
        }

        spec fn height(n: Nat) -> nat
            decreases n
        {
            match n {
                Nat::Zero => 0,
                Nat::Succ(box m) => height(m),
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] parse_empty_requires_ensure_invariant verus_code! {
        proof fn test()
            requires
        {
        }

        proof fn test2()
            ensures
        {
        }

        fn test3()
        {
            loop
                invariant
            {
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] const_name_in_lifetime_generate_regression_563 verus_code! {
        pub spec const CONST_VALUE: nat = 32;
        #[verifier(external_body)]
        struct Data { }
        impl Data {
            proof fn foo(self) {
                let value: nat = CONST_VALUE as nat;
                if vstd::prelude::arbitrary::<nat>() >= value {
                } else {
                }
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] nat_no_use_builtin_issue575 ["no-auto-import-builtin"] => code! {
        use vstd::prelude::*;

        pub struct MyType {
            x: nat,
        }

        fn main() { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] poly_invalid_air_regression_577 verus_code! {
        use vstd::{prelude::*, vec::*};

        pub trait Foo {
            fn do_something(&mut self, val: u8);
        }

        pub struct Bar {
            vec: Vec<u8>,
            field0: u8
        }

        impl Bar {
            fn new() -> Self {
                Self {
                    vec: Vec::with_capacity(2),
                    field0: 0,
                }
            }
        }

        impl Foo for Bar {
            fn do_something(&mut self, val: u8) {
                self.field0 = val;
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] def_id_names_for_builtins_regression_588 ["no-auto-import-builtin"] => code! {
        use vstd::{prelude::*, seq::*};

        verus! {

        spec fn pred(a: nat, s: Seq<int>) -> bool
        {
            a < s.len()
        }

        } // verus!
    } => Ok(())
}
