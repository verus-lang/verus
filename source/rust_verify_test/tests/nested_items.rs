#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_ignorable_items verus_code! {
        mod m {
            // Verus can ignore 'use' item
            use super::*;

            pub open spec fn test() -> bool { true }
        }

        fn test_use_item() {
            use m::test as test2;
            assert(test2());
        }

        fn test_macro_item() {
            let mut x = 1;

            // Verus can ignore 'macro' item
            macro_rules! add_1 {
                () => {
                    x = x + 1;
                }
            }

            add_1!();

            assert(x == 2);
        }
    } => Ok(())
}

// TODO: spec fn, broadcast, etc.
// TODO: ownership check

test_verify_one_file! {
    #[test] test_attr_syntax_items_without_nested_spec code! {
        #[verus_spec(requires 1 + 1 == 2)]
        fn test() {
            const fn f1(i: u64) -> u64 {
                i / 2
            }
            fn f2(i: u64) -> u64 {
                i / 2
            }
            const C: u64 = 4 + 5;

            let x = f1(10);
            let y = f2(10);
            let z = C;
            proof! {
                assert(z == 9);
                assert(y == 5); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_attr_syntax_items_with_nested_spec code! {
        #[verus_spec(requires 1 + 1 == 2)]
        fn test() {
            #[verus_spec(r => ensures r == i / 2)]
            const fn f1(i: u64) -> u64 {
                i / 2
            }
            #[verus_spec(r => ensures r == i / 2)]
            fn f2(i: u64) -> u64 {
                i / 2
            }
            #[verus_spec()]
            const C: u64 = 4 + 5;

            let x = f1(10);
            let y = f2(10);
            let z = C;
            proof! {
                assert(x == 5);
                assert(y == 5);
                assert(z == 9);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_attr_syntax_items_ownership code! {
        struct S;

        verus! {
            #[verifier::external_body]
            proof fn produce() -> tracked S {
                panic!()
            }

            proof fn consume(tracked s: S) {
            }
        }

        #[verus_spec(requires 1 + 1 == 2)]
        fn test() {
            const C: u64 = {
                proof! {
                    let s = produce();
                    consume(s);
                    consume(s);
                }
                4 + 5
            };

            let z = C;
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] test_verus_items_without_nested_spec verus_code! {
        fn test() {
            const fn f1(i: u64) -> u64 {
                i / 2
            }
            fn f2(i: u64) -> u64 {
                i / 2
            }
            const C: u64 = 4 + 5;

            let x = f1(10);
            let y = f2(10);
            let z = C;
            assert(z == 9);
            assert(y == 5); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_verus_items_with_nested_spec verus_code! {
        fn test() {
            const fn f1(i: u64) -> (r: u64)
                ensures r == i / 2
            {
                i / 2
            }
            fn f2(i: u64) -> (r: u64)
                ensures r == i / 2
            {
                i / 2
            }
            const C: u64 = 4 + 5;

            let x = f1(10);
            let y = f2(10);
            let z = C;
            assert(x == 5);
            assert(y == 5);
            assert(z == 9);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_verus_items_ownership verus_code! {
        struct S;

        #[verifier::external_body]
        proof fn produce() -> tracked S {
            panic!()
        }

        proof fn consume(tracked s: S) {
        }

        fn test() {
            const C: u64 = {
                let s = produce();
                consume(s);
                consume(s);
                4 + 5
            };

            let z = C;
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] test_verus_items_ownership_nested verus_code! {
        fn test() {
            struct S;

            #[verifier::external_body]
            proof fn produce() -> tracked S {
                panic!()
            }

            proof fn consume(tracked s: S) {
            }

            const C: u64 = {
                let s = produce();
                consume(s);
                consume(s);
                4 + 5
            };

            let z = C;
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
}

test_verify_one_file! {
    #[test] test_ghost_items verus_code! {
        proof fn test() {
            spec fn f(i: int) -> int
                decreases i
            {
                if i <= 0 {
                    0
                } else {
                    f(i - 1) + 1
                }
            }

            broadcast proof fn p(i: int)
                ensures #[trigger] f(i) >= 0
                decreases i
            {
                if i > 0 {
                    p(i - 1);
                }
            }

            assert(f(200) >= 0) by {
                broadcast use p;
            }
            assert(f(100) >= 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] nested_items_in_spec_and_proof_fns_issue3134 verus_code! {
        #[verifier::external]
        fn ext(a: u8) -> u8 {
            a
        }

        spec fn nested_fn(x: u8) -> int {
            fn e() {
            }
            x + 1
        }

        spec fn nested_const(x: u8) -> int {
            const C: u8 = 0;
            x + 1
        }

        spec fn nested_assume_specification(x: u8) -> int {
            pub assume_specification[ ext ](a: u8) -> u8;
            x + 1
        }

        proof fn nested_fn_in_proof_fn(x: u8) -> (r: int)
            ensures
                r == x + 1,
        {
            fn e() {
            }
            x + 1
        }

        proof fn test() {
            assert(nested_fn(255) == 256);
            assert(nested_const(255) == 256);
            assert(nested_assume_specification(255) == 256);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] nested_proof_fn_then_proof_block_in_exec_fn_issue3134 verus_code! {
        fn test() {
            proof fn p() {
            }
            proof {
                p();
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] nested_exec_fn_in_proof_block_issue3134 verus_code! {
        fn test() {
            proof {
                fn e() {
                }
            }
        }
    } => Ok(())
}

const ITEM_MACRO_CALL_ERR: &str = "this item is produced by a macro call inside `verus!`";

test_verify_one_file! {
    #[test] item_macro_call_trait_impl_issue3154 verus_code! {
        pub trait Small {
            fn get(&self) -> (r: usize)
                ensures r < 10;
        }

        pub struct S;

        macro_rules! mk_impl {
            ($t:ty) => {
                impl Small for $t {
                    fn get(&self) -> usize { 200 }
                }
            };
        }

        mk_impl!(S);

        fn read<T: Small>(t: &T) -> u8 {
            let a: [u8; 10] = [0; 10];
            a[t.get()]
        }
    } => Err(err) => assert_vir_error_msg(err, ITEM_MACRO_CALL_ERR)
}

test_verify_one_file! {
    #[test] item_macro_call_fn_main_issue3154 verus_code! {
        macro_rules! mk_main {
            () => {
                fn main() {
                    let a: [u8; 10] = [0; 10];
                    let _ = a[200];
                }
            };
        }

        mk_main!();
    } => Err(err) => assert_vir_error_msg(err, ITEM_MACRO_CALL_ERR)
}

test_verify_one_file! {
    #[test] item_macro_call_item_passthrough_issue3154 verus_code! {
        pub trait Small {
            fn get(&self) -> (r: usize)
                ensures r < 10;
        }

        pub struct S;

        macro_rules! pass {
            ($i:item) => { $i };
        }

        macro_rules! nested {
            ($i:item) => { pass!($i); };
        }

        nested!(impl Small for S { fn get(&self) -> usize { 200 } });
    } => Err(err) => assert_vir_error_msg(err, ITEM_MACRO_CALL_ERR)
}

test_verify_one_file! {
    #[test] item_macro_call_macro_defined_outside_issue3154 code! {
        macro_rules! mk_fn {
            () => {
                fn unverified() -> u8 { 200 }
            };
        }

        ::verus_builtin_macros::verus! {
            mk_fn!();
        }
    } => Err(err) => assert_vir_error_msg(err, ITEM_MACRO_CALL_ERR)
}

test_verify_one_file! {
    #[test] item_macro_call_outside_verus_issue3154 code! {
        macro_rules! mk_fn {
            () => {
                fn unverified() -> u8 { 200 }
            };
        }

        mk_fn!();

        ::verus_builtin_macros::verus! {
            fn verified() {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] item_macro_call_in_verus_mod_issue3154 verus_code! {
        mod m {
            use vstd::prelude::*;

            pub trait Small {
                fn get(&self) -> (r: usize)
                    ensures r < 10; // FAILS
            }

            pub struct S;

            macro_rules! mk_impl {
                ($t:ty) => {
                    impl Small for $t {
                        fn get(&self) -> usize { 200 }
                    }
                };
            }

            mk_impl!(S);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] item_macro_call_output_in_verus_issue3154 verus_code! {
        pub trait Small {
            fn get(&self) -> (r: usize)
                ensures r < 10; // FAILS
        }

        pub struct S;

        macro_rules! mk_impl {
            ($t:ty) => {
                ::verus_builtin_macros::verus! {
                    impl Small for $t {
                        fn get(&self) -> usize { 200 }
                    }
                }
            };
        }

        mk_impl!(S);
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] item_macro_call_harmless_items_issue3154 verus_code! {
        mod m {
            pub open spec fn f() -> bool { true }
        }

        macro_rules! mk_harmless {
            () => {
                use m::f as g;
                macro_rules! helper { () => {} }
            };
        }

        mk_harmless!();

        proof fn test() {
            assert(g());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] item_macro_call_include_issue3154 verus_code! {
        include!("does_not_matter.rs");
    } => Err(err) => assert!(err.errors.iter().any(|e| e.message.contains("`include!` in item position is not supported inside `verus!`")))
}
