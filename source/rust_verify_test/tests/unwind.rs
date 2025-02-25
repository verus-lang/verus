#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] basic verus_code! {
        use vstd::prelude::*;
        use vstd::invariant::*;

        fn fn_may_unwind()
            opens_invariants none
        {
        }

        fn fn_no_unwind()
            opens_invariants none
            no_unwind
        {
        }

        fn fn_conditional_unwind(i: u8)
            opens_invariants none
            no_unwind when i >= 5
        {
        }

        fn test_caller_may_unwind() {
            fn_may_unwind();
            fn_no_unwind();
            fn_conditional_unwind(0);
            fn_conditional_unwind(20);
        }

        fn test_caller_no_unwind1()
            no_unwind
        {
            fn_may_unwind(); // FAILS
        }

        fn test_caller_no_unwind2()
            no_unwind
        {
            fn_conditional_unwind(3); // FAILS
        }

        fn test_caller_no_unwind3()
            no_unwind
        {
            fn_conditional_unwind(20);
            fn_no_unwind();
        }

        fn test_caller_conditional1(j: u8)
            no_unwind when j >= 10
        {
            fn_may_unwind(); // FAILS
        }

        fn test_caller_conditional2(j: u8)
            no_unwind when j >= 10
        {
            fn_no_unwind();
        }

        fn test_caller_conditional3(j: u8)
            no_unwind when j >= 10
        {
            fn_conditional_unwind(j);
        }

        fn test_caller_conditional4(j: u8)
            no_unwind when j >= 4
        {
            fn_conditional_unwind(j); // FAILS
        }

        fn call_from_invariant<A, B: InvariantPredicate<A, u8>>(Tracked(inv): Tracked<&LocalInvariant<A, u8, B>>) {
            open_local_invariant!(inv => inner => {
                fn_no_unwind();
            });
        }

        fn call_from_invariant2<A, B: InvariantPredicate<A, u8>>(Tracked(inv): Tracked<&LocalInvariant<A, u8, B>>) {
            open_local_invariant!(inv => inner => {
                fn_may_unwind(); // FAILS
            });
        }

        fn call_from_invariant3<A, B: InvariantPredicate<A, u8>>(Tracked(inv): Tracked<&LocalInvariant<A, u8, B>>) {
            open_local_invariant!(inv => inner => {
                fn_conditional_unwind(5);
            });
        }

        fn call_from_invariant4<A, B: InvariantPredicate<A, u8>>(Tracked(inv): Tracked<&LocalInvariant<A, u8, B>>) {
            open_local_invariant!(inv => inner => {
                fn_conditional_unwind(4); // FAILS
            });
        }

        fn call_from_invariant5<A, B: InvariantPredicate<A, u8>>(Tracked(inv): Tracked<&LocalInvariant<A, u8, B>>, k: u8)
            no_unwind when k >= 8
        {
            open_local_invariant!(inv => inner => {
                fn_conditional_unwind(k); // FAILS
            });
        }

        fn call_from_invariant6<A, B: InvariantPredicate<A, u8>>(Tracked(inv): Tracked<&LocalInvariant<A, u8, B>>, k: u8)
            no_unwind when k >= 8
        {
            loop {
                open_local_invariant!(inv => inner => {
                    fn_conditional_unwind(k); // FAILS
                });
            }
        }

        fn test_closure()
            no_unwind
        {
            let f = || {
                // This is fine since it's in the closure
                fn_may_unwind();
            };
        }

        fn test_closure2()
            no_unwind
        {
            let f = || {
            };

            // not fine, closures always unwind (for now)
            f(); // FAILS
        }
    } => Err(err) => assert_fails(err, 9)
}

test_verify_one_file! {
    #[test] call_trait_methods_generic verus_code! {
        use vstd::prelude::*;
        use vstd::invariant::*;

        trait Tr {
            fn fn_may_unwind();

            fn fn_no_unwind()
                no_unwind;

            fn fn_conditional_unwind(i: u8)
                no_unwind when i >= 5;
        }

        fn test_caller_may_unwind<T: Tr>() {
            T::fn_may_unwind();
            T::fn_no_unwind();
            T::fn_conditional_unwind(0);
            T::fn_conditional_unwind(20);
        }

        fn test_caller_no_unwind1<T: Tr>()
            no_unwind
        {
            T::fn_may_unwind(); // FAILS
        }

        fn test_caller_no_unwind2<T: Tr>()
            no_unwind
        {
            T::fn_conditional_unwind(3); // FAILS
        }

        fn test_caller_no_unwind3<T: Tr>()
            no_unwind
        {
            T::fn_conditional_unwind(20);
            T::fn_no_unwind();
        }

        fn test_caller_conditional1<T: Tr>(j: u8)
            no_unwind when j >= 10
        {
            T::fn_may_unwind(); // FAILS
        }

        fn test_caller_conditional2<T: Tr>(j: u8)
            no_unwind when j >= 10
        {
            T::fn_no_unwind();
        }

        fn test_caller_conditional3<T: Tr>(j: u8)
            no_unwind when j >= 10
        {
            T::fn_conditional_unwind(j);
        }

        fn test_caller_conditional4<T: Tr>(j: u8)
            no_unwind when j >= 4
        {
            T::fn_conditional_unwind(j); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] call_trait_methods_specific verus_code! {
        use vstd::prelude::*;
        use vstd::invariant::*;

        trait Tr {
            fn fn_may_unwind();

            fn fn_no_unwind()
                no_unwind;

            fn fn_conditional_unwind(i: u8)
                no_unwind when i >= 5;
        }

        struct Y { }

        impl Tr for Y {
            fn fn_may_unwind();
            fn fn_no_unwind();
            fn fn_conditional_unwind(i: u8);
        }

        fn test_caller_may_unwind<T: Tr>() {
            Y::fn_may_unwind();
            Y::fn_no_unwind();
            Y::fn_conditional_unwind(0);
            Y::fn_conditional_unwind(20);
        }

        fn test_caller_no_unwind1<T: Tr>()
            no_unwind
        {
            Y::fn_may_unwind(); // FAILS
        }

        fn test_caller_no_unwind2<T: Tr>()
            no_unwind
        {
            Y::fn_conditional_unwind(3); // FAILS
        }

        fn test_caller_no_unwind3<T: Tr>()
            no_unwind
        {
            Y::fn_conditional_unwind(20);
            Y::fn_no_unwind();
        }

        fn test_caller_conditional1<T: Tr>(j: u8)
            no_unwind when j >= 10
        {
            Y::fn_may_unwind(); // FAILS
        }

        fn test_caller_conditional2<T: Tr>(j: u8)
            no_unwind when j >= 10
        {
            Y::fn_no_unwind();
        }

        fn test_caller_conditional3<T: Tr>(j: u8)
            no_unwind when j >= 10
        {
            Y::fn_conditional_unwind(j);
        }

        fn test_caller_conditional4<T: Tr>(j: u8)
            no_unwind when j >= 4
        {
            Y::fn_conditional_unwind(j); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] call_from_trait_fns verus_code! {
        fn fn_may_unwind()
            opens_invariants none
        {
        }

        fn fn_no_unwind()
            opens_invariants none
            no_unwind
        {
        }

        fn fn_conditional_unwind(i: u8)
            opens_invariants none
            no_unwind when i >= 5
        {
        }

        trait Tr {
            fn tr_fn_may_unwind();

            fn tr_fn_no_unwind()
                no_unwind;

            fn tr_fn_conditional_unwind(i: u8)
                no_unwind when i >= 3;
        }

        struct Y { }

        impl Tr for Y {
            fn tr_fn_may_unwind() {
                fn_may_unwind();
            }

            fn tr_fn_no_unwind() {
                fn_may_unwind(); // FAILS
            }

            fn tr_fn_conditional_unwind(i: u8)
            {
                fn_conditional_unwind(i); // FAILS
            }
        }

        struct Z { }

        impl Tr for Z {
            fn tr_fn_may_unwind() {
                fn_may_unwind();
            }

            fn tr_fn_no_unwind() {
                fn_conditional_unwind(3); // FAILS
            }

            fn tr_fn_conditional_unwind(i: u8)
            {
                assume(i >= 9);
                fn_conditional_unwind(i);
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] apply_to_trait_fn verus_code! {
        trait Tr {
            fn stuff(j: u8)
                no_unwind;
        }

        struct X { }

        impl Tr for X {
            fn stuff(j: u8)
                no_unwind when j >= 4
            {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "trait method implementation cannot declare an unwind specification")
}

test_verify_one_file! {
    #[test] mode1 verus_code! {
        proof fn stuff(j: u8)
            no_unwind
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "an 'unwind' specification can only be given on exec functions")
}

test_verify_one_file! {
    #[test] mode2 verus_code! {
        spec fn stuff(j: u8)
            no_unwind
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "an 'unwind' specification can only be given on exec functions")
}

test_verify_one_file! {
    #[test] mode3 verus_code! {
        proof fn stuff(j: u8)
            no_unwind when j >= 3
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "an 'unwind' specification can only be given on exec functions")
}

test_verify_one_file! {
    #[test] mode4 verus_code! {
        fn some_exec_fn(j: u8) -> bool { true }

        fn stuff(j: u8)
            no_unwind when some_exec_fn(j)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `crate::some_exec_fn` with mode exec")
}

test_verify_one_file! {
    #[test] specs_on_external_body verus_code! {
        #[verifier::external_body]
        fn fn_may_unwind()
            opens_invariants none
        {
        }

        #[verifier::external_body]
        fn fn_no_unwind()
            opens_invariants none
            no_unwind
        {
        }

        #[verifier::external_body]
        fn fn_conditional_unwind(i: u8)
            opens_invariants none
            no_unwind when i >= 5
        {
        }

        fn test_caller_may_unwind() {
            fn_may_unwind();
            fn_no_unwind();
            fn_conditional_unwind(0);
            fn_conditional_unwind(20);
        }

        fn test_caller_no_unwind1()
            no_unwind
        {
            fn_may_unwind(); // FAILS
        }

        fn test_caller_no_unwind2()
            no_unwind
        {
            fn_conditional_unwind(3); // FAILS
        }

        fn test_caller_no_unwind3()
            no_unwind
        {
            fn_conditional_unwind(20);
            fn_no_unwind();
        }

        fn test_caller_conditional1(j: u8)
            no_unwind when j >= 10
        {
            fn_may_unwind(); // FAILS
        }

        fn test_caller_conditional2(j: u8)
            no_unwind when j >= 10
        {
            fn_no_unwind();
        }

        fn test_caller_conditional3(j: u8)
            no_unwind when j >= 10
        {
            fn_conditional_unwind(j);
        }

        fn test_caller_conditional4(j: u8)
            no_unwind when j >= 4
        {
            fn_conditional_unwind(j); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] specs_on_external_fn_specification verus_code! {
        #[verifier::external]
        fn fn_may_unwind() { }

        #[verifier::external]
        fn fn_no_unwind() { }

        #[verifier::external]
        fn fn_conditional_unwind(i: u8) { }

        #[verifier::external_fn_specification]
        fn ex_fn_may_unwind()
            opens_invariants none
        {
            fn_may_unwind()
        }

        #[verifier::external_fn_specification]
        fn ex_fn_no_unwind()
            opens_invariants none
            no_unwind
        {
            fn_no_unwind()
        }

        #[verifier::external_fn_specification]
        fn ex_fn_conditional_unwind(i: u8)
            opens_invariants none
            no_unwind when i >= 5
        {
            fn_conditional_unwind(i)
        }

        fn test_caller_may_unwind() {
            fn_may_unwind();
            fn_no_unwind();
            fn_conditional_unwind(0);
            fn_conditional_unwind(20);
        }

        fn test_caller_no_unwind1()
            no_unwind
        {
            fn_may_unwind(); // FAILS
        }

        fn test_caller_no_unwind2()
            no_unwind
        {
            fn_conditional_unwind(3); // FAILS
        }

        fn test_caller_no_unwind3()
            no_unwind
        {
            fn_conditional_unwind(20);
            fn_no_unwind();
        }

        fn test_caller_conditional1(j: u8)
            no_unwind when j >= 10
        {
            fn_may_unwind(); // FAILS
        }

        fn test_caller_conditional2(j: u8)
            no_unwind when j >= 10
        {
            fn_no_unwind();
        }

        fn test_caller_conditional3(j: u8)
            no_unwind when j >= 10
        {
            fn_conditional_unwind(j);
        }

        fn test_caller_conditional4(j: u8)
            no_unwind when j >= 4
        {
            fn_conditional_unwind(j); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] no_unwind_box_rc_arc_new verus_code! {
        use vstd::prelude::*;
        use std::rc::Rc;
        use std::sync::Arc;

        fn test_box()
            no_unwind
        {
            let b = Box::new(8); // FAILS
        }

        fn test_rc()
            no_unwind
        {
            let b = Rc::new(8); // FAILS
        }

        fn test_arc()
            no_unwind
        {
            let b = Arc::new(8); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}
