#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const COMMON: &str = verus_code_str! {
    use vstd::invariant::*;

    verus!{

    #[verifier(atomic)] /* vattr */
    #[verifier(external_body)] /* vattr */
    fn atomic_op()
        opens_invariants none
        no_unwind
    {
    }

    #[verifier(external_body)] /* vattr */
    fn non_atomic_op()
        opens_invariants none
        no_unwind
    {
    }

    #[verifier(external_body)] /* vattr */
    proof fn proof_op() { }

    }
};

test_verify_one_file! {
    #[test] one_atomic_ok
    COMMON.to_string() + verus_code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(i: Tracked<AtomicInvariant<A, u8, B>>) {
            open_atomic_invariant!(i.borrow() => inner => {
                atomic_op();
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] two_atomic_fail
    COMMON.to_string() + verus_code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(i: Tracked<AtomicInvariant<A, u8, B>>) {
            open_atomic_invariant!(i.borrow() => inner => {
                atomic_op();
                atomic_op();
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "open_atomic_invariant cannot contain more than 1 atomic operation")
}

test_verify_one_file! {
    #[test] non_atomic_fail
    COMMON.to_string() + verus_code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(i: Tracked<AtomicInvariant<A, u8, B>>) {
            open_atomic_invariant!(i.borrow() => inner => {
                non_atomic_op();
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "open_atomic_invariant cannot contain non-atomic operations")
}

test_verify_one_file! {
    #[test] if_ok
    COMMON.to_string() + verus_code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(i: Tracked<AtomicInvariant<A, u8, B>>, j: u64) {
            open_atomic_invariant!(i.borrow() => inner => {
                if j == 1 {
                    atomic_op();
                }
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] proof_call_ok
    COMMON.to_string() + verus_code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(i: Tracked<AtomicInvariant<A, u8, B>>, j: u64) {
            open_atomic_invariant!(i.borrow() => inner => {
                proof {
                    proof_op();
                }
                atomic_op();
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assign_ok
    COMMON.to_string() + verus_code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(i: Tracked<AtomicInvariant<A, u8, B>>) -> u32 {
            #[allow(unused_assignments)]
            let mut x: u32 = 5;
            open_atomic_invariant!(i.borrow() => inner => {
                atomic_op();
                x = 7;
            });
            x
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] loop_fail
    COMMON.to_string() + verus_code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(i: Tracked<AtomicInvariant<A, u8, B>>) -> u32 {
            let mut x: u32 = 5;
            open_atomic_invariant!(i.borrow() => inner => {
                while x < 10 {
                    x = x + 1;
                }
            });
            x
        }
    } => Err(err) => assert_vir_error_msg(err, "open_atomic_invariant cannot contain an 'exec' loop")
}

test_verify_one_file! {
    #[test] untrusted_atomic_success
    COMMON.to_string() + verus_code_str! {
        #[verifier(atomic)] /* vattr */
        fn untrusted_atomic_op_1() { }

        #[verifier(atomic)] /* vattr */
        fn untrusted_atomic_op_2() {
            atomic_op();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] untrusted_atomic_fail
    COMMON.to_string() + verus_code_str! {
        #[verifier(atomic)] /* vattr */
        fn untrusted_atomic_op() {
            non_atomic_op();
        }

    } => Err(err) => assert_vir_error_msg(err, "atomic function cannot contain non-atomic operations")
}

test_verify_one_file! {
    #[test] untrusted_atomic_fail2
    COMMON.to_string() + verus_code_str! {
        #[verifier(atomic)] /* vattr */
        fn untrusted_atomic_op() {
            atomic_op();
            atomic_op();
        }

    } => Err(err) => assert_vir_error_msg(err, "atomic function cannot contain more than 1 atomic operation")
}

test_verify_one_file! {
    #[test] nonatomic_everything_ok
    COMMON.to_string() + verus_code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: LocalInvariant<A, u8, B>) -> u32 {
            let mut x: u32 = 5;
            open_local_invariant!(&i => inner => {
                atomic_op();
                atomic_op();
                atomic_op();
                non_atomic_op();
                non_atomic_op();
                while x < 10 {
                    x = x + 1;
                }
            });
            x
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] two_atomic_fail_nest1
    COMMON.to_string() + verus_code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>, #[verifier::proof] j: LocalInvariant<A, u8, B>) {
            open_local_invariant!(&j => inner => {
                open_atomic_invariant!(&i => inner => {
                    atomic_op();
                    atomic_op();
                });
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "open_atomic_invariant cannot contain more than 1 atomic operation")
}

test_verify_one_file! {
    #[test] two_atomic_fail_nest2
    COMMON.to_string() + verus_code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>, #[verifier::proof] j: LocalInvariant<A, u8, B>) {
            open_atomic_invariant!(&i => inner => {
                open_local_invariant!(&j => inner => {
                    atomic_op();
                    atomic_op();
                });
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "open_atomic_invariant cannot contain more than 1 atomic operation")
}

test_verify_one_file! {
    #[test] call_closure_from_inside_atomic
    COMMON.to_string() + &verus_code! {
        pub fn test_clos<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
            let t = || { };
            open_atomic_invariant!(&i => inner => {
                // this could fail for multiple reasons:
                // 1. t() could open i again
                // 2. t() is not atomic
                t();
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "open_atomic_invariant cannot contain non-atomic operations")
}

test_verify_one_file! {
    #[test] call_closure_from_inside_atomic2
    COMMON.to_string() + &verus_code! {
        #[verifier(atomic)] /* vattr */
        pub fn test_clos<F: Fn(u64) -> u64>(f: F) {
            f(5);
        }
    } => Err(err) => assert_vir_error_msg(err, "atomic function cannot contain non-atomic operations")
}

test_verify_one_file! {
    #[test] call_closure_from_inside_local
    COMMON.to_string() + &verus_code! {
        pub fn test_clos<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: LocalInvariant<A, u8, B>) {
            let t = || { };
            open_local_invariant!(&i => inner => { // FAILS
                // also fails because of unwinding
                t(); // FAILS
            });
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] call_closure_and_open_inv_inside
    COMMON.to_string() + &verus_code! {
        pub fn test_clos<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: LocalInvariant<A, u8, B>) {
            let t;
            open_local_invariant!(&i => inner => {
                t = || {
                    // this is okay even though it's nested because it's inside the
                    // closure. So the invariant mask gets check when we call t()
                    // below
                    open_local_invariant!(&i => inner => {
                    });
                };
            });

            t();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] call_closure_and_open_inv_inside_atomic
    COMMON.to_string() + &verus_code! {
        pub fn stuff() { }

        pub fn test_clos<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
            let t;
            open_atomic_invariant!(&i => inner => {
                t = || {
                    stuff();

                    // this is okay even though it's nested because it's inside the
                    // closure. So the invariant mask gets check when we call t()
                    // below
                    open_atomic_invariant!(&i => inner => {
                    });
                };
            });

            t();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] call_closure_and_open_inv_inside_atomic_fail
    COMMON.to_string() + &verus_code! {
        pub fn test_clos<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
            open_atomic_invariant!(&i => inner => {
                let t = || { };

                t();
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "open_atomic_invariant cannot contain non-atomic operations")
}

test_verify_one_file! {
    #[test] atomic_trait_disallowed_issue754 verus_code!{
        trait Tr {
            #[verifier(atomic)]
            fn stuff();
        }
    } => Err(err) => assert_vir_error_msg(err, "'atomic' not supported for trait functions")
}

test_verify_one_file! {
    #[test] atomic_trait_allowed2_issue754 verus_code!{
        trait Tr {
            fn stuff();
        }

        struct X { }

        impl Tr for X {
            #[verifier(atomic)]
            fn stuff();
        }
    } => Err(err) => assert_vir_error_msg(err, "'atomic' not supported for trait functions")
}

test_verify_one_file! {
    #[test] atomic_recursion1 verus_code!{
        #[verifier(atomic)]
        fn stuff() {
            stuff();
        }
    } => Err(err) => assert_vir_error_msg(err, "'atomic' cannot be used on a recursive function")
}

test_verify_one_file! {
    #[test] atomic_recursion2 verus_code!{
        #[verifier(atomic)]
        fn stuff1() {
            stuff2();
        }

        #[verifier(atomic)]
        fn stuff2() {
            stuff1();
        }
    } => Err(err) => assert_vir_error_msg(err, "'atomic' cannot be used on a recursive function")
}

test_verify_one_file! {
    #[test] open_atomic_invariant_in_proof
    COMMON.to_string() + verus_code_str! {
        pub proof fn do_nothing<A, B: InvariantPredicate<A, u8>>(tracked credit: OpenInvariantCredit, tracked i: &AtomicInvariant<A, u8, B>)
            opens_invariants any
        {
            open_atomic_invariant_in_proof!(credit => i => inner => {
                proof_op();
                proof_op();
            });
        }
        pub fn call_do_nothing<A, B: InvariantPredicate<A, u8>>(i: Tracked<&AtomicInvariant<A, u8, B>>) {
            let Tracked(credit) = create_open_invariant_credit();
            proof { do_nothing(credit, i.get()); }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] open_local_invariant_in_proof
    COMMON.to_string() + verus_code_str! {
        pub proof fn do_nothing<A, B: InvariantPredicate<A, u8>>(tracked credit: OpenInvariantCredit, tracked i: &LocalInvariant<A, u8, B>)
            opens_invariants any
        {
            open_local_invariant_in_proof!(credit => i => inner => {
                proof_op();
                proof_op();
            });
        }
        pub fn call_do_nothing<A, B: InvariantPredicate<A, u8>>(i: Tracked<&LocalInvariant<A, u8, B>>) {
            let Tracked(credit) = create_open_invariant_credit();
            proof { do_nothing(credit, i.get()); }
        }
    } => Ok(())
}
