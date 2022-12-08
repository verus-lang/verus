#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const COMMON: &str = code_str! {
    use crate::pervasive::invariant::*;

    #[verifier(atomic)]
    #[verifier(external_body)]
    fn atomic_op() {
        opens_invariants_none();
    }

    #[verifier(external_body)]
    fn non_atomic_op() {
        opens_invariants_none();
    }

    #[verifier(external_body)]
    #[proof]
    fn proof_op() { }
};

test_verify_one_file! {
    #[test] one_atomic_ok
    COMMON.to_string() + code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(#[proof] i: AtomicInvariant<A, u8, B>) {
            open_atomic_invariant!(&i => inner => {
                atomic_op();
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] two_atomic_fail
    COMMON.to_string() + code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(#[proof] i: AtomicInvariant<A, u8, B>) {
            open_atomic_invariant!(&i => inner => {
                atomic_op();
                atomic_op();
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "open_atomic_invariant cannot contain more than 1 atomic operation")
}

test_verify_one_file! {
    #[test] non_atomic_fail
    COMMON.to_string() + code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(#[proof] i: AtomicInvariant<A, u8, B>) {
            open_atomic_invariant!(&i => inner => {
                non_atomic_op();
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "open_atomic_invariant cannot contain non-atomic operations")
}

test_verify_one_file! {
    #[test] if_ok
    COMMON.to_string() + code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(#[proof] i: AtomicInvariant<A, u8, B>, j: u64) {
            open_atomic_invariant!(&i => inner => {
                if j == 1 {
                    atomic_op();
                }
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] proof_call_ok
    COMMON.to_string() + code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(#[proof] i: AtomicInvariant<A, u8, B>, j: u64) {
            open_atomic_invariant!(&i => inner => {
                proof_op();
                atomic_op();
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assign_ok
    COMMON.to_string() + code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(#[proof] i: AtomicInvariant<A, u8, B>) -> u32 {
            let mut x: u32 = 5;
            open_atomic_invariant!(&i => inner => {
                atomic_op();
                x = 7;
            });
            x
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] loop_fail
    COMMON.to_string() + code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(#[proof] i: AtomicInvariant<A, u8, B>) -> u32 {
            let mut x: u32 = 5;
            open_atomic_invariant!(&i => inner => {
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
    COMMON.to_string() + code_str! {
        #[verifier(atomic)]
        fn untrusted_atomic_op_1() { }

        #[verifier(atomic)]
        fn untrusted_atomic_op_2() {
            atomic_op();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] untrusted_atomic_fail
    COMMON.to_string() + code_str! {
        #[verifier(atomic)]
        fn untrusted_atomic_op() {
            non_atomic_op();
        }

    } => Err(err) => assert_vir_error_msg(err, "atomic function cannot contain non-atomic operations")
}

test_verify_one_file! {
    #[test] untrusted_atomic_fail2
    COMMON.to_string() + code_str! {
        #[verifier(atomic)]
        fn untrusted_atomic_op() {
            atomic_op();
            atomic_op();
        }

    } => Err(err) => assert_vir_error_msg(err, "atomic function cannot contain more than 1 atomic operation")
}

test_verify_one_file! {
    #[test] nonatomic_everything_ok
    COMMON.to_string() + code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(#[proof] i: LocalInvariant<A, u8, B>) -> u32 {
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
    COMMON.to_string() + code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(#[proof] i: AtomicInvariant<A, u8, B>, #[proof] j: LocalInvariant<A, u8, B>) {
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
    COMMON.to_string() + code_str! {
        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(#[proof] i: AtomicInvariant<A, u8, B>, #[proof] j: LocalInvariant<A, u8, B>) {
            open_atomic_invariant!(&i => inner => {
                open_local_invariant!(&j => inner => {
                    atomic_op();
                    atomic_op();
                });
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "open_atomic_invariant cannot contain more than 1 atomic operation")
}
