#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const COMMON: &str = code_str! {
    use crate::pervasive::invariants::*;

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
        pub fn do_nothing(#[proof] i: Invariant<u8>) {
            open_invariant!(&i => inner => {
                atomic_op();
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] two_atomic_fail
    COMMON.to_string() + code_str! {
        pub fn do_nothing(#[proof] i: Invariant<u8>) {
            open_invariant!(&i => inner => {
                atomic_op();
                atomic_op();
            });
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] non_atomic_fail
    COMMON.to_string() + code_str! {
        pub fn do_nothing(#[proof] i: Invariant<u8>) {
            open_invariant!(&i => inner => {
                non_atomic_op();
            });
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] if_ok
    COMMON.to_string() + code_str! {
        pub fn do_nothing(#[proof] i: Invariant<u8>, j: u64) {
            open_invariant!(&i => inner => {
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
        pub fn do_nothing(#[proof] i: Invariant<u8>, j: u64) {
            open_invariant!(&i => inner => {
                proof_op();
                atomic_op();
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assign_ok
    COMMON.to_string() + code_str! {
        pub fn do_nothing(#[proof] i: Invariant<u8>) -> u32 {
            let mut x: u32 = 5;
            open_invariant!(&i => inner => {
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
        pub fn do_nothing(#[proof] i: Invariant<u8>) -> u32 {
            let mut x: u32 = 5;
            open_invariant!(&i => inner => {
                while x < 10 {
                    x = x + 1;
                }
            });
            x
        }
    } => Err(err) => assert_vir_error(err)
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

    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] untrusted_atomic_fail2
    COMMON.to_string() + code_str! {
        #[verifier(atomic)]
        fn untrusted_atomic_op() {
            atomic_op();
            atomic_op();
        }

    } => Err(err) => assert_vir_error(err)
}
