#![feature(concat_idents)]
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Run each test for both AtomicInvariant/open_atomic_invariant and LocalInvariant/open_local_invariant

macro_rules! test_both {
    ($name:ident $name2:ident $test:expr => $p:pat) => {
        test_verify_one_file! {
            #[test] $name $test => $p
        }

        test_verify_one_file! {
            #[test] $name2 ($test
                .replace("AtomicInvariant", "LocalInvariant")
                .replace("open_atomic_invariant", "open_local_invariant")) => $p
        }
    };
    ($name:ident $name2:ident $test:expr => $p:pat => $e:expr) => {
        test_verify_one_file! {
            #[test] $name $test => $p => $e
        }

        test_verify_one_file! {
            #[test] $name2 ($test
                .replace("AtomicInvariant", "LocalInvariant")
                .replace("open_atomic_invariant", "open_local_invariant")) => $p => $e
        }
    };
}

test_both! {
    basic_usage basic_usage_local code! {
        use vstd::invariant::*;

        pub fn X<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
            requires([
                i.inv(0)
            ]);
            open_atomic_invariant!(&i => inner => {
                #[verifier::proof] let x = 5;
                #[verifier::proof] let x = 6;
                inner = 0;
            });
        }
    } => Ok(())
}

test_both! {
    basic_usage2 basic_usage2_local code! {
        use vstd::invariant::*;

        pub fn X<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
            open_atomic_invariant!(&i => inner => {
            });
        }
    } => Ok(())
}

test_both! {
    inv_fail inv_fail_local code! {
        use vstd::invariant::*;
        pub fn X<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
            open_atomic_invariant!(&i => inner => {
                #[verifier::proof] let x = 5;
                #[verifier::proof] let x = 6;
                inner = 0;
            }); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_both! {
    nested_failure nested_failure_local code! {
        use vstd::invariant::*;
        pub fn nested<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
            requires([
                i.inv(0)
            ]);
            open_atomic_invariant!(&i => inner => { // FAILS
                open_atomic_invariant!(&i => inner2 => {
                    inner2 = 0;
                });
                inner = 0;
            });
        }
    } => Err(err) => assert_one_fails(err)
}

test_both! {
    nested_good nested_good_local verus_code! {
        use vstd::invariant::*;
        pub fn nested_good<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>, #[verifier::proof] j: AtomicInvariant<A, u8, B>)
            requires
                i.inv(0),
                j.inv(1),
                i.namespace() == 0,
                j.namespace() == 1,
        {
            open_atomic_invariant!(&i => inner => {
                proof { inner = 0u8; }
                open_atomic_invariant!(&j => inner => {
                    proof { inner = 1u8; }
                });
            });
        }
    } => Ok(())
}

test_both! {
    full_call_empty full_call_empty_local code! {
        use vstd::invariant::*;
        #[verifier::proof]
        pub fn callee_mask_empty() {
          opens_invariants_none(); // will not open any invariant
        }
        pub fn t1<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
          open_atomic_invariant!(&i => inner => {
            callee_mask_empty();
          });
        }
    } => Ok(())
}

test_both! {
    open_call_full open_call_full_local code! {
        use vstd::invariant::*;
        #[verifier::proof]
        pub fn callee_mask_full() {
          opens_invariants_any(); // can open any invariant
        }
        pub fn t2<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
          open_atomic_invariant!(&i => inner => { // FAILS
            callee_mask_full();
          });
        }
    } => Err(err) => assert_one_fails(err)
}

test_both! {
    empty_open empty_open_local code! {
        use vstd::invariant::*;
        #[verifier::proof]
        pub fn callee_mask_empty() {
          opens_invariants_none(); // will not open any invariant
        }
        pub fn t3<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
          opens_invariants_none();
          open_atomic_invariant!(&i => inner => { // FAILS
          });
        }
    } => Err(err) => assert_one_fails(err)
}

// mode stuff

test_both! {
    open_inv_in_spec open_inv_in_spec_local code! {
        use vstd::invariant::*;

        #[verifier::spec]
        pub fn open_inv_in_spec<A, B: InvariantPredicate<A, u8>>(i: AtomicInvariant<A, u8, B>) {
          open_atomic_invariant!(&i => inner => {
          });
        }
    } => Err(err) => assert_vir_error_msg(err, "Cannot open invariant in Spec mode")
}

test_both! {
    inv_header_in_spec inv_header_in_spec_local code! {
        use vstd::invariant::*;

        #[verifier::spec]
        pub fn inv_header_in_spec<A, B: InvariantPredicate<A, u8>>(i: AtomicInvariant<A, u8, B>) {
          opens_invariants_any();
        }
    } => Err(err) => assert_vir_error_msg(err, "invariants cannot be opened in spec functions")
}

test_both! {
    open_inv_in_proof open_inv_in_proof_local code! {
        use vstd::invariant::*;

        #[verifier::proof]
        pub fn open_inv_in_proof<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
          opens_invariants_any();
          open_atomic_invariant!(&i => inner => {
          });
        }
    } => Ok(())
}

test_both! {
    inv_cannot_be_exec inv_cannot_be_exec_local code! {
        use vstd::invariant::*;

        pub fn X<A, B: InvariantPredicate<A, u8>>(#[verifier::exec] i: AtomicInvariant<A, u8, B>) {
            open_atomic_invariant!(&i => inner => {
            });
        }

    } => Err(err) => assert_vir_error_msg(err, "Invariant must be Proof mode")
}

test_both! {
    inv_cannot_be_spec inv_cannot_be_spec_local code! {
        use vstd::invariant::*;

        pub fn X<A, B: InvariantPredicate<A, u8>>(#[verifier::spec] i: AtomicInvariant<A, u8, B>) {
            open_atomic_invariant!(&i => inner => {
            });
        }

    } => Err(err) => assert_vir_error_msg(err, "Invariant must be Proof mode")
}

// This test doesn't apply to LocalInvariant
test_verify_one_file! {
    #[test] exec_code_in_inv_block code! {
        use vstd::invariant::*;

        pub fn exec_fn() { }

        pub fn X<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
            open_atomic_invariant!(&i => inner => {
                exec_fn();
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "open_atomic_invariant cannot contain non-atomic operations")
}

/*
// TODO (erasure-todo)
// This needs to be ported to verus_code
test_both! {
    inv_lifetime inv_lifetime_local code! {
        use vstd::invariant::*;

        #[verifier::proof]
        fn throw_away<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
        }

        pub fn do_nothing<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
          requires([
            i.inv(0)
          ]);
          open_atomic_invariant!(&i => inner => {
            throw_away(i);
          });
        }
    } => Err(err) => assert_error_msg(err, "error[E0505]: cannot move out of `i` because it is borrowed")
}
*/

test_both! {
    return_early return_early_local code! {
        use vstd::invariant::*;

        pub fn blah<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
          open_atomic_invariant!(&i => inner => {
            return;
          });
        }
    } => Err(err) => assert_vir_error_msg(err, "invariant block might exit early")
}

test_both! {
    return_early_nested return_early_nested_local code! {
        use vstd::invariant::*;

        pub fn blah<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>, #[verifier::proof] j: AtomicInvariant<A, u8, B>) {
          open_atomic_invariant!(&i => inner => {
            open_atomic_invariant!(&j => inner => {
              return;
            });
          });
        }
    } => Err(err) => assert_vir_error_msg(err, "invariant block might exit early")
}

test_both! {
    break_early break_early_local code! {
        use vstd::invariant::*;

        pub fn blah<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
          let mut idx = 0;
          while idx < 5 {
            open_atomic_invariant!(&i => inner => {
              break;
            });
          }
        }
    } => Err(err) => assert_vir_error_msg(err, "invariant block might exit early")
}

test_both! {
    continue_early continue_early_local code! {
        use vstd::invariant::*;

        pub fn blah<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
          let mut idx = 0;
          while idx < 5 {
            open_atomic_invariant!(&i => inner => {
              break;
            });
          }
        }
    } => Err(err) => assert_vir_error_msg(err, "invariant block might exit early")
}

test_both! {
    return_early_proof return_early_proof_local code! {
        use vstd::invariant::*;

        #[verifier::proof]
        pub fn blah<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
          open_atomic_invariant!(&i => inner => {
            return;
          });
        }
    } => Err(err) => assert_vir_error_msg(err, "invariant block might exit early")
}

test_both! {
    break_early_proof break_early_proof_local code! {
        use vstd::invariant::*;

        #[verifier::proof]
        pub fn blah<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
          let mut idx = 0;
          while idx < 5 {
            open_atomic_invariant!(&i => inner => {
              break;
            });
          }
        }

    } => Err(err) => assert_vir_error_msg(err, "invariant block might exit early")
}

test_both! {
    continue_early_proof continue_early_proof_local code! {
        use vstd::invariant::*;

        #[verifier::proof]
        pub fn blah<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
          let mut idx = 0;
          while idx < 5 {
            open_atomic_invariant!(&i => inner => {
              break;
            });
          }
        }

    } => Err(err) => assert_vir_error_msg(err, "invariant block might exit early")
}

// Check that we can't open a AtomicInvariant with open_local_invariant and vice-versa

test_verify_one_file! {
    #[test] mixup1 code! {
        use vstd::invariant::*;

        pub fn X<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: LocalInvariant<A, u8, B>) {
            open_atomic_invariant!(&i => inner => {
            });
        }
    } => Err(err) => assert_error_msg(err, "mismatched types")
}

test_verify_one_file! {
    #[test] mixup2 code! {
        use vstd::invariant::*;

        pub fn X<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: AtomicInvariant<A, u8, B>) {
            open_local_invariant!(&i => inner => {
            });
        }
    } => Err(err) => assert_error_msg(err, "mismatched types")
}

test_verify_one_file! {
    #[test] nest_local_loop_local code! {
        use vstd::invariant::*;

        pub fn X<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: LocalInvariant<A, u8, B>, #[verifier::proof] j: LocalInvariant<A, u8, B>) {
            open_local_invariant!(&i => inner => { // FAILS
                let mut idx: u64 = 0;
                while idx < 5 {
                    open_local_invariant!(&j => jnner => {
                    });
                    idx = idx + 1;
                }
            });
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] never_terminate_in_invariant code! {
        use vstd::invariant::*;

        pub fn X<A, B: InvariantPredicate<A, u8>>(#[verifier::proof] i: LocalInvariant<A, u8, B>) {
            open_local_invariant!(&i => inner => {
                inner = 7;
                loop { }
            });
        }
    } => Ok(())
}
