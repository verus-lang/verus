#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] basic_usage code! {
        use crate::pervasive::invariants::*;

        pub fn X(#[proof] i: Invariant<u8>) {
            requires([
                i.inv(0)
            ]);
            open_invariant!(&i => inner => {
                #[proof] let x = 5;
                #[proof] let x = 6;
                inner = 0;
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] basic_usage2 code! {
        use crate::pervasive::invariants::*;

        pub fn X(#[proof] i: Invariant<u8>) {
            open_invariant!(&i => inner => {
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] inv_fail code! {
        use crate::pervasive::invariants::*;
        pub fn X(#[proof] i: Invariant<u8>) {
            open_invariant!(&i => inner => {
                #[proof] let x = 5;
                #[proof] let x = 6;
                inner = 0;
            }); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] nested_failure code! {
        use crate::pervasive::invariants::*;
        pub fn nested(#[proof] i: Invariant<u8>) {
            requires([
                i.inv(0)
            ]);
            open_invariant!(&i => inner => { // FAILS
                open_invariant!(&i => inner2 => {
                    inner2 = 0;
                });
                inner = 0;
            });
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] nested_good code! {
        use crate::pervasive::invariants::*;
        pub fn nested_good(#[proof] i: Invariant<u8>, #[proof] j: Invariant<u8>) {
            requires([
                i.inv(0),
                j.inv(1),
                i.namespace() == 0,
                j.namespace() == 1,
            ]);
            open_invariant!(&i => inner => {
                inner = 0;
                open_invariant!(&j => inner => {
                    inner = 1;
                });
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] full_call_empty code! {
        use crate::pervasive::invariants::*;
        #[proof]
        pub fn callee_mask_empty() {
          opens_invariants_none(); // will not open any invariant
        }
        pub fn t1(#[proof] i: Invariant<u8>) {
          open_invariant!(&i => inner => {
            callee_mask_empty();
          });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] open_call_full code! {
        use crate::pervasive::invariants::*;
        #[proof]
        pub fn callee_mask_full() {
          opens_invariants_any(); // can open any invariant
        }
        pub fn t2(#[proof] i: Invariant<u8>) {
          open_invariant!(&i => inner => { // FAILS
            callee_mask_full();
          });
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] empty_open code! {
        use crate::pervasive::invariants::*;
        #[proof]
        pub fn callee_mask_empty() {
          opens_invariants_none(); // will not open any invariant
        }
        pub fn t3(#[proof] i: Invariant<u8>) {
          opens_invariants_none();
          open_invariant!(&i => inner => { // FAILS
          });
        }
    } => Err(err) => assert_one_fails(err)
}

// mode stuff

test_verify_one_file! {
    #[test] open_inv_in_spec code! {
        use crate::pervasive::invariants::*;

        #[spec]
        pub fn open_inv_in_spec(i: Invariant<u8>) {
          open_invariant!(&i => inner => {
          });
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] inv_header_in_spec code! {
        use crate::pervasive::invariants::*;

        #[spec]
        pub fn inv_header_in_spec(i: Invariant<u8>) {
          opens_invariants_any();
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] open_inv_in_proof code! {
        use crate::pervasive::invariants::*;

        #[proof]
        pub fn open_inv_in_proof(#[proof] i: Invariant<u8>) {
          opens_invariants_any();
          open_invariant!(&i => inner => {
          });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] inv_cannot_be_exec code! {
        use crate::pervasive::invariants::*;

        pub fn X(#[exec] i: Invariant<u8>) {
            open_invariant!(&i => inner => {
            });
        }

    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] inv_cannot_be_spec code! {
        use crate::pervasive::invariants::*;

        pub fn X(#[spec] i: Invariant<u8>) {
            open_invariant!(&i => inner => {
            });
        }

    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] exec_code_in_inv_block code! {
        use crate::pervasive::invariants::*;

        pub fn exec_fn() { }

        pub fn X(#[proof] i: Invariant<u8>) {
            open_invariant!(&i => inner => {
                exec_fn();
            });
        }

    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] inv_lifetime code! {
        use crate::pervasive::invariants::*;

        #[proof]
        fn throw_away(#[proof] i: Invariant<u8>) {
        }

        pub fn do_nothing(#[proof] i: Invariant<u8>) {
          requires([
            i.inv(0)
          ]);
          open_invariant!(&i => inner => {
            throw_away(i);
          });
        }
    } => Err(_) => ()
}

test_verify_one_file! {
    #[test] return_early code! {
        use crate::pervasive::invariants::*;

        pub fn blah(#[proof] i: Invariant<u8>) {
          open_invariant!(&i => inner => {
            return;
          });
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] return_early_nested code! {
        use crate::pervasive::invariants::*;

        pub fn blah(#[proof] i: Invariant<u8>, #[proof] j: Invariant<u8>) {
          open_invariant!(&i => inner => {
            open_invariant!(&j => inner => {
              return;
            });
          });
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] break_early code! {
        use crate::pervasive::invariants::*;

        pub fn blah(#[proof] i: Invariant<u8>) {
          let mut idx = 0;
          while idx < 5 {
            open_invariant!(&i => inner => {
              break;
            });
          }
        }

    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] continue_early code! {
        use crate::pervasive::invariants::*;

        pub fn blah(#[proof] i: Invariant<u8>) {
          let mut idx = 0;
          while idx < 5 {
            open_invariant!(&i => inner => {
              break;
            });
          }
        }

    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] return_early_proof code! {
        use crate::pervasive::invariants::*;

        #[proof]
        pub fn blah(#[proof] i: Invariant<u8>) {
          open_invariant!(&i => inner => {
            return;
          });
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] break_early_proof code! {
        use crate::pervasive::invariants::*;

        #[proof]
        pub fn blah(#[proof] i: Invariant<u8>) {
          let mut idx = 0;
          while idx < 5 {
            open_invariant!(&i => inner => {
              break;
            });
          }
        }

    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] continue_early_proof code! {
        use crate::pervasive::invariants::*;

        #[proof]
        pub fn blah(#[proof] i: Invariant<u8>) {
          let mut idx = 0;
          while idx < 5 {
            open_invariant!(&i => inner => {
              break;
            });
          }
        }

    } => Err(err) => assert_vir_error(err)
}
