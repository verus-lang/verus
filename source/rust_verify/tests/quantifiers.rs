#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        spec fn tr(i: int) -> bool {
            true
        }

        proof fn test1() {
            assert(tr(300));
            assert(exists|i: nat| i >= 0 && tr(i));
        }

        proof fn test1_inference() {
            assert(tr(300));
            assert(exists|i| i >= 0 && tr(i));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails verus_code! {
        spec fn tr(i: int) -> bool {
            true
        }

        proof fn test1() {
            assert(exists|i: nat| i >= 0 && tr(i)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2 verus_code! {
        spec fn tr1(i: int) -> bool {
            true
        }

        spec fn tr2(i: int) -> bool {
            true
        }

        proof fn test1() {
            assert(tr1(300));
            assert(exists|i: nat| i >= 0 && tr1(i) && tr2(i));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3 verus_code! {
        spec fn tr1(i: int) -> bool {
            true
        }

        spec fn tr2(i: int) -> bool {
            true
        }

        proof fn test1() {
            assert(tr2(300));
            assert(exists|i: nat| i >= 0 && tr1(i) && tr2(i));
        }
    } => Ok(())
}

////

test_verify_one_file! {
    #[test] test1g verus_code! {
        spec fn tr<A>(a: A) -> bool {
            true
        }

        proof fn test1() {
            assert(tr::<nat>(300));
            assert(exists|i: nat| i >= 0 && tr(i));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1g_fails verus_code! {
        spec fn tr<A>(a: A) -> bool {
            true
        }

        proof fn test1() {
            assert(exists|i: nat| i >= 0 && tr(i)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2g verus_code! {
        spec fn tr1<A>(a: A) -> bool {
            true
        }

        spec fn tr2<A>(a: A) -> bool {
            true
        }

        proof fn test1() {
            assert(tr1::<nat>(300));
            assert(exists|i: nat| i >= 0 && tr1(i) && tr2(i));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3g verus_code! {
        spec fn tr1<A>(a: A) -> bool {
            true
        }

        spec fn tr2<A>(a: A) -> bool {
            true
        }

        proof fn test1() {
            assert(tr2::<nat>(300));
            assert(exists|i: nat| i >= 0 && tr1(i) && tr2(i));
        }
    } => Ok(())
}

////

test_verify_one_file! {
    #[test] test4 verus_code! {
        spec fn tr1(i: int) -> bool {
            true
        }

        spec fn tr2(i: int) -> bool {
            true
        }

        proof fn test1() {
            assert(tr2(300));
            assert(exists|i: nat| i >= 0 && tr1(i) && #[trigger] tr2(i));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test4_fails verus_code! {
        spec fn tr1(i: int) -> bool {
            true
        }

        spec fn tr2(i: int) -> bool {
            true
        }

        proof fn test1() {
            assert(tr1(300));
            assert(exists|i: nat| i >= 0 && tr1(i) && #[trigger] tr2(i)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
