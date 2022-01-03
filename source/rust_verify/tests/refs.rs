#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_ref_0 code! {
        fn test_ref_0(p: int) {
            requires(p == 12);
            let b: &int = &p;
            assert(*b == 12);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ref_1 code! {
        fn test_ref_1(p: &u64) {
            requires(*p == 12);
            let b: &u64 = p;
            assert(*b == 12);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_return_ref_0 code! {
        fn return_ref(p: &u64) -> &u64 {
            ensures(|r: &u64| r == p);
            p
        }

        fn test_ret() {
            let a = 2;
            let b = return_ref(&a);
            assert(*b == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    // TODO(utaal) support named lifetimes for immutable references
    #[ignore] #[test] test_return_ref_named_lifetime code! {
        fn return_ref<'a>(p: &'a u64) -> &'a u64 {
            ensures(|r: &u64| r == p);
            p
        }
    } => Ok(())
}
