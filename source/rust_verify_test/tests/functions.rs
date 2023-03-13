#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_use_fun_ext verus_code! {
        use vstd::function::*;

        proof fn test_use_fun_ext(f: FnSpec(int) -> int) {
          fun_ext::<int, int>(|i: int| i + 1, |i: int| 1 + i);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_use_fun_ext2 verus_code! {
        use vstd::function::*;

        spec fn drop<A>(f: FnSpec(int) -> A, k: nat) -> FnSpec(int) -> A {
          |n: int| f(n + k)
        }

        /// prove a rule for simplifying drop(drop(f, ...))
        proof fn test_use_fun_ext2<A>(f: FnSpec(int) -> A, k1: nat, k2: nat)
          ensures drop(drop(f, k1), k2) === drop(f, k1 + k2) {
          fun_ext::<int, A>(drop(drop(f, k1), k2), drop(f, k1 + k2));
        }
    } => Ok(())
}
