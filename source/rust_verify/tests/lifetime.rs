#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 code! {
        #[proof]
        fn consume<A>(#[proof] a: A) {
        }

        #[proof]
        fn test1<A>(#[proof] a: A) {
            consume(a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fail code! {
        #[proof]
        fn consume<A>(#[proof] a: A) {
        }

        #[proof]
        fn test1<A>(#[proof] a: A) {
            consume(a);
            consume(a);
        }
    } => Err(_) => ()
}
