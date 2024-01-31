#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_387_discussioncomment_6202136 verus_code! {
        fn bar(v: Vec<u8>) {
            let bytes: &[u8] = &v[3 as usize .. 9 as usize];
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].rendered.contains("Range"));
    }
}
