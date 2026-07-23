#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_char_is_whitespace verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = ' '.is_whitespace();
            assert(a);
            let b = '\u{3000}'.is_whitespace(); // IDEOGRAPHIC SPACE
            assert(b);
            let c = 'a'.is_whitespace();
            assert(!c);
            let d = '\u{2010}'.is_whitespace(); // HYPHEN, not whitespace
            assert(!d);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_whitespace_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'a'.is_whitespace();
            assert(a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
