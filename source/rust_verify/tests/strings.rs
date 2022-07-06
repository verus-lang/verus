#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;


test_verify_one_file! {
    #[test] test_strings_1 code! {
        use pervasive::string::*;

        fn string_enc(a: String) {
        }

        fn str_enc(a: StrSlice) {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_string_literal verus_code! {
        use pervasive::string::*;

        fn string_lit() {
            let a: StrSlice<'_> = StrSlice::new("strlit1");
            let b: StrSlice<'_> = StrSlice::new("strlit2");

            assert(a === b);
        }
    } => Ok(())
}
