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
        const GREETING: StrSlice<'static> = StrSlice::new("Hello World");
        fn string_lit() {
            GREETING.reveal();
        }
    } => Ok(())
}
