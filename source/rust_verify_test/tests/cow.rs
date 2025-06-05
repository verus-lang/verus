#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_cow_basic verus_code! {
        use vstd::*;
        use vstd::prelude::*;
        use vstd::std_specs::borrow::*;
        use std::borrow::Cow;

        #[derive(Copy, Clone)]
        pub struct NumWrapper { pub x: u64 }

        impl View for NumWrapper {
            type V = int;
            open spec fn view(&self) -> Self::V {
                self.x as int
            }
        }


        fn cow_struct(x: u64) {
            let as_cow: Cow<'_, NumWrapper> = Cow::Owned(NumWrapper { x });

            assert(as_cow@ == x as int);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_cow_str verus_code! {

        use vstd::*;
        use vstd::prelude::*;
        use vstd::std_specs::borrow::*;
        use std::borrow::Cow;
        fn cow_str() {
            proof! {
                reveal_strlit("abc");
            }
            let a = "abc";
            let c: Cow<'_, str> = Cow::Borrowed(a);

            assert(c@ == "abc"@);
        }
    } => Ok(())
}
