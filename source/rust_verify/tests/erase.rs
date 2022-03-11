#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_regression_78 code! {
        use pervasive::modes::*;
        use pervasive::option::*;

        fn f1<T>(t: Spec<Option<T>>) {
            #[spec] let x = t.value().get_Some_0();
        }

        #[spec]
        fn f2() -> bool {
            let x: Option<usize> = Option::None;
            x.is_None()
        }
    } => Ok(())
}
