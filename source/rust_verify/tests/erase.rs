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

test_verify_one_file! {
    #[test] test_regression_70 code! {
        fn m(v: &mut u64) { }

        fn main() {
            let v = 6;
            m(&mut v);
        }
    } => Err(e) => assert_eq!(e.errors.len(), 0)
}
