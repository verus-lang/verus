#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_with_pervasive! {
    #[test] test1 code! {
        fn test1() {
            {
                let mut x = 5;
                x = 50;
            }
            let mut x = 6;
            x = 60;
            let x = 7;
            assert(x == 7);
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] test1_fails code! {
        fn test1() {
            {
                let mut x = 5;
                x = 50;
            }
            let mut x = 6;
            x = 60;
            let x = 7;
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    #[test] test2 code! {
        fn test1() {
            let mut x = 6;
            x = 60;
            let x = 7;
            {
                let mut x = 5;
                x = 50;
            }
            assert(x == 7);
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] test2_fails code! {
        fn test1() {
            let mut x = 6;
            x = 60;
            let x = 7;
            {
                let mut x = 5;
                x = 50;
            }
            assert(x == 7);
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    #[test] test3 code! {
        fn test1() {
            let mut x = 6;
            x = 60;
            let x = 7;
            let y = {
                let mut x = 5;
                x = 50;
                x
            };
            assert(x == 7);
            assert(y == 50);
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] test3_fails code! {
        fn test1() {
            let mut x = 6;
            x = 60;
            let x = 7;
            let y = {
                let mut x = 5;
                x = 50;
                x
            };
            assert(x == 7);
            assert(y == 50);
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    #[test] test4 code! {
        fn test1() {
            let mut x = 6;
            x = 60;
            let x = 7;
            let y = {
                let mut x = 5;
                x = {let x = x + 50; x + 50};
                x
            };
            assert(x == 7);
            assert(y == 105);
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] test4_fails code! {
        fn test1() {
            let mut x = 6;
            x = 60;
            let x = 7;
            let y = {
                let mut x = 5;
                x = {let x = x + 50; x + 50};
                x
            };
            assert(x == 7);
            assert(y == 105);
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_with_pervasive! {
    #[test] test5 code! {
        fn test1() {
            let mut x = 6;
            x = 60;
            let x = 7;
            let x = {
                let mut x = 5;
                x = {let x = x + 50; x + 50};
                x
            };
            assert(x == 105);
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] test5_fails code! {
        fn test1() {
            let mut x = 6;
            x = 60;
            let x = 7;
            let x = {
                let mut x = 5;
                x = {let x = x + 50; x + 50};
                x
            };
            assert(x == 105);
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
