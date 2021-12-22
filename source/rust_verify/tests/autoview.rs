#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 code! {
        struct S {
        }

        struct V {
        }

        impl V {
            #[spec]
            fn mkint(self, _i: int) -> int {
                8
            }
        }

        impl S {
            #[proof]
            fn f(#[proof]&self, #[spec] x: int) {

            }

            #[verifier(autoview)]
            fn mkint(&self, _u: u64) -> u64 {
                7
            }

            #[spec]
            fn view(self) -> V {
                V {}
            }
        }

        fn test() {
            let s = S {};
            #[spec] let i: int = 10;
            s.f(s.mkint(i));
            assert(s.mkint(i) == s.mkint(i));
            #[spec] let x: u64 = s.mkint(10);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 code! {
        struct S {
        }

        struct V {
        }

        impl V {
            #[spec]
            fn mkint(self, _i: int) -> int {
                8
            }
        }

        impl S {
            #[verifier(autoview)]
            #[spec] // ERROR: autoview cannot be spec
            fn mkint(&self, _u: u64) -> u64 {
                7
            }

            #[spec]
            fn view(self) -> V {
                V {}
            }
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test1_fails2 code! {
        struct S {
        }

        struct V {
        }

        impl V {
            #[spec]
            fn mkint(self, _i: int) -> int {
                8
            }
        }

        impl S {
            #[verifier(autoview)]
            fn mkint(&self, _u: u64) -> u64 {
                7
            }

            #[spec]
            // ERROR: wrong signature for view
            fn view(self, foo: int) -> V {
                V {}
            }
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test1_fails3 code! {
        struct S {
        }

        struct V {
        }

        impl V {
            #[spec]
            fn mkint(self, _i: int) -> int {
                8
            }
        }

        impl S {
            #[verifier(autoview)]
            fn mkint(&self, _u: u64) -> u64 {
                7
            }

            // ERROR: view is missing
        }
    } => Err(_)
}
