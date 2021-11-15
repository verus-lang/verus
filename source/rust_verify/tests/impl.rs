#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const STRUCT: &str = code_str! {
    #[derive(PartialEq, Eq)]
    struct Bike {
        hard_tail: bool,
    }
};

test_verify_one_file! {
    #[test] test_impl_1 STRUCT.to_string() + code_str! {
        impl Bike {
            #[spec]
            pub fn is_hard_tail(&self) -> bool {
                self.hard_tail
            }
        }

        fn test_impl_1(b: Bike) {
            requires(b.is_hard_tail());
            assert(b.hard_tail);
        }

        fn test_impl_2(b: &Bike) {
            requires(b.is_hard_tail());
            assert(b.hard_tail);
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impl_mod_1 code! {
        mod M1 {
            #[derive(PartialEq, Eq)]
            pub struct Bike {
                pub hard_tail: bool,
            }

            impl Bike {
                #[spec]
                pub fn is_hard_tail(&self) -> bool {
                    self.hard_tail
                }
            }
        }

        mod M2 {
            use super::M1::Bike;
            use builtin::*;
            use crate::pervasive::*;

            fn test_impl_1(b: Bike) {
                requires(b.is_hard_tail());
                assert(b.is_hard_tail());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impl_mod_priv_field code! {
        mod M1 {
            #[derive(PartialEq, Eq)]
            pub struct Bike {
                hard_tail: bool,
            }

            impl Bike {
                #[spec]
                #[verifier(pub_abstract)]
                pub fn is_hard_tail(&self) -> bool {
                    self.hard_tail
                }
            }
        }

        mod M2 {
            use super::M1::Bike;
            use builtin::*;
            use crate::pervasive::*;

            fn test_impl_1(b: Bike) {
                requires(b.is_hard_tail());
                assert(b.is_hard_tail());
            }
        }
    } => Ok(())
}

const IMPL_GENERIC_SHARED: &str = code_str! {
    #[derive(PartialEq, Eq)]
    struct Wrapper<A> {
        v: A,
    }

    impl<A> Wrapper<A> {
        #[spec]
        pub fn take(self) -> A {
            self.v
        }
    }
};

test_verify_one_file! {
    #[test] test_impl_generic_pass IMPL_GENERIC_SHARED.to_string() + code_str! {
        #[proof]
        fn test_impl_1(a: int) {
            let w = Wrapper { v: a };
            assert(w.take() == a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impl_generic_fail IMPL_GENERIC_SHARED.to_string() + code_str! {
        #[proof]
        fn test_impl_1(a: int) {
            let w = Wrapper { v: a };
            assert(w.take() != a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
