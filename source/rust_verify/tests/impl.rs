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

test_verify_one_file! {
    #[test] test_impl_generic_param code! {
        #[derive(PartialEq, Eq, Structural)]
        struct Two<A, B> {
            a: A,
            b: B,
        }

        #[derive(PartialEq, Eq)]
        struct Wrapper<A> {
            v: A,
        }

        impl<A> Wrapper<A> {
            #[spec]
            pub fn take<B>(self, b: B) -> Two<A, B> {
                Two { a: self.v, b: b }
            }
        }

        #[proof]
        fn test_impl_1(a: int) {
            let w = Wrapper { v: a };
            assert(w.take(12) == Two { a: a, b: 12 });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impl_with_self code! {
        #[derive(PartialEq, Eq, Structural)]
        struct Bike {
            hard_tail: bool,
        }

        impl Bike {
            #[spec]
            fn id(self) -> Self {
                self
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ops_trait_impl code! {
        #[derive(PartialEq, Eq)] #[spec]
        struct V {
            one: nat,
            two: nat,
        }

        impl V {
            #[spec]
            fn get_one(self) -> nat {
                self.one
            }
        }

        impl std::ops::Index<int> for V {
            type Output = nat;

            #[spec]
            fn index(&self, idx: int) -> &nat {
                if idx == 0 {
                    &self.one
                } else if idx == 1 {
                    &self.two
                } else {
                    arbitrary()
                }
            }
        }

        fn test(v: V) {
            requires(v[0] == 3);

            assert(v[0] + 1 == 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_illegal_trait_impl code! {
        #[derive(PartialEq, Eq)]
        struct V {
            one: nat,
        }

        impl std::ops::Index<int> for V {
            type Output = nat;

            #[spec]
            fn index(&self, idx: int) -> &nat {
                if idx == 0 {
                    &self.one
                } else {
                    arbitrary()
                }
            }
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test_illegal_trait_impl_2 code! {
        struct V {
        }

        impl std::ops::Index<usize> for V {
            type Output = bool;
            fn index(&self, #[spec]idx: usize) -> &bool { &true }
        }
    } => Err(_)
}
