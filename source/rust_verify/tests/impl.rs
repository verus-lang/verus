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
    #[test] test_impl_no_self STRUCT.to_string() + code_str! {
        impl Bike {
            fn new() -> Bike {
                ensures(|result: Bike| result.hard_tail);
                Bike { hard_tail: true }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impl_no_self_fail_pub_private STRUCT.to_string() + code_str! {
        impl Bike {
            pub fn new() -> Bike {
                ensures(|result: Bike| result.hard_tail);
                Bike { hard_tail: true }
            }
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_impl_mod_1 code! {
        mod M1 {
            use builtin::*;

            #[derive(PartialEq, Eq)]
            pub struct Bike {
                pub hard_tail: bool,
            }

            impl Bike {
                #[spec] #[verifier(publish)]
                pub fn is_hard_tail(&self) -> bool {
                    self.hard_tail
                }

                pub fn new() -> Bike {
                    ensures(|result: Bike| result.hard_tail);
                    Bike { hard_tail: true }
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

            fn test_impl_2() {
                let b = Bike::new();
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

test_verify_one_file! {
    #[test] test_generic_struct code! {
        #[derive(PartialEq, Eq)]
        struct TemplateCar<V> {
            four_doors: bool,
            passengers: u64,
            the_v: V,
        }

        impl<V> TemplateCar<V> {
            fn template_new(v: V) -> TemplateCar<V> {
                ensures(|result: TemplateCar<V>|
                  equal(result.passengers, 205) && equal(result.the_v, v)
                );
                TemplateCar::<V> { four_doors: false, passengers: 205, the_v: v }
            }

            fn template_get_passengers(&self) -> u64 {
                ensures(|result: u64| result == self.passengers);
                self.passengers
            }

            fn template_get_v(self) -> V {
                ensures(|result: V| equal(result, self.the_v));
                self.the_v
            }
        }

        fn test1() {
            let c3 = TemplateCar::<u64>::template_new(5);
            let p3 = c3.template_get_passengers();
            assert(p3 == 205);
            let v = c3.template_get_v();
            assert(v == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_erased_assoc_type_param code! {
        struct Foo<V> {
            v: V
        }

        impl<V> Foo<V> {
            #[verifier(returns(spec))]
            fn bar<F: Fn(V) -> bool>(#[spec] f: F, #[spec] v: V) -> bool {
                f(v)
            }

            #[verifier(returns(spec))]
            fn bar2<F: Fn(V) -> bool>(self, #[spec] f: F) -> bool {
                f(self.v)
            }
        }

        fn test() {
            #[spec] let x: u64 = 0;
            Foo::<u64>::bar(|y: u64| true, x);

            let f = Foo::<u64> { v: 17 };
            #[spec] let b = f.bar2(|y: u64| true);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_resolve_self_ty code! {
        struct Foo<V> {
          x: V,
        }

        impl<V> Foo<V> {
            fn bar(self) -> Self {
                ensures(|s: Self| equal(self, s));

                self
            }

            fn bar2(self) -> Self {
                ensures(|s: Self| equal(self, s));

                Self::bar(self)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] unsafe_impl_fail code! {
        struct Foo {
            x: u32,
        }

        unsafe impl Send for Foo { }
    } => Err(e) => assert_vir_error_msg(e, "the verifier does not support `unsafe` here")
}
