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
            #[verus::spec]
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
    } => Err(err) => assert_vir_error_msg(err, "public function ensures cannot refer to private items")
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
                #[verus::spec] #[verus::verifier(publish)]
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
                #[verus::spec]
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
        #[verus::spec]
        pub fn take(self) -> A {
            self.v
        }
    }
};

test_verify_one_file! {
    #[test] test_impl_generic_pass IMPL_GENERIC_SHARED.to_string() + code_str! {
        #[verus::proof]
        fn test_impl_1(a: int) {
            let w = Wrapper { v: a };
            assert(w.take() == a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impl_generic_fail IMPL_GENERIC_SHARED.to_string() + code_str! {
        #[verus::proof]
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
            #[verus::spec]
            pub fn take<B>(self, b: B) -> Two<A, B> {
                Two { a: self.v, b: b }
            }
        }

        #[verus::proof]
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
            #[verus::spec]
            fn id(self) -> Self {
                self
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ops_trait_impl verus_code! {
        #[derive(PartialEq, Eq)]
        ghost struct V {
            one: nat,
            two: nat,
        }

        impl V {
            spec fn get_one(self) -> nat {
                self.one
            }
        }

        impl V {
            spec fn spec_index(self, idx: int) -> nat {
                if idx == 0 {
                    self.one
                } else if idx == 1 {
                    self.two
                } else {
                    arbitrary()
                }
            }
        }

        impl std::ops::Index<int> for V {
            type Output = nat;

            // TODO: this index-via-ghost-struct feature is probably obsolete now;
            // we should consider removing it
            spec fn index(&self, idx: int) -> &nat {
                if idx == 0 {
                    &self.one
                } else if idx == 1 {
                    &self.two
                } else {
                    arbitrary()
                }
            }
        }

        // this actually uses spec_index, not index:
        fn test(v: V)
            requires
                v[0] == 3,
        {
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

            #[verus::spec]
            fn index(&self, idx: int) -> &nat {
                if idx == 0 {
                    &self.one
                } else {
                    arbitrary()
                }
            }
        }
    } => Err(err) => assert_error_msg(err, "error[E0308]: mismatched types")
}

test_verify_one_file! {
    #[test] test_illegal_trait_impl_2 code! {
        struct V {
        }

        impl std::ops::Index<usize> for V {
            type Output = bool;
            fn index(&self, #[verus::spec]idx: usize) -> &bool { &true }
        }
    } => Err(err) => assert_error_msg(err, "parameter must have mode exec")
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
    #[ignore] #[test] test_erased_assoc_type_param code! {
        struct Foo<V> {
            v: V
        }

        impl<V> Foo<V> {
            #[verus::verifier(returns(spec))]
            fn bar<F: Fn(V) -> bool>(#[verus::spec] f: F, #[verus::spec] v: V) -> bool {
                f.requires((v,))
            }

            #[verus::verifier(returns(spec))]
            fn bar2<F: Fn(V) -> bool>(self, #[verus::spec] f: F) -> bool {
                f.requires((self.v,))
            }
        }

        fn test() {
            #[verus::spec] let x: u64 = 0;
            let z = |y: u64| true;
            Foo::<u64>::bar(z, x);

            let f = Foo::<u64> { v: 17 };
            let w = |y: u64| true;
            #[verus::spec] let b = f.bar2(w);
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
