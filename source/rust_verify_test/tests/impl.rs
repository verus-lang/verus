#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const STRUCT: &str = verus_code_str! {
    #[derive(PartialEq, Eq)]
    struct Bike {
        hard_tail: bool,
    }
};

test_verify_one_file! {
    #[test] test_impl_1 STRUCT.to_string() + verus_code_str! {
        impl Bike {
            pub closed spec fn is_hard_tail(&self) -> bool {
                self.hard_tail
            }
        }

        fn test_impl_1(b: Bike)
            requires b.is_hard_tail()
        {
            assert(b.hard_tail);
        }

        fn test_impl_2(b: &Bike)
            requires b.is_hard_tail()
        {
            assert(b.hard_tail);
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impl_no_self STRUCT.to_string() + verus_code_str! {
        impl Bike {
            fn new() -> Bike {
                ensures(|result: Bike| result.hard_tail);
                Bike { hard_tail: true }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impl_no_self_fail_pub_private STRUCT.to_string() + verus_code_str! {
        impl Bike {
            pub fn new() -> Bike {
                ensures(|result: Bike| result.hard_tail);
                Bike { hard_tail: true }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "in 'ensures' clause of public function, cannot access any field of a datatype where one or more fields are private")
}

test_verify_one_file! {
    #[test] test_impl_mod_1 verus_code! {
        mod M1 {
            use builtin::*;

            #[derive(PartialEq, Eq)]
            pub struct Bike {
                pub hard_tail: bool,
            }

            impl Bike {
                pub open spec fn is_hard_tail(&self) -> bool {
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

            fn test_impl_1(b: Bike)
                requires b.is_hard_tail()
            {
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
    #[test] test_impl_mod_priv_field verus_code! {
        mod M1 {
            #[derive(PartialEq, Eq)]
            pub struct Bike {
                hard_tail: bool,
            }

            impl Bike {
                pub closed spec fn is_hard_tail(&self) -> bool {
                    self.hard_tail
                }
            }
        }

        mod M2 {
            use super::M1::Bike;
            use builtin::*;

            fn test_impl_1(b: Bike)
                requires b.is_hard_tail()
            {
                assert(b.is_hard_tail());
            }
        }
    } => Ok(())
}

const IMPL_GENERIC_SHARED: &str = verus_code_str! {
    #[derive(PartialEq, Eq)]
    struct Wrapper<A> {
        v: A,
    }

    impl<A> Wrapper<A> {
        pub closed spec fn take(self) -> A {
            self.v
        }
    }
};

test_verify_one_file! {
    #[test] test_impl_generic_pass IMPL_GENERIC_SHARED.to_string() + verus_code_str! {
        proof fn test_impl_1(a: int) {
            let w = Wrapper { v: a };
            assert(w.take() == a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impl_generic_fail IMPL_GENERIC_SHARED.to_string() + verus_code_str! {
        proof fn test_impl_1(a: int) {
            let w = Wrapper { v: a };
            assert(w.take() != a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_impl_generic_param verus_code! {
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
            pub closed spec fn take<B>(self, b: B) -> Two<A, B> {
                Two { a: self.v, b: b }
            }
        }

        proof fn test_impl_1(a: int) {
            let w = Wrapper { v: a };
            assert(w.take(12i32) == Two { a: a, b: 12i32 });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impl_with_self verus_code! {
        #[derive(PartialEq, Eq, Structural)]
        struct Bike {
            hard_tail: bool,
        }

        impl Bike {
            spec fn id(self) -> Self {
                self
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_illegal_trait_impl verus_code! {
        #[derive(PartialEq, Eq)]
        struct V {
            one: nat,
        }

        impl std::ops::Index<int> for V {
            type Output = nat;

            open spec fn index(&self, idx: int) -> &nat {
                if idx == 0 {
                    &self.one
                } else {
                    vstd::pervasive::arbitrary()
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "function for external trait must have mode 'exec'")
}

test_verify_one_file! {
    #[test] test_illegal_trait_impl_2 verus_code! {
        struct V {
        }

        impl std::ops::Index<usize> for V {
            type Output = bool;
            fn index(&self, #[verifier::spec]idx: usize) -> &bool { &true }
        }
    } => Err(err) => assert_vir_error_msg(err, "function for external trait must have all parameters have mode 'exec'")
}

test_verify_one_file! {
    #[test] test_generic_struct verus_code! {
        #[derive(PartialEq, Eq)]
        struct TemplateCar<V> {
            four_doors: bool,
            passengers: u64,
            the_v: V,
        }

        impl<V> TemplateCar<V> {
            fn template_new(v: V) -> (result: TemplateCar<V>)
                ensures
                    equal(result.passengers, 205),
                    equal(result.the_v, v),
            {
                TemplateCar::<V> { four_doors: false, passengers: 205, the_v: v }
            }

            fn template_get_passengers(&self) -> (result: u64)
                ensures result == self.passengers
            {
                self.passengers
            }

            fn template_get_v(self) -> (result: V)
                ensures equal(result, self.the_v)
            {
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
    #[ignore] #[test] test_erased_assoc_type_param verus_code! {
        struct Foo<V> {
            v: V
        }

        impl<V> Foo<V> {
            fn bar<F: Fn(V) -> bool>(f: Ghost<F>, v: Ghost<V>) -> Ghost<bool> {
                Ghost(f.requires((v,)))
            }

            fn bar2<F: Fn(V) -> bool>(self, f: Ghost<F>) -> Ghost<bool> {
                Ghost(f.requires((self.v,)))
            }
        }

        fn test() {
            let x: Ghost<u64> = Ghost(0u64);
            let z = |y: u64| true;
            Foo::<u64>::bar(Ghost(z), x);

            let f = Foo::<u64> { v: 17 };
            let w = |y: u64| true;
            let b: Ghost<bool> = f.bar2(Ghost(w));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_resolve_self_ty verus_code! {
        struct Foo<V> {
          x: V,
        }

        impl<V> Foo<V> {
            fn bar(self) -> (s: Self)
                ensures equal(self, s)
            {
                self
            }

            fn bar2(self) -> (s: Self)
                ensures equal(self, s)
            {
                Self::bar(self)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] unsafe_impl_fail verus_code! {
        struct Foo {
            x: u32,
        }

        unsafe impl Send for Foo { }
    } => Err(e) => assert_vir_error_msg(e, "the verifier does not support `unsafe` here")
}
