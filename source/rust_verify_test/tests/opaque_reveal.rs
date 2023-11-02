#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const COMMON_TRAIT_AND_TYPE: &str = verus_code_str! {
    trait Tr {
        spec fn afunction(&self) -> bool;
    }

    struct A { }

    impl Tr for A {
        spec fn afunction(&self) -> bool { true }
    }
};

test_verify_one_file! {
    #[test] trait_fn_free_fn_nogeneric COMMON_TRAIT_AND_TYPE.to_string() + verus_code_str! {
        fn some_fn_nogeneric(a: A) {
            hide(<A as Tr>::afunction);
            reveal(<A as Tr>::afunction);
            assert(a.afunction());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_fn_inherent_fn_nogeneric COMMON_TRAIT_AND_TYPE.to_string() + verus_code_str! {
        impl A {
            fn some_fn_nogeneric(&self) {
                hide(<A as Tr>::afunction);
                reveal(<A as Tr>::afunction);
                assert(self.afunction());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_fn_inherent_fn_self_nogeneric COMMON_TRAIT_AND_TYPE.to_string() + verus_code_str! {
        impl A {
            fn some_fn_nogeneric(&self) {
                reveal(<Self as Tr>::afunction);
                assert(self.afunction());
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Self is not supported in reveal/hide")
}

test_verify_one_file! {
    #[test] trait_fn_trait_fn_nogeneric verus_code! {
        trait Tr {
            spec fn afunction(&self) -> bool;
            proof fn aproof(&self);
        }

        struct A { }

        impl Tr for A {
            #[verifier::opaque]
            spec fn afunction(&self) -> bool { true }

            proof fn aproof(&self) {
                reveal(<A as Tr>::afunction);
                assert(self.afunction());
            }
        }
    } => Ok(())
}

const COMMON_TRAIT_AND_TYPE_WITH_GENERIC: &str = verus_code_str! {
    trait Tr<T> {
        spec fn afunction(&self) -> bool;
    }

    struct A<T> {
        t: T,
    }

    impl<T> Tr<T> for A<T> {
        spec fn afunction(&self) -> bool { true }
    }
};

test_verify_one_file! {
    #[test] trait_fn_free_fn_generic_1 COMMON_TRAIT_AND_TYPE_WITH_GENERIC.to_string() + verus_code_str! {
        fn some_fn_generic<T>(a: A<T>) {
            hide(<A<_> as Tr<_>>::afunction);
            reveal(<A<_> as Tr<_>>::afunction);
            assert(a.afunction());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_fn_free_fn_generic_2 COMMON_TRAIT_AND_TYPE_WITH_GENERIC.to_string() + verus_code_str! {
        fn some_fn_generic<T>(a: A<T>) {
            hide(<A as Tr>::afunction);
            reveal(<A as Tr>::afunction);
            assert(a.afunction());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_fn_inherent_fn_generic COMMON_TRAIT_AND_TYPE_WITH_GENERIC.to_string() + verus_code_str! {
        impl<T> A<T> {
            fn some_fn_generic(&self) {
                hide(<A as Tr>::afunction);
                reveal(<A as Tr>::afunction);
                assert(self.afunction());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_fn_inherent_fn_self_generic COMMON_TRAIT_AND_TYPE_WITH_GENERIC.to_string() + verus_code_str! {
        impl<T> A<T> {
            fn some_fn_generic(&self) {
                reveal(<Self as Tr>::afunction);
                assert(self.afunction());
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Self is not supported in reveal/hide")
}

test_verify_one_file! {
    #[test] trait_fn_trait_fn_generic verus_code! {
        trait Tr {
            spec fn afunction(&self) -> bool;
            proof fn aproof(&self);
        }

        struct A { }

        impl Tr for A {
            #[verifier::opaque]
            spec fn afunction(&self) -> bool { true }

            proof fn aproof(&self) {
                reveal(<A as Tr>::afunction);
                assert(self.afunction());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_fn_free_fn_expanded_invalid_1 COMMON_TRAIT_AND_TYPE_WITH_GENERIC.to_string() + code_str! {
        #[verus::internal(verus_macro)]
        fn some_fn_generic<T>(a: A<T>) {
            #[verifier::proof_block]
            {
                ::builtin::reveal_hide_({
                        #[verus::internal(reveal_fn)]
                        fn __VERUS_REVEAL_INTERNAL__() {
                            let a = ();

                            ::builtin::reveal_hide_internal_path_(<A<_> as Tr<_>>::afunction)
                        }
                        __VERUS_REVEAL_INTERNAL__
                    }, 1)
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "invalid reveal/hide")
}

const STRUCT_AND_INHERENT_FN: &str = verus_code_str! {
    struct A<T> {
        t: T,
    }

    impl<T> A<T> {
        #[verifier::opaque]
        spec fn afunction(&self) -> bool { true }
    }
};

test_verify_one_file! {
    #[test] struct_fn_free_fn_1 STRUCT_AND_INHERENT_FN.to_string() + verus_code_str! {
        fn aproof(a: A<u64>) {
            reveal(A::<_>::afunction);
            assert(a.afunction());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] struct_fn_free_fn_2 STRUCT_AND_INHERENT_FN.to_string() + verus_code_str! {
        fn aproof(a: A<u64>) {
            reveal(A::afunction);
            assert(a.afunction());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] struct_fn_free_fn_3_incorrect_type STRUCT_AND_INHERENT_FN.to_string() + verus_code_str! {
        fn aproof(a: A<u64>) {
            reveal(A::<usize>::afunction); // produces a warning
            assert(a.afunction());
        }
    } => Ok(err) => {
        assert!(err.warnings.iter().find(|x| x.message.contains("in hide/reveal, type arguments are ignored")).is_some());
    }
}

test_verify_one_file! {
    #[test] mod_invalid_1 verus_code! {
        mod m1 {}

        fn aproof(a: nat) {
            reveal(m1);
        }
    } => Err(err) => assert_rust_error_msg(err, "expected value, found module")
}

test_verify_one_file! {
    #[test] struct_fn_free_fn_4_not_found STRUCT_AND_INHERENT_FN.to_string() + verus_code_str! {
        fn aproof(a: A<u64>) {
            reveal(A::wrong);
            assert(a.afunction());
        }
    } => Err(err) => assert_vir_error_msg(err, "`wrong` not found")
}

test_verify_one_file! {
    #[test] across_modules_and_use verus_code! {
        mod m1 {
            pub struct A<T> {
                t: T,
            }

            impl<T> A<T> {
                #[verifier::opaque]
                pub open spec fn afunction(&self) -> bool { true }
            }

            #[verifier::opaque]
            pub open spec fn bfunction() -> bool { true }
        }

        mod m2 {
            use crate::m1::*;
            fn aproof(a: A<u64>) {
                reveal(A::afunction);
                assert(a.afunction());

                reveal(bfunction);
                assert(bfunction());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] across_crates verus_code! {
        use vstd::seq::*;
        proof fn aproof(s: Seq<nat>)
            requires s == seq![1nat, 2nat],
        {
            reveal_with_fuel(Seq::filter, 3);
            assert(s.filter(|x| x == 1) =~= seq![1nat]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] regression_704_impl_arg verus_code! {
        trait X {}
        impl X for int {}

        #[verifier::opaque]
        spec fn foo(x: impl X) -> bool {
            true
        }

        proof fn test() {
            reveal(foo);
            assert(foo(3int));
        }
    } => Ok(())
}
