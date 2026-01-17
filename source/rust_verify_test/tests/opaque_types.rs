#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

fn assert_spec_eq_type_err(err: TestErr, typ1: &str, typ2: &str) {
    assert_eq!(err.errors.len(), 1);
    let err0 = &err.errors[0];
    assert!(err0.code.is_none());
    assert!(err0.message.contains("mismatched types; types must be compatible to use == or !="));
    assert!(err0.spans.len() == 2 || err0.spans.len() == 3);
    assert_spans_contain(err0, typ1);
    assert_spans_contain(err0, typ2);
}

test_verify_one_file! {
    #[test] test_return_opaque_type verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{}
        impl DummyTrait for bool{}
        fn return_opaque_variable() -> impl DummyTrait{
            true
        }
        fn test(){
            let x = return_opaque_variable();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_return_opaque_type_hides_real_type verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{}
        impl DummyTrait for bool{}
        fn return_opaque_variable() -> impl DummyTrait{
            true
        }
        fn test(){
            let x = return_opaque_variable();
            assert(x);
        }
    } => Err(err) => assert_rust_error_msg_all(err, "mismatched types")
}

test_verify_one_file! {
    #[test] test_return_opaque_type_allows_trait_functions verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;
        }
        impl DummyTrait for bool{
            fn foo(&self) -> (ret: bool)
            {
                false
            }
        }
        fn return_opaque_variable() -> impl DummyTrait{
            true
        }
        fn test(){
            let x = return_opaque_variable();
            let ret = x.foo();
            assert(ret == false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_return_opaque_type_reveal_real_type verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;
            fn get_output(&self) -> (ret : Self::Output);
        }
        impl DummyTrait for bool{
            type Output = bool;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            fn get_output(&self) -> (ret : Self::Output){
                *self
            }
        }
        fn return_opaque_variable() -> impl DummyTrait<Output = bool>{
            true
        }
        fn test(){
            let x = return_opaque_variable();
            let output = x.get_output();
            // Here Verus should be able to infer the type of output, but assertion should fail
            assert(output);  // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_no_opaque_types_from_traits verus_code! {
    use vstd::prelude::*;
    trait DummyTraitA{}
    impl<T> DummyTraitA for T {}
    trait DummyTraitB {
        fn foo(&self) -> impl DummyTraitA;
    }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not yet support Opaque types in trait def")
}

test_verify_one_file! {
    #[test] test_opaque_function_with_ensures verus_code! {
        use vstd::prelude::*;
        trait DummyTraitA{}
        impl<T> DummyTraitA for T {}
        fn foo() -> (ret: impl DummyTraitA)
            ensures
                ret == ret
        {
            true
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_function_return_value_type verus_code! {
        use vstd::prelude::*;
        trait DummyTraitA{}
        impl<T> DummyTraitA for T {}
        fn foo() -> (ret: impl DummyTraitA)
            ensures
                ret == ret,
                ret == true,
        {
            true
        }
    } => Err(err) => assert_spec_eq_type_err(err, "opaque_ty", "bool")
}

test_verify_one_file! {
    #[test] test_opaque_type_projection_without_annotation  verus_code! {
        use vstd::prelude::*;
        trait DummyTraitA{
            type Output;
            spec fn get_output(&self) -> Self::Output;
        }
        impl<T> DummyTraitA for T {
            type Output = T;
            uninterp spec fn get_output(&self) -> Self::Output;
        }
        fn foo() -> (ret: impl DummyTraitA)
            ensures
                ret == ret,
                ret.get_output() == true,
        {
            true
        }
    } => Err(err) => assert_spec_eq_type_err(err, "<opaque_ty as test_crate::DummyTraitA>::Output", "bool")
}

test_verify_one_file! {
    #[test] test_opaque_type_projection_with_annotation verus_code! {
        use vstd::prelude::*;
        trait DummyTraitA{
            type Output;
            spec fn get_output(&self) -> Self::Output;
        }
        impl<T> DummyTraitA for T {
            type Output = T;
            uninterp spec fn get_output(&self) -> Self::Output;
        }
        fn foo() -> (ret: impl DummyTraitA)
            ensures
                ret == ret,
                ret.get_output() == true,  // FAILS
        {
            true
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_opaque_type_external_body_function verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;
            spec fn bar(&self) -> bool;
        }
        impl DummyTrait for bool{
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool {
                true
            }
        }

        #[verifier::external_body]
        fn return_opaque_variable() -> (ret: impl DummyTrait)
            ensures
                ret.bar() == false,
        {
            true
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_assume_spec_ok verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
        }
        impl<T> DummyTrait for T{
            type Output = T;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }
        }
        #[verifier::external]
        fn return_opaque_variable<T>(x:T) -> impl DummyTrait<Output = T>
        {
            x
        }
        assume_specification<T> [ return_opaque_variable::<T> ](x:T) -> (ret: impl DummyTrait<Output = T>)
            ensures ret.bar();
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_tuple_opaque_type_assume_spec_ok verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
        }
        impl<T> DummyTrait for T{
            type Output = T;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }
        }
        #[verifier::external]
        fn return_opaque_variable<T>(x:T, y:T) -> (impl DummyTrait<Output = T>, impl DummyTrait<Output = T>)
        {
            (x, y)
        }
        assume_specification<T> [ return_opaque_variable::<T> ](x:T, y:T) -> (ret: (impl DummyTrait<Output = T>, impl DummyTrait<Output = T>))
            ensures ret.0.bar();
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_assume_spec_fail verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
        }
        impl<T> DummyTrait for T{
            type Output = T;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }
        }
        #[verifier::external]
        fn return_opaque_variable<T>(x:T) -> impl DummyTrait<Output = T>
        {
            x
        }
        assume_specification<T> [ return_opaque_variable::<T> ](x:T) -> (ret: impl DummyTrait)
            ensures ret.bar();
    }  => Err(err) => assert_vir_error_msg(err, "assume_specification requires function type signature to match")
}

test_verify_one_file! {
    #[test] test_nested_opaque_type_assume_spec_ok verus_code! {
        use vstd::prelude::*;
         trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
            spec fn get_self(&self) -> Self::Output;
        }
        impl DummyTrait for bool{
            type Output = bool;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }

            spec fn get_self(&self) -> Self::Output{
                *self
            }
        }
        #[verifier::external]
        fn return_opaque_variable() -> impl DummyTrait<Output = impl DummyTrait>
        {
            true
        }
        assume_specification [ return_opaque_variable ]() -> (ret: impl DummyTrait<Output = impl DummyTrait>)
            ensures ret.get_self().bar()
            ;   

        fn test(){
            let ret = return_opaque_variable();
            assert(ret.get_self().bar());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_nested_opaque_type_assume_spec_fail verus_code! {
        use vstd::prelude::*;
         trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
            spec fn get_self(&self) -> Self::Output;
        }
        impl DummyTrait for bool{
            type Output = bool;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }

            spec fn get_self(&self) -> Self::Output{
                *self
            }
        }
        #[verifier::external]
        fn return_opaque_variable() -> impl DummyTrait<Output = impl DummyTrait<Output = bool>>
        {
            true
        }
        assume_specification [ return_opaque_variable ]() -> (ret: impl DummyTrait<Output = impl DummyTrait>)
            ensures ret.get_self().bar()
            ;   
    } => Err(err) => assert_vir_error_msg(err, "assume_specification requires function type signature to match")
}

test_verify_one_file! {
    #[test] test_opaque_type_returns_error verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
        }
        impl<T> DummyTrait for T{
            type Output = T;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }
        }
        fn return_opaque_variable<T>(x:T) -> impl DummyTrait<Output = T>
            returns x
        {
            x
        }
    }  => Err(err) => assert_vir_error_msg(err, "`returns` clause is not allowed for function that returns opaque type")
}

test_verify_one_file! {
    #[test] test_tuple_of_opaque_types_ok verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            spec fn bar(&self) -> bool;
        }
        impl DummyTrait for bool{
            spec fn bar(&self) -> bool{
                true
            }
        }
        fn foo() -> (ret:(impl DummyTrait, impl DummyTrait))
            ensures
                ret.0.bar(),
                ret.1.bar(),
        {
            (true, true)
        }
    }  => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_from_opaque_type_ok verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            spec fn bar(&self) -> bool;
        }
        impl DummyTrait for bool{
            spec fn bar(&self) -> bool{
                true
            }
        }
        fn foo() -> (ret:(impl DummyTrait, impl DummyTrait))
            ensures
                ret.0.bar(),
                ret.1.bar(),
        {
            (true, true)
        }
        fn bar() -> (ret:(impl DummyTrait, impl DummyTrait))
            ensures
                ret.0.bar(),
                ret.1.bar(),
        {
            foo()
        }
    }  => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_projection_fail verus_code! {
        use vstd::prelude::*;
        trait Tr{
            spec fn dummy_spec(&self) -> bool;
            type T;
            type Y;
            spec fn ret_y(&self) -> Self::Y;
        }
        impl Tr for bool{
            spec fn dummy_spec(&self) -> bool{
                true
            }
            type T = bool;
            type Y = Self;
            uninterp spec fn ret_y(&self) -> Self::Y;
        }
        fn boo() -> (ret: impl Tr<T = impl Tr<T = bool>, Y = impl Tr<T = bool>>)
            ensures
                // ret.ret_y().dummy_spec(),
        {
            true
        }
        fn bar() -> (ret: impl Tr<Y = impl Tr<T = bool>, T = impl Tr<T = bool>>)
            ensures
                ret.ret_y().dummy_spec(), // FAILS
        {
            boo()
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_opaque_type_projection_ok verus_code! {
        use vstd::prelude::*;
        trait Tr{
            spec fn dummy_spec(&self) -> bool;
            type T;
            type Y;
            spec fn ret_y(&self) -> Self::Y;
        }
        impl Tr for bool{
            spec fn dummy_spec(&self) -> bool{
                true
            }
            type T = bool;
            type Y = Self;
            uninterp spec fn ret_y(&self) -> Self::Y;
        }

        fn boo() -> (ret: impl Tr<T = impl Tr<T = bool>, Y = impl Tr<T = bool>>)
            ensures
                ret.ret_y().dummy_spec(),
        {
            true
        }
        fn bar() -> (ret: impl Tr<Y = impl Tr<T = bool>, T = impl Tr<T = bool>>)
            ensures
                ret.ret_y().dummy_spec(),
        {
            boo()
        }
    }  => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_projection_inherent_ok verus_code! {
        use vstd::prelude::*;
        trait Tr{
            spec fn dummy_spec(&self) -> bool;
            type T;
            type Y;
            spec fn ret_y(&self) -> Self::Y;
        }
        impl Tr for bool{
            spec fn dummy_spec(&self) -> bool{
                true
            }
            type T = bool;
            type Y = Self;
            uninterp spec fn ret_y(&self) -> Self::Y;
        }

        fn boo() -> (ret: impl Tr<T = impl Tr<T = bool>, Y = bool>)
            ensures
                // ret.ret_y().dummy_spec(),
        {
            true
        }
        fn bar() -> (ret: impl Tr<Y = impl Tr<T = bool>, T = impl Tr<T = bool>>)
            ensures
                ret.ret_y().dummy_spec(),
        {
            boo()
        }
    } => Ok(())
}
