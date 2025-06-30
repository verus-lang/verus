#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

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
    } => Err(err) => assert_vir_error_msg(err, "function with opaque type does not yet support ensure clause")
}
