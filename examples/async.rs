use verus_builtin_macros::*;
use vstd::*;
use std::future::*;
use vstd::future::*;
use vstd::prelude::*; 

verus! {
    // trait DummyTrait{
    //     spec fn dummy_spec(&self) -> bool;
    // }
    // impl DummyTrait for bool{
    //     spec fn dummy_spec(&self) -> bool{
    //         true
    //     }
    // }    
    // async fn foo() -> (ret: (impl DummyTrait, impl DummyTrait))
    //     ensures
    //         ret.0.dummy_spec(),
    // {
    //     (true, true)
    // }
    // async fn bar()
    // {
    //     let future = foo();
    //     assert(future.awaited() ==> future@.0.dummy_spec());
    //     let ret_0 = future.await.0;
    //     assert(ret_0.dummy_spec());
    // }
    // fn baz() -> (ret: impl Future<Output = (impl DummyTrait, impl DummyTrait)>)
    //     ensures
    //         ret.awaited() ==> ret@.0.dummy_spec(),
    // {
    //     foo()
    // }
    // async fn test_baz(){
    //     let future = baz();
    //     assert(future.awaited() ==> future@.0.dummy_spec());
    // }

    // pub struct WrapperUsize{
    //     pub x: usize
    // }
    // impl WrapperUsize{
    //     async fn mut_usize(&mut self) -> (ret: ())
    //         ensures
    //             self == old(self),
    //     {
    //     }
    // }

    // async fn foo(immut_usize: &usize) -> (ret: ())
    //     ensures
    //         immut_usize == immut_usize,
    // {
    //     ()
    // }

    // async fn bar(mut_usize: &mut usize) -> (ret: usize)
    //         ensures
    //             mut_usize == old(mut_usize),
    // {
    //     1
    // }

    // async fn call_mut_usize(){
    //     let mut x = 0;
    //     let f = bar(&mut x);
    //     f.await;
    //     assert(x == 1);
    // }

    #[verifier(external)]
    fn negate_int(b: bool, x: u8) -> bool {
        !b
    }

    #[verifier(external_fn_specification)]
    fn negate_int_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
        requires x != 0,
        ensures ret_b == !b
    {
        negate_int(b, x)
    }

    #[verifier(external)]
    async fn negate_booool(b: bool, x: u8) -> bool {
        !b
    }

    #[verifier(external_fn_specification)]
    async fn negate_booool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
        requires x != 0,
        ensures ret_b == !b
    {
        negate_booool(b, x).await
    }


    // #[verifier(external)]
    // async fn negate_bool(b: bool, x: u8) -> impl Future<Output = bool> {
    //     negate_booool(b, x)
    // }

    // #[verifier(external_fn_specification)]
    // async fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: impl Future<Output = bool>)
    //     requires x != 0,
    //     ensures ret_b == !b
    // {
    //     negate_bool(b, x).await
    // }

    async fn test(){
        let f = negate_booool(true, 1);
    }
}

fn main(){}