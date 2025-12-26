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
    // // async fn foo() -> (ret: (impl DummyTrait, impl DummyTrait))
    // //     ensures
    // //         ret.awaited() ==> ret@.0.dummy_spec(),
    // // {
    // //     (true, true)
    // // }
    async fn foo() -> (ret: usize)
        ensures
            // ret == 1,
            ({let here = 233usize; here == 234}),
    {
        1
    }
    // async fn bar()
    //     // opens_invariants none
    // {
    //     let future = foo();
    //     // assert(future.awaited() ==> future@.0.dummy_spec());
    //     assert(future.awaited() ==> future@ == 2);
    //     // let ret_0 = future.await.0;
    //     // let ret_0_ghost = Ghost(ret_0);
    //     // assert(ret_0.dummy_spec());
    // }
    // // fn baz() -> (ret: impl Future<Output = (impl DummyTrait, impl DummyTrait)>)
    // //     ensures
    // //         ret.awaited() ==> ret@.0.dummy_spec(),
    // // {
    // //     foo()
    // // }
}

fn main(){}