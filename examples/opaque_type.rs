use vstd::prelude::*;
verus!{
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
fn main(){}
}