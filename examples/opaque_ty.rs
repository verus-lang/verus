#[allow(unused_imports)]
use {verus_builtin::*, verus_builtin_macros::*, prelude::*, seq::*, vstd::*};

verus! {
trait DummyTrait{
    spec fn s(&self) -> bool;
}
impl DummyTrait for bool{
    spec fn s(&self) -> bool{
        true
    }
}
fn return_opaque_variable() -> (ret: (impl DummyTrait, impl DummyTrait))
    ensures
        ret.0.s(),
{
    (true, true)
}
fn return_opaque_variable1() -> (ret: impl DummyTrait)
    ensures
        ret.s(),
{
    true
}
}

fn main(){}