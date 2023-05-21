use vstd::prelude::*;

verus! {

fn main() {}

proof fn test_funext_specific_1(f1: FnSpec(u8) -> int, f2: FnSpec(u8) -> int)
    requires forall|x: u8| #[trigger] f1(x) == f2(x)
    ensures f1 == f2
{
    assert(ext_equal(f1, f2));
}

proof fn test_funext_specific_1_alt(f1: FnSpec(u8) -> int, f2: FnSpec(u8) -> int)
    requires forall|x: u8| #[trigger] f1(x) == f2(x)
    ensures f1 == f2
{
    assert(ext_equal(f1, f2));
}


proof fn test_funext_specific_2(f1: FnSpec(u8, u16) -> int, f2: FnSpec(u8, u16) -> int)
    requires forall|x, y| #[trigger] f1(x, y) == f2(x, y)
    ensures f1 == f2
{
    assert(ext_equal(f1, f2));
}

} // verus!
