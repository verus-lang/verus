use vstd::prelude::*;

verus! {

fn main() {
}

proof fn test_funext_specific_1(f1: spec_fn(u8) -> int, f2: spec_fn(u8) -> int)
    requires
        forall|x: u8| #[trigger] f1(x) == f2(x),
    ensures
        f1 == f2,
{
    assert(f1 =~= f2);
}

proof fn test_funext_specific_1_alt(f1: spec_fn(u8) -> int, f2: spec_fn(u8) -> int)
    requires
        forall|x: u8| #[trigger] f1(x) == f2(x),
    ensures
        f1 == f2,
{
    assert(f1 =~= f2);
}

proof fn test_funext_specific_2(f1: spec_fn(u8, u16) -> int, f2: spec_fn(u8, u16) -> int)
    requires
        forall|x, y| #[trigger] f1(x, y) == f2(x, y),
    ensures
        f1 == f2,
{
    assert(f1 =~= f2);
}

} // verus!
