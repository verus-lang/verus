#![recursion_limit = "512"]
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
mod pervasive;
#[allow(unused_imports)]
use pervasive::option::Option;
#[allow(unused_imports)]
use pervasive::*;
#[allow(unused_imports)]
use pervasive::function::*;
#[allow(unused_imports)]
use seq::*;

verus! {

fn main() {}

proof fn test_funext_specific_1(f1: FnSpec(u8) -> int, f2: FnSpec(u8) -> int)
  requires forall |x: u8| #[trigger] f1(x) == f2(x)
  ensures f1 == f2
{
    fun_ext::<u8, int>(f1, f2)
}

proof fn test_funext_specific_1_alt(f1: FnSpec(u8) -> int, f2: FnSpec(u8) -> int)
  requires forall |x: u8| #[trigger] f1(x) == f2(x)
  ensures f1 == f2
{
    fun_ext_1::<u8, int>(f1, f2)
}


proof fn test_funext_specific_2(f1: FnSpec(u8, u16) -> int, f2: FnSpec(u8, u16) -> int)
  requires forall |x, y| #[trigger] f1(x, y) == f2(x, y)
  ensures f1 == f2
{
    fun_ext_2::<u8, u16, int>(f1, f2)
}


} // verus!
