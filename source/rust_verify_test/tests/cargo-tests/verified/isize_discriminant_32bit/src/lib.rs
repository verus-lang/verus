#![no_std]
use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

// https://github.com/verus-lang/verus/issues/2783
#[repr(isize)]
#[derive(Clone, Copy)]
enum E {
    A = -1,
    B = 0,
}

proof fn test() {
    assert(E::A as int == -1);
    assert(E::B as int == 0);
}

} // verus!
