#![allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::prelude::*;

pub mod agreement;
pub mod log;
pub mod monotonic_counter;
pub mod oneshot;

verus! {

pub fn main() {
}

} // verus!
