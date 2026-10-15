// EXPECTED-ERROR: precondition not satisfied
//! A stored payload cannot be recovered while an owned reader remains live.
#[path = "../counting.rs"]
mod complete_counting;
use vstd::prelude::*;
verus! {

proof fn withdraw_with_reader() {
    let tracked (instance, mut counter) = complete_counting::Instance::<int>::new();
    instance.writeable_to_readable(&mut counter, 17int);
    let tracked reader = instance.new_ref(&mut counter);
    let tracked payload = instance.readable_to_writeable(&mut counter);
}

fn main() {
}

} // verus!
