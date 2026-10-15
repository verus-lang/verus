// EXPECTED-ERROR: precondition not satisfied
//! Agreement requires both observations to belong to the same protocol.
#[path = "../counting.rs"]
mod complete_counting;
use vstd::prelude::*;
verus! {

proof fn compare_other_protocol() {
    let tracked (instance, mut counter) = complete_counting::Instance::<int>::new();
    let tracked (other, mut other_counter) = complete_counting::Instance::<int>::new();
    instance.writeable_to_readable(&mut counter, 17int);
    other.writeable_to_readable(&mut other_counter, 19int);
    let tracked first = instance.new_ref(&mut counter);
    let tracked second = other.new_ref(&mut other_counter);
    instance.compare_refs(&first, &second);
}

fn main() {
}

} // verus!
