#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{cell::*, prelude::*};

//// InvCell

verus! {

// ANCHOR: inv_cell_example
spec fn result_of_computation() -> u64 {
    2
}

fn expensive_computation() -> (res: u64)
    ensures
        res == result_of_computation(),
{
    1 + 1
}

spec fn cell_is_valid(cell: &InvCell<Option<u64>>) -> bool {
    forall|v|
        (cell.inv(v) <==> match v {
            Option::Some(i) => i == result_of_computation(),
            Option::None => true,
        })
}

// Memoize the call to `expensive_computation()`.
// The argument here is an InvCell wrapping an Option<u64>,
// which is initially None, but then it is set to the correct
// answer once it's computed.
//
// The precondition here, given in the definition of `cell_is_valid` above,
// says that the InvCell has an invariant that the interior contents is either
// `None` or `Some(i)` where `i` is the desired value.
fn memoized_computation(cell: &InvCell<Option<u64>>) -> (res: u64)
    requires
        cell_is_valid(cell),
    ensures
        res == result_of_computation(),
{
    let c = cell.get();
    match c {
        Option::Some(i) => {
            // The value has already been computed; return the cached value
            i
        },
        Option::None => {
            // The value hasn't been computed yet. Compute it here
            let i = expensive_computation();
            // Store it for later
            cell.replace(Option::Some(i));
            // And return it now
            i
        },
    }
}
// ANCHOR_END: inv_cell_example

} // verus!
fn main() {}
