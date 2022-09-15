use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;
use pervasive::cell::*;
use pervasive::option::*;

//// InvCell

verus!{

// ANCHOR: inv_cell_example
spec fn some_value() -> u64 { 2 }

fn expensive_computation() -> (res: u64)
    ensures res == some_value()
{
    1 + 1
}

// Memoize the call to `expensive_computation()`.
// The argument here is an InvCell wrapping an Option<u64>,
// which is initially None, but then it is set to the correct
// answer once it's computed.
//
// The precondition here says that:
// The InvCell has an invariant that the interior contents is either
// `None` or `Some(i)` where `i` is the desired value.

fn memoized_computation(cell: &InvCell<Option<u64>>) -> u64
    requires
        cell.wf(),
        forall |v| (cell.inv(v) <==>
            match v {
                Option::Some(i) => i == some_value(),
                Option::None => true,
            }),
{
    let c = cell.get();
    match c {
        Option::Some(i) => {
            // The value has already been computed; return the cache value
            i
        } 
        Option::None => {
            // The value hasn't been computed yet. Compute it here
            let i = expensive_computation();
            // Store it for later
            cell.replace(Option::Some(i));
            // And return it now
            i
        }
    }
}
// ANCHOR_END: inv_cell_example

}

fn main() { }
