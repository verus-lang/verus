// rust_verify/tests/example.rs
#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::{cell::invcell::*, prelude::*};
use vstd::predicate::Predicate;

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

// Implement this trait to specify validity for the cell contents
//
// Validity of the interior contents of the cell means that the value is either
// `None` or `Some(i)` where `i` is the desired value.
struct MemoizedCellInvariant;
impl Predicate<Option<u64>> for MemoizedCellInvariant {
    closed spec fn predicate(&self, v: Option<u64>) -> bool {
        match v {
            Option::Some(i) => i == result_of_computation(),
            Option::None => true,
        }
    }
}

// Memoize the call to `expensive_computation()`.
// The argument here is an InvCell wrapping an Option<u64>,
// which is initially None, but then it is set to the correct
// answer once it's computed.
fn memoized_computation(cell: &InvCell<Option<u64>, MemoizedCellInvariant>) -> (res: u64)
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
