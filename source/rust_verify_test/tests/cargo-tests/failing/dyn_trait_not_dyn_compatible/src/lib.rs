use dyn_trait_def::NotDyn;
use vstd::prelude::*;

verus! {

// dyn_trait_def exports NotDyn as not Verus dyn-compatible, so this must be rejected
pub fn f(x: &dyn NotDyn) {
}

} // verus!
