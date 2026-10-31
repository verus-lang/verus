use vstd::prelude::*;

verus! {

#[verifier::external_body]
pub fn helper_value() -> u32 {
    helper::value()
}

} // verus!
