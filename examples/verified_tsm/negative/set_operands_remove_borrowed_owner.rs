// EXPECTED-ERROR: precondition not satisfied
#[path = "../set_operands.rs"]
mod demo;
use vstd::prelude::*;
use vstd::set::*;
verus! {

proof fn borrowed_members_cannot_be_removed() {
    let tracked (owner, shared) = demo::allocate_without_permissions();
    let tracked output = demo::SetPermissions::Protocol::remove_many_with_shared(
        owner,
        &shared,
        Set::empty().insert(1int),
    );
}

} // verus!
fn main() {}
