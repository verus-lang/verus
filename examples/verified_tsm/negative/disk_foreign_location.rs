// EXPECTED-ERROR: precondition not satisfied
#[path = "../disk_example.rs"]
mod disk_example;
use disk_example::*;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm_collections::*;
use vstd::resource::Loc;

verus! {

proof fn reject_foreign_fragment(
    tracked auth: &DiskInterp,
    tracked leaf: &Fragment,
    location: Loc,
    other: Loc,
    disk: Map<nat, Block>,
)
    requires
        location != other,
        auth.loc() == location,
        auth.fragment() == auth_fragment(disk),
        leaf.well_formed(other),
{
    values_agree(auth, leaf, location, disk);
}

} // verus!
fn main() {}
