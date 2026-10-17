// EXPECTED-ERROR: disallowed: constructor for an opaque datatype
use vstd::prelude::*;
use vstd::resource::agree::AgreementRA;
use vstd::resource::pcm::Resource;
use vstd::resource::tsm_context::Descriptor;

verus! {

proof fn cannot_bypass_metadata_invariant() {
    let tracked resource = Resource::<Option<AgreementRA<u64>>>::alloc(None);
    let tracked descriptor = Descriptor::<u64> { resource };
}

} // verus!
fn main() {}
