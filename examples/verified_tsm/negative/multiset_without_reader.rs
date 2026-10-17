// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::Multiset;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    Readers {
        fields { #[sharding(multiset)] pub readers:Multiset<int>, }
        init! { initialize() { init readers=Multiset::singleton(1int); } }
        transition! { consume() { remove readers -= {1int}; } }
    }
}

pub proof fn missing_reader() {
    use vstd::resource::tsm_finite_multiset::finite_multiset_frag;
    use vstd::resource::pcm::PCM;
    use vstd::resource::algebra::ResourceAlgebra;
    let tracked all = Readers::Protocol::initialize();
    let empty = Readers::Fragment { readers: finite_multiset_frag(Multiset::empty()) };
    let elsewhere = Readers::Fragment { readers: finite_multiset_frag(Multiset::singleton(1int)) };
    elsewhere.readers.op_unit();
    vstd::resource::tsm_finite_multiset::FiniteMultisetRA::commutative(
        empty.readers,
        elsewhere.readers,
    );
    let tracked (empty, elsewhere) = all.split(empty, elsewhere);
    let tracked invalid = Readers::Protocol::consume(empty);
}

} // verus!
fn main() {}
