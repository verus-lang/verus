// EXPECTED-ERROR: precondition not satisfied
#[path = "../guarded_readers.rs"]
mod definition;
use definition::GuardedReaders;
use vstd::cell::PCell;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::resource::agree::AgreementRA;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm_finite_multiset::finite_multiset_frag;
verus! {

pub fn cannot_choose_an_unobserved_guard_key() {
    let (_, Tracked(permission)) = PCell::new(7u64);
    let ghost p = permission;
    let tracked mut base = IMap::tracked_empty();
    proof {
        base.tracked_insert(GuardedReaders::__StorageKey::stored(0int), GuardedReaders::__StorageValue::stored(permission));
        assert(base =~= GuardedReaders::__tag_stored(IMap::empty().insert(0int, p)));
    }
    let tracked all = GuardedReaders::Protocol::<u64>::initialize(base, p);
    let ghost reader = GuardedReaders::Fragment::<u64> {
        readers: finite_multiset_frag(Multiset::singleton(p)),
        ..GuardedReaders::Fragment::unit()
    };
    let ghost key = GuardedReaders::Fragment::<u64> {
        slot: Some(AgreementRA::Agree(0int)),
        ..GuardedReaders::Fragment::unit()
    };
    proof {
        reader.readers.op_unit();
    }
    let tracked (reader, _key) = all.split(reader, key);
    let tracked invalid = GuardedReaders::Protocol::<u64>::reader_guard(&reader, p);
}

fn main() {
}

} // verus!
