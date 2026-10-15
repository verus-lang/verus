use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {  X<T> {
    fields {
        #[sharding(map)] pub m: Map<int, T>,
        #[sharding(imap)] pub n: IMap<int, T>,
    }
    init! { initialize() { init m = Map::empty(); init n = IMap::empty(); } }
} }

proof fn test<T>() {
    let tracked (Tracked(inst), Tracked(m), Tracked(n)) = X::Instance::<T>::initialize();
    let tracked m: X::m_map<T> = m;
    let tracked n: X::n_map<T> = n;
    assert(m.instance_id() == inst.id());
    assert(n.instance_id() == inst.id());
    assert(m.map() =~= Map::empty());
    assert(n.map() =~= IMap::empty());
}

fn main() {
    proof {
        test::<int>();
    }
}

} // verus!
