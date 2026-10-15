use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::Multiset;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
Collections {
    fields {
        #[sharding(map)] pub m: Map<int,int>,
        #[sharding(imap)] pub im: IMap<int,int>,
        #[sharding(set)] pub s: Set<int>,
        #[sharding(iset)] pub is: ISet<int>,
        #[sharding(multiset)] pub ms: Multiset<int>,
        #[sharding(persistent_map)] pub pm: Map<int,int>,
        #[sharding(persistent_imap)] pub pim: IMap<int,int>,
        #[sharding(persistent_set)] pub ps: Set<int>,
        #[sharding(persistent_iset)] pub pis: ISet<int>,
    }
    init! { initialize() {
        init m=Map::empty().insert(0,7);init im=IMap::empty().insert(0,7);
        init s=Set::empty().insert(4);init is=ISet::empty().insert(4);
        init ms=Multiset::singleton(4);
        init pm=Map::empty().insert(0,7);init pim=IMap::empty().insert(0,7);
        init ps=Set::empty().insert(4);init pis=ISet::empty().insert(4);
    } }
}}

fn main() {
    proof {
        let tracked (
            Tracked(inst),
            Tracked(mut m),
            Tracked(mut im),
            Tracked(mut s),
            Tracked(mut is),
            Tracked(mut ms),
            Tracked(mut pm),
            Tracked(mut pim),
            Tracked(mut ps),
            Tracked(mut pis),
        ) = Collections::Instance::initialize();
        let tracked entry = m.remove(0);
        assert(entry.value() == 7 && entry.instance_id() == inst.id());
        m.insert(entry);
        let tracked entry = im.remove(0);
        assert(entry.value() == 7);
        im.insert(entry);
        let tracked entry = s.remove(4);
        assert(entry.element() == 4);
        s.insert(entry);
        let tracked entry = is.remove(4);
        assert(entry.element() == 4);
        is.insert(entry);
        let tracked entry = ms.remove(4);
        assert(entry.element() == 4);
        ms.insert(entry);
        let tracked entry = pm.remove(0);
        let tracked copied = entry.clone();
        assert(copied.value() == 7 && copied.instance_id() == inst.id());
        pm.insert(entry);
        let tracked entry = pim.remove(0);
        let tracked copied = entry.clone();
        assert(copied.value() == 7);
        pim.insert(entry);
        let tracked entry = ps.remove(4);
        let tracked copied = entry.clone();
        assert(copied.element() == 4);
        ps.insert(entry);
        let tracked entry = pis.remove(4);
        let tracked copied = entry.clone();
        assert(copied.element() == 4);
        pis.insert(entry);
    }
}

} // verus!
