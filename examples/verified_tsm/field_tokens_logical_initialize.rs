use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::Multiset;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{ X<T>{
fields{
#[sharding(constant)]pub tag:T,
#[sharding(variable)]pub v:int,
#[sharding(count)]pub c:nat,
#[sharding(bool)]pub b:bool,
#[sharding(option)]pub o:Option<int>,
#[sharding(persistent_bool)]pub pb:bool,
#[sharding(persistent_count)]pub pc:nat,
#[sharding(persistent_option)]pub po:Option<int>,
#[sharding(imap)]pub m:IMap<int,int>,
#[sharding(multiset)]pub ms:Multiset<int>,
#[sharding(persistent_iset)]pub ps:ISet<int>,
}
init!{initialize(tag:T,enabled:bool){
init tag=tag; init v=17; init c=9; init b=enabled; init o=if enabled{Some(7)}else{None};
init pb=enabled; init pc=9; init po=if enabled{Some(8)}else{None};
init m=IMap::empty().insert(0,7); init ms=Multiset::singleton(4); init ps=ISet::empty().insert(5);
}}
}}

fn main() {
    proof {
        let tracked (
            Tracked(instance),
            Tracked(v),
            Tracked(mut c),
            Tracked(b),
            Tracked(o),
            Tracked(pb),
            Tracked(pc),
            Tracked(po),
            Tracked(mut m),
            Tracked(mut ms),
            Tracked(mut ps),
        ) = X::Instance::initialize(10int, true);
        assert(instance.tag() == 10 && v.value() == 17 && c.count() == 9);
        assert(b is Some && o is Some && pb is Some && po is Some);
        assert(o->Some_0.value() == 7 && po->Some_0.value() == 8);
        let tracked part = c.split(2);
        assert(c.count() == 7);
        c.join(part);
        let tracked copied = pc.clone();
        let tracked small = copied.weaken(2);
        assert(small.count() == 2);
        let tracked copied = po.tracked_borrow().clone();
        assert(copied.value() == 8);
        let tracked entry = m.remove(0);
        assert(entry.value() == 7);
        m.insert(entry);
        let tracked element = ms.remove(4);
        assert(element.element() == 4);
        ms.insert(element);
        let tracked element = ps.remove(5);
        let tracked copied = element.clone();
        assert(copied.element() == 5);
        ps.insert(element);
        let tracked (
            Tracked(empty_instance),
            Tracked(v),
            Tracked(c),
            Tracked(b),
            Tracked(o),
            Tracked(pb),
            Tracked(pc),
            Tracked(po),
            Tracked(m),
            Tracked(ms),
            Tracked(ps),
        ) = X::Instance::initialize(11int, false);
        assert(b is None && o is None && pb is None && po is None && empty_instance.tag() == 11);

    }
}

} // verus!
