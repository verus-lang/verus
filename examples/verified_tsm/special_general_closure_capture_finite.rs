//! Complete original special-operation relations with a checked resource companion.
//! Tagged physical storage preserves both original storage projections; the
//! tracked histories exercise all four transitions and reuse withdrawn permission12.
#![allow(unused_imports)]
use verus_state_machines_macros::{verified_state_machine_model, verified_tokenized_state_machine};
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
use vstd::resource::tsm_collections::*;
use vstd::{imap::*, iset::*, map::*, modes::*, multiset::*, pervasive::*, set::*};
verified_state_machine_model! { Y {
    fields {
        #[sharding(option)]
        pub opt: Option<int>,

        #[sharding(map)]
        pub map: Map<int, int>,

        #[sharding(multiset)]
        pub mset: Multiset<int>,

        #[sharding(storage_option)]
        pub storage_opt: Option<int>,

        #[sharding(storage_map)]
        pub storage_map: Map<int, int>,
    }

    transition!{
        tr1() {
            remove opt -= ( Option::Some(5) );
            add opt += ( Option::Some(8) );

            remove map -= ( Map::<int, int>::empty().insert(0, 1) );
            have map >= ( Map::<int, int>::empty().insert(2, 3) );
            add map += ( Map::<int, int>::empty().insert(4, 5) ) by { /* Original unsafe override omitted from this pure diagnostic. */ };

            remove mset -= ( Multiset::<int>::singleton(10) );
            have mset >= ( Multiset::<int>::singleton(11) );
            add mset += ( Multiset::<int>::singleton(12) );

            withdraw storage_opt -= ( Option::Some(13) ) by { /* Original unsafe override omitted from this pure diagnostic. */ };
            deposit storage_opt += ( Option::Some(14) );

            withdraw storage_map -= ( Map::<int, int>::empty().insert(15, 16) ) by { /* Original unsafe override omitted from this pure diagnostic. */ };
            deposit storage_map += ( Map::<int, int>::empty().insert(17, 18) ) by { /* Original unsafe override omitted from this pure diagnostic. */ };
        }
    }

    transition!{
        tr2() {
            have opt >= (Option::Some(7));
            add map += (Map::<int, int>::empty().insert(4, 5)) by { /* Original unsafe override omitted from this pure diagnostic. */ };
        }
    }

    transition!{
        tr3() {
            remove opt -= (Option::Some(7));
            withdraw storage_opt -= (Option::Some(12)) by { /* Original unsafe override omitted from this pure diagnostic. */ };
        }
    }

    transition!{
        tr4() {
            add opt += (Option::Some(7)) by { /* Original unsafe override omitted from this pure diagnostic. */ };
            deposit storage_opt += (Option::Some(12)) by { /* Original unsafe override omitted from this pure diagnostic. */ };
        }
    }
}}

verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(5)
    &&& map![0 => 1].submap_of(pre.map)
    &&& map![2 => 3].submap_of(pre.map.remove_keys(map![0 => 1int].dom()))
    &&& pre.map.remove_keys(map![0 => 1int].dom()).dom().disjoint(map![4 => 5int].dom()) ==> {
        &&& Multiset::singleton(10).subset_of(pre.mset)
        &&& Multiset::singleton(11).subset_of(pre.mset.sub(Multiset::singleton(10)))
        &&& (pre.storage_opt == Option::Some(13) ==> (map![15 => 16].submap_of(pre.storage_map)
            ==> (pre.storage_map.remove_keys(map![15 => 16int].dom()).dom().disjoint(
            map![17 => 18int].dom(),
        ) ==> {
            &&& post.opt == Option::Some(8)
            &&& post.map == pre.map.remove_keys(map![0 => 1int].dom()).union_prefer_right(
                map![4 => 5],
            )
            &&& post.mset == pre.mset.sub(Multiset::singleton(10)).add(Multiset::singleton(12))
            &&& post.storage_opt == Option::Some(14)
            &&& post.storage_map == pre.storage_map.remove_keys(
                map![15 => 16int].dom(),
            ).union_prefer_right(map![17 => 18])
        })))
    }
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(5)
    &&& post.opt == Option::Some(8)
    &&& map![0 => 1].submap_of(pre.map)
    &&& map![2 => 3].submap_of(pre.map.remove_keys(map![0 => 1int].dom()))
    &&& pre.map.remove_keys(map![0 => 1int].dom()).dom().disjoint(map![4 => 5int].dom())
    &&& post.map == pre.map.remove_keys(map![0 => 1int].dom()).union_prefer_right(map![4 => 5])
    &&& Multiset::singleton(10).subset_of(pre.mset)
    &&& Multiset::singleton(11).subset_of(pre.mset.sub(Multiset::singleton(10)))
    &&& post.mset == pre.mset.sub(Multiset::singleton(10)).add(Multiset::singleton(12))
    &&& pre.storage_opt == Option::Some(13)
    &&& post.storage_opt == Option::Some(14)
    &&& map![15 => 16].submap_of(pre.storage_map)
    &&& pre.storage_map.remove_keys(map![15 => 16int].dom()).dom().disjoint(map![17 => 18int].dom())
    &&& post.storage_map == pre.storage_map.remove_keys(map![15 => 16int].dom()).union_prefer_right(
        map![17 => 18],
    )
}

spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(7)
    &&& !pre.map.dom().contains(4) ==> {
        &&& post.map == pre.map.union_prefer_right(map![4 => 5])
        &&& post.opt == pre.opt
        &&& post.storage_opt == pre.storage_opt
        &&& post.storage_map == pre.storage_map
        &&& post.mset == pre.mset
    }
}

spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(7)
    &&& !pre.map.dom().contains(4)
    &&& post.map == pre.map.union_prefer_right(map![4 => 5])
    &&& post.opt == pre.opt
    &&& post.storage_opt == pre.storage_opt
    &&& post.storage_map == pre.storage_map
    &&& post.mset == pre.mset
}

spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(7)
    &&& pre.storage_opt == Option::Some(12) ==> {
        &&& post.storage_opt == Option::None
        &&& post.map == pre.map
        &&& post.storage_map == pre.storage_map
        &&& post.mset == pre.mset
        &&& post.opt == Option::None
    }
}

spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::Some(7)
    &&& post.opt == Option::None
    &&& pre.storage_opt == Option::Some(12)
    &&& post.storage_opt == Option::None
    &&& post.map == pre.map
    &&& post.storage_map == pre.storage_map
    &&& post.mset == pre.mset
}

spec fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
    pre.opt == Option::None ==> ((pre.storage_opt == Option::None ==> {
        &&& post.storage_opt == Option::Some(12)
        &&& post.map == pre.map
        &&& post.storage_map == pre.storage_map
        &&& post.mset == pre.mset
        &&& post.opt == Option::Some(7)
    }))
}

spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
    &&& pre.opt == Option::None
    &&& post.opt == Option::Some(7)
    &&& pre.storage_opt == Option::None
    &&& post.storage_opt == Option::Some(12)
    &&& post.map == pre.map
    &&& post.storage_map == pre.storage_map
    &&& post.mset == pre.mset
}

proof fn correct_tr1(pre: Y::State, post: Y::State) {
    requires(Y::State::tr1(pre, post));
    ensures(rel_tr1(pre, post));
}

proof fn rev_tr1(pre: Y::State, post: Y::State) {
    requires(rel_tr1(pre, post));
    ensures(Y::State::tr1(pre, post));
}

proof fn correct_tr1_strong(pre: Y::State, post: Y::State) {
    requires(Y::State::tr1_strong(pre, post));
    ensures(rel_tr1_strong(pre, post));
}

proof fn rev_tr1_strong(pre: Y::State, post: Y::State) {
    requires(rel_tr1_strong(pre, post));
    ensures(Y::State::tr1_strong(pre, post));
}

proof fn correct_tr2(pre: Y::State, post: Y::State) {
    requires(Y::State::tr2(pre, post));
    ensures(rel_tr2(pre, post));
}

proof fn rev_tr2(pre: Y::State, post: Y::State) {
    requires(rel_tr2(pre, post));
    ensures(Y::State::tr2(pre, post));
}

proof fn correct_tr2_strong(pre: Y::State, post: Y::State) {
    requires(Y::State::tr2_strong(pre, post));
    ensures(rel_tr2_strong(pre, post));
}

proof fn rev_tr2_strong(pre: Y::State, post: Y::State) {
    requires(rel_tr2_strong(pre, post));
    ensures(Y::State::tr2_strong(pre, post));
}

proof fn correct_tr3(pre: Y::State, post: Y::State) {
    requires(Y::State::tr3(pre, post));
    ensures(rel_tr3(pre, post));
}

proof fn rev_tr3(pre: Y::State, post: Y::State) {
    requires(rel_tr3(pre, post));
    ensures(Y::State::tr3(pre, post));
}

proof fn correct_tr3_strong(pre: Y::State, post: Y::State) {
    requires(Y::State::tr3_strong(pre, post));
    ensures(rel_tr3_strong(pre, post));
}

proof fn rev_tr3_strong(pre: Y::State, post: Y::State) {
    requires(rel_tr3_strong(pre, post));
    ensures(Y::State::tr3_strong(pre, post));
}

proof fn correct_tr4(pre: Y::State, post: Y::State) {
    requires(Y::State::tr4(pre, post));
    ensures(rel_tr4(pre, post));
}

proof fn rev_tr4(pre: Y::State, post: Y::State) {
    requires(rel_tr4(pre, post));
    ensures(Y::State::tr4(pre, post));
}

proof fn correct_tr4_strong(pre: Y::State, post: Y::State) {
    requires(Y::State::tr4_strong(pre, post));
    ensures(rel_tr4_strong(pre, post));
}

proof fn rev_tr4_strong(pre: Y::State, post: Y::State) {
    requires(rel_tr4_strong(pre, post));
    ensures(Y::State::tr4_strong(pre, post));
}

} // verus!
verus! {

broadcast use {
    vstd::map::group_map_lemmas,
    vstd::imap::group_imap_lemmas,
    vstd::iset::group_iset_lemmas,
    vstd::multiset::group_multiset_axioms,
};

/// Value tagging allows old and new optional permissions to be exchanged while
/// satisfying the existing storage-protocol disjoint-deposit contract.
pub ghost enum StorageKey {
    MapKey(int),
    OptionalValue(int),
}

pub open spec fn packed(opt: Option<int>, m: Map<int, int>) -> IMap<StorageKey, int> {
    let entries = m.to_imap();
    IMap::new(
        |tag: StorageKey|
            match tag {
                StorageKey::MapKey(k) => entries.dom().contains(k),
                StorageKey::OptionalValue(v) => opt == Some(v),
            },
        |tag: StorageKey|
            match tag {
                StorageKey::MapKey(k) => entries[k],
                StorageKey::OptionalValue(v) => v,
            },
    )
}

pub proof fn packed_map_at(opt: Option<int>, m: Map<int, int>, key: int)
    ensures
        packed(opt, m).dom().contains(StorageKey::MapKey(key)) == m.dom().contains(key),
        m.dom().contains(key) ==> packed(opt, m)[StorageKey::MapKey(key)] == m[key],
{
}

pub proof fn packed_option_at(opt: Option<int>, m: Map<int, int>, value: int)
    ensures
        packed(opt, m).dom().contains(StorageKey::OptionalValue(value)) == (opt == Some(value)),
        opt == Some(value) ==> packed(opt, m)[StorageKey::OptionalValue(value)] == value,
{
}

/// Concrete tagged-map shape for actual two-permission exchanges.
pub proof fn packed_pair(optional: int, key: int, value: int)
    ensures
        packed(Some(optional), Map::<int, int>::empty().insert(key, value)) == IMap::empty().insert(
            StorageKey::OptionalValue(optional),
            optional,
        ).insert(StorageKey::MapKey(key), value),
{
    let left = packed(Some(optional), Map::<int, int>::empty().insert(key, value));
    let right = IMap::empty().insert(StorageKey::OptionalValue(optional), optional).insert(
        StorageKey::MapKey(key),
        value,
    );
    assert(left =~= right) by {
        assert forall|tag: StorageKey| left.contains_key(tag) == right.contains_key(tag) by {
            match tag {
                StorageKey::MapKey(k) => {},
                StorageKey::OptionalValue(v) => {},
            }
        }
        assert forall|tag: StorageKey| left.contains_key(tag) implies left[tag] == right[tag] by {
            match tag {
                StorageKey::MapKey(k) => {},
                StorageKey::OptionalValue(v) => {},
            }
        }
    }
}

pub proof fn packed_optional(optional: Option<int>)
    ensures
        packed(optional, Map::<int, int>::empty()) == match optional {
            None => IMap::empty(),
            Some(v) => IMap::empty().insert(StorageKey::OptionalValue(v), v),
        },
{
    let left = packed(optional, Map::<int, int>::empty());
    let right = match optional {
        None => IMap::empty(),
        Some(v) => IMap::empty().insert(StorageKey::OptionalValue(v), v),
    };
    assert(left =~= right) by {
        assert forall|tag: StorageKey| left.contains_key(tag) == right.contains_key(tag) by {
            match tag {
                StorageKey::MapKey(k) => {},
                StorageKey::OptionalValue(v) => {},
            }
        }
        assert forall|tag: StorageKey| left.contains_key(tag) implies left[tag] == right[tag] by {
            match tag {
                StorageKey::MapKey(k) => {},
                StorageKey::OptionalValue(v) => {},
            }
        }
    }
}

pub proof fn normalize_map_operands(m: Map<int, int>, removed: int, old: int, added: int, new: int)
    ensures
        m.remove_keys(Map::<int, int>::empty().insert(removed, old).dom()) == m.remove(removed),
        m.union_prefer_right(Map::<int, int>::empty().insert(added, new)) == m.insert(added, new),
        m.remove_keys(Map::<int, int>::empty().insert(removed, old).dom()).union_prefer_right(
            Map::<int, int>::empty().insert(added, new),
        ) == m.remove(removed).insert(added, new),
{
    assert(m.remove_keys(Map::<int, int>::empty().insert(removed, old).dom()) =~= m.remove(
        removed,
    ));
    assert(m.union_prefer_right(Map::<int, int>::empty().insert(added, new)) =~= m.insert(
        added,
        new,
    ));
    assert(m.remove_keys(Map::<int, int>::empty().insert(removed, old).dom()).union_prefer_right(
        Map::<int, int>::empty().insert(added, new),
    ) =~= m.remove(removed).insert(added, new));
}

pub proof fn normalize_bag_operands(m: Multiset<int>)
    requires
        m.count(10int) >= 1,
    ensures
        m.sub(Multiset::singleton(10int)).add(Multiset::singleton(12int)) == m.remove(10int).insert(
            12int,
        ),
        m.sub(Multiset::empty().insert(10int)).add(Multiset::empty().insert(12int)) == m.remove(
            10int,
        ).insert(12int),
{
    assert(m.sub(Multiset::singleton(10int)).add(Multiset::singleton(12int)) =~= m.remove(
        10int,
    ).insert(12int));
    assert(m.sub(Multiset::empty().insert(10int)).add(Multiset::empty().insert(12int)) =~= m.remove(
        10int,
    ).insert(12int));
}

pub proof fn packed_injective(
    opt: Option<int>,
    m: Map<int, int>,
    opt2: Option<int>,
    m2: Map<int, int>,
)
    requires
        packed(opt, m) == packed(opt2, m2),
    ensures
        opt == opt2,
        m == m2,
{
    assert(m =~= m2) by {
        assert forall|k: int| m.dom().contains(k) == m2.dom().contains(k) by {
            packed_map_at(opt, m, k);
            packed_map_at(opt2, m2, k);
        }
        assert forall|k: int| m.dom().contains(k) implies m[k] == m2[k] by {
            packed_map_at(opt, m, k);
            packed_map_at(opt2, m2, k);
        }
    }
    if opt is Some {
        packed_option_at(opt, m, opt->Some_0);
        packed_option_at(opt2, m2, opt->Some_0);
    } else if opt2 is Some {
        packed_option_at(opt, m, opt2->Some_0);
        packed_option_at(opt2, m2, opt2->Some_0);
    }
}

} // verus!
verified_tokenized_state_machine! {  #[verified_local_ready(tr1,tr2,tr3,tr4)] SafeY {
    fields {
        #[sharding(variable)] pub auth:Y::State,
        #[sharding(option)] pub opt:Option<int>,
        #[sharding(map)] pub map:Map<int,int>,
        #[sharding(multiset)] pub mset:Multiset<int>,
        #[sharding(storage_imap)] pub stored:IMap<StorageKey,int>,
    }
    #[invariant] pub fn exact(self)->bool {
        self.opt==self.auth.opt && self.map==self.auth.map && self.mset==self.auth.mset
        && self.stored==packed(self.auth.storage_opt,self.auth.storage_map)
    }
    init! { initialize(initial:Y::State) {
        init auth=initial;
        init opt=initial.opt;
        init map=initial.map;
        init mset=initial.mset;
        init stored=packed(initial.storage_opt,initial.storage_map);
    } }
    transition! { tr1() {
        require (|__tsm_general_bulk_raw:bool| Y::State::tr1_enabled_strong(pre.auth))(false);
        remove opt -= (Some(5int));
        add opt += (Some(8int));
        remove map -= (Map::<int,int>::empty().insert(0int,1int));
        have map >= (Map::<int,int>::empty().insert(2int,3int));
        add map += (Map::<int,int>::empty().insert(4int,5int));
        remove mset -= (Multiset::singleton(10int));
        have mset >= (Multiset::singleton(11int));
        add mset += (Multiset::singleton(12int));
        withdraw stored -= (packed(Some(13int),Map::<int,int>::empty().insert(15int,16int)));
        deposit stored += (packed(Some(14int),Map::<int,int>::empty().insert(17int,18int)));
        update auth=Y::State {
            opt:Some(8int),map:pre.auth.map.remove(0int).insert(4int,5int),
            mset:pre.auth.mset.remove(10int).insert(12int),storage_opt:Some(14int),
            storage_map:pre.auth.storage_map.remove(15int).insert(17int,18int),
        };
    } }
    transition! { tr2() {
        require Y::State::tr2_enabled_strong(pre.auth);
        have opt >= Some(7);
        add map += (Map::<int,int>::empty().insert(4int,5int));
        update auth=Y::State {map:pre.auth.map.insert(4int,5int),..pre.auth};
    } }
    transition! { tr3() {
        require Y::State::tr3_enabled_strong(pre.auth);
        remove opt -= Some(7);
        withdraw stored -= [StorageKey::OptionalValue(12int)=>12int];
        update auth=Y::State {opt:None,storage_opt:None,..pre.auth};
    } }
    transition! { tr4() {
        require Y::State::tr4_enabled_strong(pre.auth);
        add opt += Some(7);
        deposit stored += [StorageKey::OptionalValue(12int)=>12int];
        update auth=Y::State {opt:Some(7int),storage_opt:Some(12int),..pre.auth};
    } }
    #[inductive(initialize)] fn initialize_inductive(post:Self,initial:Y::State){}
    #[inductive(tr1)] fn tr1_inductive(pre:Self,post:Self) {
        normalize_map_operands(pre.map,0int,1int,4int,5int);
        normalize_bag_operands(pre.mset);
        assert(post.map==post.auth.map);
        assert(post.mset==post.auth.mset);
        assert(post.stored =~= packed(post.auth.storage_opt,post.auth.storage_map));
    }
    #[inductive(tr2)] fn tr2_inductive(pre:Self,post:Self){
        normalize_map_operands(pre.map,0int,1int,4int,5int);
        assert(post.map==post.auth.map);
    }
    #[inductive(tr3)] fn tr3_inductive(pre:Self,post:Self) {
        assert(post.stored =~= packed(post.auth.storage_opt,post.auth.storage_map));
    }
    #[inductive(tr4)] fn tr4_inductive(pre:Self,post:Self) {
        assert(post.stored =~= packed(post.auth.storage_opt,post.auth.storage_map));
    }
} }
verus! {

pub proof fn original_protocol_refinement(pre: SafeY::State, post: SafeY::State)
    requires
        pre.invariant(),
        post.invariant(),
    ensures
        SafeY::State::tr1_strong(pre, post) ==> Y::State::tr1_strong(pre.auth, post.auth),
        SafeY::State::tr2_strong(pre, post) ==> Y::State::tr2_strong(pre.auth, post.auth),
        SafeY::State::tr3_strong(pre, post) ==> Y::State::tr3_strong(pre.auth, post.auth),
        SafeY::State::tr4_strong(pre, post) ==> Y::State::tr4_strong(pre.auth, post.auth),
{
    normalize_map_operands(pre.auth.map, 0int, 1int, 4int, 5int);
    normalize_map_operands(pre.auth.storage_map, 15int, 16int, 17int, 18int);
    if SafeY::State::tr1_strong(pre, post) {
        normalize_bag_operands(pre.auth.mset);
    }
}

} // verus!
verus! {

/// The authority is owned, so every compatible completion agrees on this
/// entire original mathematical state. Storage permissions are transferred
/// separately in tracked maps below.
/// Tr4 -> tr3 -> tr4 reuses the actual permission returned by tr3. Tr2 then
/// observes Some(7) and adds logical map entry 4, preserving stored permission12.
fn main() {
    proof {
        let initial = Y::State {
            opt: Some(5int),
            map: Map::<int, int>::empty().insert(0int, 1int).insert(2int, 3int),
            mset: Multiset::empty().insert(10int).insert(11int),
            storage_opt: Some(13int),
            storage_map: Map::<int, int>::empty().insert(15int, 16int),
        };
        let tracked permission13 = 13int;
        let tracked permission16 = 16int;
        let tracked mut base: IMap<StorageKey, int> = IMap::tracked_empty();
        base.tracked_insert(StorageKey::OptionalValue(13int), permission13);
        base.tracked_insert(StorageKey::MapKey(15int), permission16);
        packed_pair(13int, 15int, 16int);
        assert(base =~= packed(initial.storage_opt, initial.storage_map));
        let tracked (inst, auth, opt, map, mset) = SafeY::Instance::initialize(initial, base);
        let tracked permission14 = 14int;
        let tracked permission18 = 18int;
        let tracked mut deposit: IMap<StorageKey, int> = IMap::tracked_empty();
        deposit.tracked_insert(StorageKey::OptionalValue(14int), permission14);
        deposit.tracked_insert(StorageKey::MapKey(17int), permission18);
        let deposited = deposit;
        packed_pair(14int, 17int, 18int);
        assert(deposited =~= packed(Some(14int), Map::<int, int>::empty().insert(17int, 18int)));
        let tracked token = inst.tr1(auth, opt, map, mset, deposit);
        let pre = token.before;
        let post = token.after;
        let tracked mut withdrawn = token.withdrawn;
        assert(pre.auth == initial);
        original_protocol_refinement(pre, post);
        assert(Y::State::tr1_strong(initial, post.auth));
        assert(post.auth.opt == Some(8int));
        assert(post.auth.map == Map::<int, int>::empty().insert(2int, 3int).insert(4int, 5int));
        assert(post.auth.mset =~= Multiset::empty().insert(11int).insert(12int));
        assert(post.auth.storage_opt == Some(14int));
        assert(post.auth.storage_map == Map::<int, int>::empty().insert(17int, 18int));
        assert(withdrawn =~= IMap::empty().insert(StorageKey::OptionalValue(13int), 13int).insert(
            StorageKey::MapKey(15int),
            16int,
        ));
        // These values come from the returned tracked map, never from a witness.
        let tracked returned13 = withdrawn.tracked_remove(StorageKey::OptionalValue(13int));
        let tracked returned16 = withdrawn.tracked_remove(StorageKey::MapKey(15int));
        assert(returned13 == 13int && returned16 == 16int);
        assert(withdrawn =~= IMap::empty());
        assert(token.auth.value() == post.auth);

    }
    proof {
        let initial = Y::State {
            opt: None,
            map: Map::<int, int>::empty(),
            mset: Multiset::empty(),
            storage_opt: None,
            storage_map: Map::<int, int>::empty(),
        };
        packed_optional(None);
        packed_optional(Some(12int));
        let tracked (inst, auth, opt, map, mset) = SafeY::Instance::initialize(
            initial,
            IMap::tracked_empty(),
        );
        let tracked permission12 = 12int;
        let tracked mut deposit: IMap<StorageKey, int> = IMap::tracked_empty();
        deposit.tracked_insert(StorageKey::OptionalValue(12int), permission12);
        let deposited = deposit;
        let tracked token = inst.tr4(auth, opt, map, mset, deposit);
        let pre = token.before;
        let post = token.after;
        assert(pre.auth == initial);
        original_protocol_refinement(pre, post);
        let populated = Y::State { opt: Some(7int), storage_opt: Some(12int), ..initial };
        assert(post.auth == populated);
        assert(token.auth.value() == populated);
        let tracked token = inst.tr3(token.auth, token.opt, token.map, token.mset);
        let pre = token.before;
        let post = token.after;
        let tracked mut withdrawn = token.withdrawn;
        assert(pre.auth == populated);
        original_protocol_refinement(pre, post);
        assert(post.auth == initial);
        assert(token.auth.value() == initial);
        assert(withdrawn =~= IMap::empty().insert(StorageKey::OptionalValue(12int), 12int));
        let tracked returned12 = withdrawn.tracked_remove(StorageKey::OptionalValue(12int));
        assert(returned12 == 12int);
        assert(withdrawn =~= IMap::empty());
        let tracked mut redeposit: IMap<StorageKey, int> = IMap::tracked_empty();
        redeposit.tracked_insert(StorageKey::OptionalValue(12int), returned12);
        let deposited_again = redeposit;
        let tracked token = inst.tr4(token.auth, token.opt, token.map, token.mset, redeposit);
        let pre = token.before;
        let post = token.after;
        assert(pre.auth == initial);
        original_protocol_refinement(pre, post);
        assert(post.auth == populated);
        assert(token.auth.value() == populated);
        let tracked token = inst.tr2(token.auth, token.opt, token.map, token.mset);
        let pre = token.before;
        let post = token.after;
        assert(pre.auth == populated);
        original_protocol_refinement(pre, post);
        assert(post.auth.opt == Some(7int));
        assert(post.auth.map == Map::<int, int>::empty().insert(4int, 5int));
        assert(post.auth.storage_opt == Some(12int));
        assert(post.auth.storage_map == Map::<int, int>::empty());
        assert(token.auth.value() == post.auth);

    }
}

} // verus!
