//! Borrowed token collections of the finite strategies (`have f >= (e)` on
//! `map`, `set`, `multiset`, `option`, `bool` and their persistent variants),
//! after rust_verify_test `relation_codegen_special_general_finite`.
//!
//! The tokens of the borrowed part `e` are observed one by one through the
//! `borrow` accessors of `vstd::tokens::MapToken`/`SetToken`/`MultisetToken`
//! (and of `Option`), and their joined observation fixes each element. A
//! borrowed multiset part must not contain an element twice: two shared
//! references to tokens do not show that the tokens are distinct resources.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::multiset::Multiset;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    B {
        fields {
            #[sharding(option)]
            pub opt: Option<int>,

            #[sharding(map)]
            pub map: Map<int, int>,

            #[sharding(set)]
            pub set: Set<int>,

            #[sharding(multiset)]
            pub mset: Multiset<int>,

            #[sharding(bool)]
            pub flag: bool,

            #[sharding(persistent_map)]
            pub pmap: Map<int, int>,

            #[sharding(persistent_set)]
            pub pset: Set<int>,

            #[sharding(persistent_option)]
            pub popt: Option<int>,

            #[sharding(persistent_bool)]
            pub pflag: bool,

            #[sharding(variable)]
            pub counter: nat,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            &&& self.opt == Some(5int)
            &&& self.map == Map::<int, int>::empty().insert(1, 10).insert(2, 20)
            &&& self.set == Set::<int>::empty().insert(3).insert(4)
            &&& self.mset == Multiset::<int>::empty().insert(7).insert(8)
            &&& self.flag
            &&& self.pmap == Map::<int, int>::empty().insert(1, 11)
            &&& self.pset == Set::<int>::empty().insert(6)
            &&& self.popt == Some(9int)
            &&& self.pflag
        }

        init!{
            initialize() {
                init opt = Some(5);
                init map = Map::empty().insert(1, 10).insert(2, 20);
                init set = Set::empty().insert(3).insert(4);
                init mset = Multiset::empty().insert(7).insert(8);
                init flag = true;
                init pmap = Map::empty().insert(1, 11);
                init pset = Set::empty().insert(6);
                init popt = Some(9);
                init pflag = true;
                init counter = 0;
            }
        }

        // Read-only: only borrowed collections.
        property!{
            observe_all() {
                have opt >= (Option::<int>::Some(5));
                have map >= (Map::<int, int>::empty().insert(1, 10).insert(2, 20));
                have set >= (Set::<int>::empty().insert(3));
                have mset >= (Multiset::<int>::empty().insert(7).insert(8));
                have flag >= (true);
                have pmap >= (Map::<int, int>::empty().insert(1, 11));
                have pset >= (Set::<int>::empty().insert(6));
                have popt >= (Option::<int>::Some(9));
                have pflag >= (true);
                assert(Set::<int>::empty().insert(3).contains(3));
            }
        }

        // Empty borrowed parts: nothing is observed.
        property!{
            observe_empty() {
                have map >= (Map::<int, int>::empty());
                have opt >= (Option::<int>::None);
                assert(Map::<int, int>::empty().dom().len() == 0);
            }
        }

        // A mutating operation whose only token inputs are borrowed collections.
        transition!{
            count(m: Map<int, int>) {
                have map >= (m);
                update counter = pre.counter + m.dom().len();
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(count)]
        fn count_inductive(pre: Self, post: Self, m: Map<int, int>) { }
    }
}

verus! {

proof fn client() {
    let tracked (Tracked(inst), Tracked(opt), Tracked(map), Tracked(set), Tracked(mset),
        Tracked(flag), Tracked(pmap), Tracked(pset), Tracked(popt), Tracked(pflag), Tracked(counter)) =
        B::Instance::initialize();
    assert(map.map() =~= Map::<int, int>::empty().insert(1, 10).insert(2, 20));
    assert(set.set() =~= Set::<int>::empty().insert(3).insert(4));
    assert(pmap.map() =~= Map::<int, int>::empty().insert(1, 11));
    assert(pset.set() =~= Set::<int>::empty().insert(6));
    broadcast use vstd::multiset::group_multiset_axioms;
    assert(Multiset::<int>::empty().insert(7).insert(8).subset_of(mset.multiset()));
    inst.observe_all(&opt, &map, &set, &mset, &flag, &pmap, &pset, &popt, &pflag);
    inst.observe_empty(&opt, &map);
    let tracked mut counter = counter;
    let m = Map::<int, int>::empty().insert(2, 20);
    inst.count(m, &map, &mut counter);
    assert(m.dom() =~= Set::<int>::empty().insert(2));
    assert(counter.value() == 1);
}

}

fn main() {}
