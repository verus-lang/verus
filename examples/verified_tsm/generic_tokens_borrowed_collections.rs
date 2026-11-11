//! Borrowed token collections (`have f >= (e)`) on the generic interface: the
//! finite strategies, observed token by token through `borrow`, and borrowed
//! parts of a `multiset` field (the counterpart of
//! negative/generic_tokens_multiset_repeated_borrow.rs).

// ----------------------------------------------------------------------------
// Borrowed token collections of the finite strategies (`have f >= (e)` on
// `map`, `set`, `multiset`, `option`, `bool` and their persistent variants),
// after rust_verify_test `relation_codegen_special_general_finite`.
//
// The tokens of the borrowed part `e` are observed one by one through the
// `borrow` accessors of `vstd::tokens::MapToken`/`SetToken`/`MultisetToken`
// (and of `Option`), and their joined observation fixes each element. A
// borrowed multiset part must not contain an element twice: two shared
// references to tokens do not show that the tokens are distinct resources.
pub mod finite {
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
}

// ----------------------------------------------------------------------------
// Borrowed parts of a `multiset` field on the generic interface.
//
// A borrowed token collection (`have f >= (e)`) is observed token by token
// through `MultisetToken::borrow`. Shared references to two tokens of one
// element do not show that the tokens are distinct resources, so the joined
// observation shows each element of `e` at least once, not its multiplicity.
// The borrowed part `e` must therefore not contain an element twice. A
// machine states this with a `require` (`spread` below); without one, the
// generated operation reports the diagnostic
// "the borrowed part of multiset field `..` must not contain an element twice"
// at the `have` statement (see
// `negative/generic_tokens_multiset_repeated_borrow.rs`).
//
// Separate singleton borrows (`have f >= {x}; have f >= {y}`) require each
// element once (the model reads `count(x) >= 1` and `count(y) >= 1`), so
// they need no such condition, also for `x == y`.
pub mod multiset {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::multiset::Multiset;
    use vstd::prelude::*;
    use vstd::tokens::*;

    verified_tokenized_state_machine! {
        Bag {
            fields {
                #[sharding(variable)]
                pub bound: int,

                #[sharding(multiset)]
                pub items: Multiset<int>,
            }

            #[invariant]
            pub fn inv(&self) -> bool {
                forall|x: int| #[trigger] self.items.count(x) > 0 ==> x < self.bound
            }

            init!{
                initialize(bound: int) {
                    init bound = bound;
                    init items = Multiset::empty();
                }
            }

            transition!{
                put(x: int) {
                    require(x < pre.bound);
                    add items += { x };
                }
            }

            // A borrowed part without repeated elements: every element is below
            // the bound.
            property!{
                spread(e: Multiset<int>) {
                    require(forall|x: int| #[trigger] e.count(x) <= 1);
                    have items >= (e);
                    assert(forall|x: int| #[trigger] e.count(x) > 0 ==> x < pre.bound) by {
                        broadcast use vstd::multiset::group_multiset_axioms;
                    };
                }
            }

            // Two singleton borrows, possibly of one element.
            property!{
                pair(x: int, y: int) {
                    have items >= { x };
                    have items >= { y };
                    assert(x < pre.bound && y < pre.bound) by {
                        broadcast use vstd::multiset::group_multiset_axioms;
                    };
                }
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self, bound: int) {
                broadcast use vstd::multiset::group_multiset_axioms;
            }

            #[inductive(put)]
            fn put_inductive(pre: Self, post: Self, x: int) {
                broadcast use vstd::multiset::group_multiset_axioms;
                assert forall|y: int| #[trigger] post.items.count(y) > 0 implies y < post.bound by {
                    if y != x { assert(pre.items.count(y) > 0); }
                }
            }
        }
    }

    verus! {

    proof fn client() {
        broadcast use vstd::multiset::group_multiset_axioms;
        let tracked (Tracked(inst), Tracked(bound), Tracked(items)) = Bag::Instance::initialize(10);
        let tracked a1 = inst.put(3, &bound);
        let tracked a2 = inst.put(3, &bound);
        let tracked b = inst.put(5, &bound);
        // Two tokens of the element 3.
        inst.pair(3, 3, &bound, &a1, &a2);
        let tracked mut all = items;
        all.insert(a1);
        all.insert(a2);
        all.insert(b);
        assert(all.multiset() =~= Multiset::empty().insert(3).insert(3).insert(5));
        let e = Multiset::empty().insert(3).insert(5);
        assert(e.subset_of(all.multiset()));
        assert(e.count(3) == 1 && e.count(5) == 1);
        assert forall|x: int| #[trigger] e.count(x) <= 1 by {
            if x != 3 && x != 5 { assert(e.count(x) == 0); }
        }
        inst.spread(e, &bound, &all);
        assert(e.count(5) > 0);
        assert(5 < bound.value());
    }

    }
}

fn main() {
}
