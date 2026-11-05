// rust_verify/tests/example.rs expect-warnings
//! Raw backend (`#[verified_raw_tokens]`) statement forms: remove/have/add
//! sequences on every monoid kind (collections, count/bool, persistent fields),
//! labeled machines, machines the straight-line emitter routes to the general
//! emitter, and the same sequences through the generic interface (merged from the
//! former raw_forms_{collections,count_bool,persistent,labels,basic_fallback,
//! generic_sequences}.rs).

// ----------------------------------------------------------------------------
// Raw backend statement forms: sequences of `remove`, `have` and `add` on one
// `set`, `multiset`, `map` or `option` field, including several removals or
// additions of the same field, general operands mixed with singletons, and
// bindings that follow removals of their source field.
pub mod collections {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::multiset::Multiset;
    use vstd::prelude::*;
    use vstd::resource::algebra::ResourceAlgebra;
    use vstd::resource::pcm::PCM;
    use vstd::resource::tsm::Machine;

    verus! {

    verified_tokenized_state_machine! {
        #[verified_raw_tokens]
        Sets {
            fields {
                #[sharding(variable)] pub auth: Set<int>,
                #[sharding(set)] pub s: Set<int>,
            }
            #[invariant] pub fn same(&self) -> bool { self.auth == self.s }
            init! { initialize() { init auth = Set::empty(); init s = Set::empty(); } }
            transition! { add_two(a: int, b: int) {
                require(a != b && !pre.auth.contains(a) && !pre.auth.contains(b));
                add s += set {a};
                add s += set {b};
                update auth = pre.auth.insert(a).insert(b);
            } }
            transition! { remove_two(a: int, b: int) {
                remove s -= set {a};
                remove s -= set {b};
                update auth = pre.auth.remove(a).remove(b);
            } }
            transition! { move_elem(a: int, b: int, c: int) {
                require(!pre.auth.contains(b) || b == a);
                remove s -= set {a};
                have s >= set {c};
                add s += set {b};
                update auth = pre.auth.remove(a).insert(b);
            } }
            transition! { general_mix(x: Set<int>, a: int, y: Set<int>) {
                require(y.disjoint(pre.auth.difference(x).remove(a)) && !y.contains(a));
                remove s -= (x);
                remove s -= set {a};
                add s += (y);
                update auth = pre.auth.difference(x).remove(a).union(y);
            } }
            #[inductive(initialize)] fn initialize_inductive(post: Self) {}
            #[inductive(add_two)] fn add_two_inductive(pre: Self, post: Self, a: int, b: int) {}
            #[inductive(remove_two)] fn remove_two_inductive(pre: Self, post: Self, a: int, b: int) {}
            #[inductive(move_elem)] fn move_elem_inductive(pre: Self, post: Self, a: int, b: int, c: int) {}
            #[inductive(general_mix)] fn general_mix_inductive(pre: Self, post: Self, x: Set<int>, a: int, y: Set<int>) {}
        }
    }
    proof fn set_history() {
        let tracked token = Sets::Protocol::initialize();
        let tracked token = Sets::Protocol::add_two(token, 1, 2);
        let tracked token = Sets::Protocol::remove_two(token, 1, 2);
    }
    verified_tokenized_state_machine! {
        #[verified_raw_tokens]
        Bags {
            fields {
                #[sharding(variable)] pub auth: Multiset<int>,
                #[sharding(multiset)] pub bag: Multiset<int>,
                #[sharding(variable)] pub mauth: Map<int, int>,
                #[sharding(map)] pub m: Map<int, int>,
            }
            #[invariant] pub fn same(&self) -> bool { self.auth == self.bag && self.mauth == self.m }
            init! { initialize() { init auth = Multiset::empty(); init bag = Multiset::empty();
                init mauth = Map::empty(); init m = Map::empty(); } }
            transition! { three_adds(a: int) {
                add bag += {a};
                add bag += {a};
                add bag += {a};
                update auth = pre.auth.insert(a).insert(a).insert(a);
            } }
            transition! { three_removes_two_adds(a: int, b: int) {
                remove bag -= {a};
                remove bag -= {a};
                remove bag -= {a};
                have bag >= {b};
                add bag += {b};
                add bag += {b};
                update auth = pre.auth.remove(a).remove(a).remove(a).insert(b).insert(b);
            } }
            transition! { map_three(k1: int, k2: int, k3: int) {
                require(k1 != k2 && k2 != k3 && k1 != k3);
                require(!pre.mauth.contains_key(k1) && !pre.mauth.contains_key(k2) && !pre.mauth.contains_key(k3));
                add m += [k1 => 1];
                add m += [k2 => 2];
                add m += [k3 => 3];
                update mauth = pre.mauth.insert(k1, 1).insert(k2, 2).insert(k3, 3);
            } }
            transition! { map_shuffle(k1: int, k2: int, k3: int) {
                require(k1 != k2);
                remove m -= [k1 => let v1];
                remove m -= [k2 => let v2];
                have m >= [k3 => let v3];
                add m += [k1 => v2];
                add m += [k2 => v1 + v3];
                update mauth = pre.mauth.insert(k1, v2).insert(k2, v1 + v3);
            } }
            #[inductive(initialize)] fn initialize_inductive(post: Self) {}
            #[inductive(three_adds)] fn three_adds_inductive(pre: Self, post: Self, a: int) {}
            #[inductive(three_removes_two_adds)] fn three_removes_two_adds_inductive(pre: Self, post: Self, a: int, b: int) {}
            #[inductive(map_three)] fn map_three_inductive(pre: Self, post: Self, k1: int, k2: int, k3: int) {}
            #[inductive(map_shuffle)] fn map_shuffle_inductive(pre: Self, post: Self, k1: int, k2: int, k3: int) {
                assert(post.mauth =~= post.m);
            }
        }
    }
    proof fn bag_history() {
        let tracked token = Bags::Protocol::initialize();
        let tracked token = Bags::Protocol::three_adds(token, 5);
        let tracked token = Bags::Protocol::map_three(token, 1, 2, 3);
        let tracked token = Bags::Protocol::map_shuffle(token, 1, 2, 3);
        assert(token.fragment().mauth->Some_0->Exclusive_0[2] == 4);
    }

    verified_tokenized_state_machine! {
        #[verified_raw_tokens]
        Opts {
            fields {
                #[sharding(variable)] pub auth: Option<int>,
                #[sharding(option)] pub o: Option<int>,
                #[sharding(option)] pub p: Option<int>,
            }
            #[invariant] pub fn same(&self) -> bool { self.auth == self.o && self.p is None }
            init! { initialize() { init auth = None; init o = None; init p = None; } }
            transition! { put(v: int) {
                require(pre.auth is None);
                add o += Some(v);
                update auth = Some(v);
            } }
            transition! { general_two_removes(x: Option<int>, y: Option<int>) {
                require(x is None || y is None);
                remove o -= (x);
                remove o -= (y);
                update auth = if x is Some || y is Some { None } else { pre.auth };
            } }
            transition! { general_two_adds(x: Option<int>, y: Option<int>) {
                require(pre.auth is None && (x is None || y is None));
                add o += (x);
                add o += (y);
                update auth = if y is Some { y } else { x };
            } }
            transition! { replace_have(v: int) {
                remove o -= Some(let old);
                have p >= (None);
                add o += Some(old + v);
                update auth = Some(old + v);
            } }
            #[inductive(initialize)] fn initialize_inductive(post: Self) {}
            #[inductive(put)] fn put_inductive(pre: Self, post: Self, v: int) {}
            #[inductive(general_two_removes)] fn general_two_removes_inductive(pre: Self, post: Self, x: Option<int>, y: Option<int>) {}
            #[inductive(general_two_adds)] fn general_two_adds_inductive(pre: Self, post: Self, x: Option<int>, y: Option<int>) {}
            #[inductive(replace_have)] fn replace_have_inductive(pre: Self, post: Self, v: int) {}
        }
    }
    proof fn option_history() {
        let tracked token = Opts::Protocol::initialize();
        let tracked token = Opts::Protocol::put(token, 3);
        let tracked token = Opts::Protocol::replace_have(token, 4);
        assert(token.fragment().auth->Some_0->Exclusive_0 == Some(7int));
    }

    } // verus!
}

// ----------------------------------------------------------------------------
// Raw backend statement forms: sequences of `remove`, `have` and `add` on one
// `count` or `bool` field (in the trusted order remove, have, add), each
// checked as one combined resource update.
pub mod count_bool {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::prelude::*;
    use vstd::resource::algebra::ResourceAlgebra;
    use vstd::resource::pcm::PCM;
    use vstd::resource::tsm::Machine;

    verus! {

    verified_tokenized_state_machine! {
        #[verified_raw_tokens]
        Counts {
            fields {
                #[sharding(variable)] pub total: nat,
                #[sharding(count)] pub c: nat,
            }
            #[invariant] pub fn same(&self) -> bool { self.total == self.c }
            init! { initialize() { init total = 10; init c = 10; } }
            transition! { take_two_steps(a: nat, b: nat) {
                remove c -= (a);
                remove c -= (b);
                update total = (pre.total - a - b) as nat;
            } }
            transition! { give_two_steps(a: nat, b: nat) {
                add c += (a);
                add c += (b);
                update total = pre.total + a + b;
            } }
            transition! { exchange(a: nat, b: nat, k: nat) {
                remove c -= (a);
                have c >= (k);
                have c >= (k);
                add c += (b);
                update total = (pre.total - a + b) as nat;
            } }
            transition! { exchange_many(a: nat, a2: nat, b: nat, b2: nat) {
                remove c -= (a);
                remove c -= (a2);
                add c += (b);
                add c += (b2);
                update total = (pre.total - a - a2 + b + b2) as nat;
            } }
            #[inductive(initialize)] fn initialize_inductive(post: Self) {}
            #[inductive(take_two_steps)] fn take_two_steps_inductive(pre: Self, post: Self, a: nat, b: nat) {}
            #[inductive(give_two_steps)] fn give_two_steps_inductive(pre: Self, post: Self, a: nat, b: nat) {}
            #[inductive(exchange)] fn exchange_inductive(pre: Self, post: Self, a: nat, b: nat, k: nat) {}
            #[inductive(exchange_many)] fn exchange_many_inductive(pre: Self, post: Self, a: nat, a2: nat, b: nat, b2: nat) {}
        }
    }
    proof fn count_history() {
        let tracked token = Counts::Protocol::initialize();
        let tracked token = Counts::Protocol::take_two_steps(token, 3, 4);
        let tracked token = Counts::Protocol::give_two_steps(token, 1, 2);
        let tracked token = Counts::Protocol::exchange_many(token, 1, 1, 5, 5);
        assert(token.fragment().total->Some_0->Exclusive_0 == 14);
    }
    verified_tokenized_state_machine! {
        #[verified_raw_tokens]
        Flags {
            fields {
                #[sharding(variable)] pub on: bool,
                #[sharding(bool)] pub flag: bool,
                #[sharding(bool)] pub other: bool,
            }
            #[invariant] pub fn same(&self) -> bool { self.on == self.flag && self.other == !self.flag }
            init! { initialize() { init on = true; init flag = true; init other = false; } }
            transition! { toggle_off() {
                remove flag -= true;
                add other += true;
                update on = false;
            } }
            transition! { cycle() {
                remove flag -= true;
                add flag += true;
            } }
            transition! { cycle_general(x: bool) {
                require(x);
                remove flag -= (x);
                add flag += (x);
            } }
            transition! { general_twice(x: bool, y: bool) {
                require(x && !y);
                remove flag -= (x);
                remove flag -= (y);
                add flag += (y);
                add flag += (x);
            } }
            #[inductive(initialize)] fn initialize_inductive(post: Self) {}
            #[inductive(toggle_off)] fn toggle_off_inductive(pre: Self, post: Self) {}
            #[inductive(cycle)] fn cycle_inductive(pre: Self, post: Self) {}
            #[inductive(cycle_general)] fn cycle_general_inductive(pre: Self, post: Self, x: bool) {}
            #[inductive(general_twice)] fn general_twice_inductive(pre: Self, post: Self, x: bool, y: bool) {}
        }
    }
    proof fn flag_history() {
        let tracked token = Flags::Protocol::initialize();
        let tracked token = Flags::Protocol::cycle(token);
        let tracked token = Flags::Protocol::cycle_general(token, true);
        let tracked token = Flags::Protocol::general_twice(token, true, false);
        let tracked token = Flags::Protocol::toggle_off(token);
        assert(token.fragment().on->Some_0->Exclusive_0 == false);
    }

    } // verus!
}

// ----------------------------------------------------------------------------
// Raw backend statement forms: repeated additions to persistent fields, each
// sequence composed by the idempotent join of the field's algebra.
pub mod persistent {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::prelude::*;
    use vstd::resource::algebra::ResourceAlgebra;
    use vstd::resource::pcm::PCM;
    use vstd::resource::tsm::Machine;

    verus! {

    verified_tokenized_state_machine! {
        #[verified_raw_tokens]
        Persist {
            fields {
                #[sharding(persistent_count)] pub hi: nat,
                #[sharding(persistent_bool)] pub done: bool,
                #[sharding(persistent_set)] pub seen: Set<int>,
                #[sharding(persistent_map)] pub log: Map<int, int>,
                #[sharding(persistent_option)] pub first: Option<int>,
            }
            init! { initialize() { init hi = 0; init done = false; init seen = Set::empty();
                init log = Map::empty(); init first = None; } }
            transition! { raise_twice(a: nat, b: nat) {
                add hi (union)= (a);
                add hi (union)= (b);
                have hi >= (a);
            } }
            transition! { finish_twice() {
                add done (union)= true;
                add done (union)= true;
            } }
            transition! { see_two(a: int, b: int) {
                have seen >= set {a};
                add seen (union)= set {a};
                add seen (union)= set {b};
            } }
            transition! { log_two(k: int, v: int, k2: int) {
                require(k != k2);
                have log >= [k => v];
                have log >= [k2 => v];
                add log (union)= [k => v];
                add log (union)= [k2 => v];
            } }
            transition! { set_first_twice(v: int) {
                have first >= Some(v);
                add first (union)= Some(v);
                add first (union)= Some(v);
            } }
            #[inductive(initialize)] fn initialize_inductive(post: Self) {}
            #[inductive(raise_twice)] fn raise_twice_inductive(pre: Self, post: Self, a: nat, b: nat) {}
            #[inductive(finish_twice)] fn finish_twice_inductive(pre: Self, post: Self) {}
            #[inductive(see_two)] fn see_two_inductive(pre: Self, post: Self, a: int, b: int) {}
            #[inductive(log_two)] fn log_two_inductive(pre: Self, post: Self, k: int, v: int, k2: int) {}
            #[inductive(set_first_twice)] fn set_first_twice_inductive(pre: Self, post: Self, v: int) {}
        }
    }
    proof fn persistent_history() {
        let tracked token = Persist::Protocol::initialize();
        let tracked token = Persist::Protocol::raise_twice(token, 0, 0);
        let tracked token = Persist::Protocol::finish_twice(token);
        assert(token.fragment().done.count >= 1);
    }


    } // verus!
}

// ----------------------------------------------------------------------------
// Raw backend statement forms: labeled machines. Init and transition labels
// are ordinary first parameters of the generated relations and operations.
pub mod labels {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::prelude::*;
    use vstd::resource::algebra::ResourceAlgebra;
    use vstd::resource::pcm::PCM;
    use vstd::resource::tsm::Machine;

    verus! {

    verified_tokenized_state_machine! {
        #[verified_raw_tokens]
        Labeled {
            fields {
                #[sharding(variable)] pub number: int,
                #[sharding(count)] pub ticks: nat,
            }
            pub struct InitLabel { pub start: int }
            pub enum Label { Add { n: int }, Tick }
            #[invariant] pub fn even(&self) -> bool { self.number % 2 == 0 }
            init! { initialize(label: InitLabel) {
                require(label.start % 2 == 0);
                init number = label.start;
                init ticks = 0;
            } }
            transition! { add(label: Label, n: int) {
                require(label == Label::Add { n } && n % 2 == 0);
                update number = pre.number + n;
            } }
            transition! { tick(label: Label) {
                require(label is Tick);
                add ticks += (1);
            } }
            #[inductive(initialize)] fn initialize_inductive(post: Self, label: InitLabel) {}
            #[inductive(add)] fn add_inductive(pre: Self, post: Self, label: Label, n: int) {}
            #[inductive(tick)] fn tick_inductive(pre: Self, post: Self, label: Label) {}
        }
    }
    proof fn labeled_history() {
        let tracked token = Labeled::Protocol::initialize(Labeled::InitLabel { start: 4 });
        let tracked token = Labeled::Protocol::add(token, Labeled::Label::Add { n: 2 }, 2);
        let tracked token = Labeled::Protocol::tick(token, Labeled::Label::Tick);
        assert(token.fragment().number->Some_0->Exclusive_0 == 6);
    }

    } // verus!
}

// ----------------------------------------------------------------------------
// Raw backend statement forms over the straight-line backend's field kinds
// (variable, constant, count, not_tokenized, storage_option) that it does not
// itself support: `have` before `add`, updates of not_tokenized fields, two
// optional stores, and several storage operations on one path. These machines
// are generated by the general backend.
pub mod basic_fallback {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::prelude::*;
    use vstd::resource::algebra::ResourceAlgebra;
    use vstd::resource::pcm::PCM;
    use vstd::resource::tsm::Machine;

    verus! {

    pub struct Tok { pub v: int }
    // Variable, constant, count and storage_option fields only: the straight-line backend's kinds.
    verified_tokenized_state_machine! {
        #[verified_raw_tokens]
        Basic {
            fields {
                #[sharding(constant)] pub limit: nat,
                #[sharding(variable)] pub held: Option<Tok>,
                #[sharding(variable)] pub held2: Option<Tok>,
                #[sharding(count)] pub c: nat,
                #[sharding(not_tokenized)] pub hidden: int,
                #[sharding(storage_option)] pub cell: Option<Tok>,
                #[sharding(storage_option)] pub cell2: Option<Tok>,
            }
            #[invariant] pub fn same(&self) -> bool { self.held == self.cell && self.held2 == self.cell2  }
            init! { initialize(limit: nat) {
                init limit = limit; init held = None; init held2 = None; init c = 0; init hidden = 0;
                init cell = None; init cell2 = None;
            } }
            transition! { count_have_before_add(a: nat) {
                have c >= (a);
                add c += (1);
            } }
            transition! { bump_hidden() {
                update hidden = 3;
            } }
            transition! { put_both(a: Tok, b: Tok) {
                require(pre.held is None && pre.held2 is None);
                deposit cell += Some(a);
                deposit cell2 += Some(b);
                update held = Some(a);
                update held2 = Some(b);
            } }
            transition! { take_both(a: Tok, b: Tok) {
                require(pre.held == Some(a) && pre.held2 == Some(b));
                withdraw cell -= Some(a);
                withdraw cell2 -= Some(b);
                update held = None;
                update held2 = None;
            } }
            transition! { swap_cells(a: Tok) {
                require(pre.held == Some(a) && pre.held2 is None);
                withdraw cell -= Some(a);
                deposit cell2 += Some(a);
                update held = None;
                update held2 = Some(a);
            } }
            #[inductive(initialize)] fn initialize_inductive(post: Self, limit: nat) {}
            #[inductive(count_have_before_add)] fn count_have_before_add_inductive(pre: Self, post: Self, a: nat) {}
            #[inductive(bump_hidden)] fn bump_hidden_inductive(pre: Self, post: Self) {}
            #[inductive(put_both)] fn put_both_inductive(pre: Self, post: Self, a: Tok, b: Tok) {}
            #[inductive(take_both)] fn take_both_inductive(pre: Self, post: Self, a: Tok, b: Tok) {}
            #[inductive(swap_cells)] fn swap_cells_inductive(pre: Self, post: Self, a: Tok) {}
        }
    }
    proof fn basic_history(tracked a: Tok, tracked b: Tok) {
        // The storage is one `IMap<__StorageKey, __StorageValue>`, tagged by field.
        assert forall|s: Basic::State| Basic::State::initialize_strong(s, 3)
            implies IMap::<Basic::__StorageKey, Basic::__StorageValue>::empty() == s.__storage() by {
            assert(IMap::<Basic::__StorageKey, Basic::__StorageValue>::empty() =~= s.__storage());
        }
        let tracked token = Basic::Protocol::initialize(IMap::tracked_empty(), 3);
        let tracked token = Basic::Protocol::count_have_before_add(token, 0);
        let tracked token = Basic::Protocol::bump_hidden(token);
        let ghost f = token.fragment();
        let tracked mut d = IMap::tracked_empty();
        d.tracked_insert(Basic::__StorageKey::cell, Basic::__StorageValue::cell(a));
        d.tracked_insert(Basic::__StorageKey::cell2, Basic::__StorageValue::cell2(b));
        assert forall|z: Basic::Fragment, pre: Basic::State|
            pre.invariant() && Basic::Fragment::op(Basic::Fragment::op(f, Basic::Fragment::unit()), z)
                == Basic::Protocol::embed(pre)
            implies Basic::State::put_both_deposited(pre, a, b) == d by {
            assert(Basic::State::put_both_deposited(pre, a, b) =~= d);
        }
        let tracked token = Basic::Protocol::put_both(token, d, a, b);
        let tracked (token, w) = Basic::Protocol::take_both(token, a, b);
        assert(w.contains_key(Basic::__StorageKey::cell));
    }


    } // verus!
}

// ----------------------------------------------------------------------------
// Raw backend statement forms through the generic interface: several
// removals and additions of one set or map field, and several deposits into
// and withdrawals from one storage map, in a single transition. The generic
// operations call the raw ones, which check each path as one exchange.
pub mod generic_sequences {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::prelude::*;
    use vstd::tokens::*;

    verified_tokenized_state_machine! {
        #[verified_generic_tokens]
        G {
            fields {
                #[sharding(set)] pub unused: Set<int>,
                #[sharding(map)] pub owner: Map<int, int>,
                #[sharding(storage_map)] pub left: Map<int, int>,
                #[sharding(storage_map)] pub right: Map<int, int>,
            }
            #[invariant]
            pub fn inv(&self) -> bool {
                &&& forall|k: int| #[trigger] self.owner.dom().contains(k) <==> self.left.dom().contains(k)
                &&& forall|k: int| #[trigger] self.owner.dom().contains(k) ==> self.left[k] == self.owner[k]
                &&& forall|k: int| #[trigger] self.unused.contains(k) ==> !self.owner.dom().contains(k)
            }
            init!{ initialize(free: Set<int>) {
                init unused = free; init owner = Map::empty(); init left = Map::empty(); init right = Map::empty();
            } }
            transition!{ insert_two(k: int, j: int, v: int) {
                remove unused -= set { k };
                remove unused -= set { j };
                add owner += [k => v];
                add owner += [j => v];
                deposit left += [k => v];
                deposit left += [j => v];
            } }
            transition!{ take_two(k: int, j: int) {
                remove owner -= [k => let v];
                remove owner -= [j => let w];
                withdraw left -= [k => v];
                withdraw left -= [j => w];
                add unused += set { k };
                add unused += set { j };
            } }
            #[inductive(initialize)] fn initialize_inductive(post: Self, free: Set<int>) {}
            #[inductive(insert_two)] fn insert_two_inductive(pre: Self, post: Self, k: int, j: int, v: int) {
                assert forall|x: int| #[trigger] post.owner.dom().contains(x) ==> post.left[x] == post.owner[x] by {
                    if x == k || x == j {} else {}
                }
            }
            #[inductive(take_two)] fn take_two_inductive(pre: Self, post: Self, k: int, j: int) {}
        }
    }
    verus! {

    proof fn client() {
        let free = Set::<int>::empty().insert(1).insert(2);
        let tracked (Tracked(inst), Tracked(unused), Tracked(owner)) =
            G::Instance::initialize(free, Map::tracked_empty(), Map::tracked_empty());
        let tracked mut unused = unused;
        let tracked u1 = unused.remove(1);
        let tracked u2 = unused.remove(2);
        let tracked (Tracked(o1), Tracked(o2)) = inst.insert_two(1, 2, 7, u1, u2, 7, 7);
        assert(o1.key() == 1 && o2.key() == 2 && o1.value() == 7);
        let tracked (Tracked(u1), Tracked(u2), Tracked(l1), Tracked(l2)) = inst.take_two(1, 2, o1, o2);
        assert(l1 == 7 && l2 == 7 && u1.element() == 1 && u2.element() == 2);
    }

    }
}

fn main() {
}
