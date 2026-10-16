//! Raw backend statement forms: sequences of `remove`, `have` and `add` on one
//! `set`, `multiset`, `map` or `option` field, including several removals or
//! additions of the same field, general operands mixed with singletons, and
//! bindings that follow removals of their source field.
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
fn main() {}

} // verus!
