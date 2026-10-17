//! Raw backend statement forms with local readiness: two deposits, and a
//! withdrawal followed by a deposit at another key, in `#[verified_local_ready]`
//! transitions; and an index update of a variable field.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;

verus! {

pub struct Tok { pub v: int }
pub struct Pair { pub a: int, pub b: int }
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    #[verified_local_ready(put_two, swap)]
    SubUp {
        fields {
            #[sharding(variable)] pub pair: Pair,
            #[sharding(variable)] pub m: Map<int, int>,
            #[sharding(variable)] pub auth: Map<nat, Tok>,
            #[sharding(storage_map)] pub stored: Map<nat, Tok>,
        }
        #[invariant] pub fn same(&self) -> bool { self.auth == self.stored }
        init! { initialize() { init pair = Pair { a: 0, b: 0 }; init m = Map::empty();
            init auth = Map::empty(); init stored = Map::empty(); } }
        transition! { set_key(k: int, x: int) {
            require(pre.m.dom().contains(k));
            update m[k] = x;
        } }
        transition! { put_two(a: Tok, b: Tok) {
            require(!pre.auth.contains_key(1nat) && !pre.auth.contains_key(2nat));
            deposit stored += [1nat => a] by { };
            deposit stored += [2nat => b];
            update auth = pre.auth.insert(1nat, a).insert(2nat, b);
        } }
        transition! { swap(a: Tok, b: Tok) {
            require(pre.auth.contains_key(1nat) && pre.auth[1nat] == a && !pre.auth.contains_key(3nat));
            withdraw stored -= [1nat => a];
            deposit stored += [3nat => b];
            update auth = pre.auth.remove(1nat).insert(3nat, b);
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(set_key)] fn set_key_inductive(pre: Self, post: Self, k: int, x: int) {}
        #[inductive(put_two)] fn put_two_inductive(pre: Self, post: Self, a: Tok, b: Tok) {}
        #[inductive(swap)] fn swap_inductive(pre: Self, post: Self, a: Tok, b: Tok) {}
    }
}
proof fn client(tracked a: Tok, tracked b: Tok, tracked c: Tok) {
    assert(IMap::<nat, Tok>::empty() =~= Map::<nat, Tok>::empty().to_imap());
    let tracked token = SubUp::Protocol::initialize(IMap::tracked_empty());
    let tracked mut d = IMap::tracked_empty();
    d.tracked_insert(1nat, a);
    d.tracked_insert(2nat, b);
    assert(d =~= IMap::empty().insert(1nat, a).union_prefer_right(IMap::empty().insert(2nat, b)));
    let tracked token = SubUp::Protocol::put_two_local(token, d, a, b);
    let tracked mut d = IMap::tracked_empty();
    d.tracked_insert(3nat, c);
    assert(d =~= IMap::empty().insert(3nat, c));
    let tracked (token, mut w) = SubUp::Protocol::swap_local(token, d, a, c);
    let tracked a2 = w.tracked_remove(1nat);
    assert(a2 == a);
}
fn main() {}

} // verus!
