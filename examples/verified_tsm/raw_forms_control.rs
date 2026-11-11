//! Raw backend statement forms: `let`, `require let`, `assert let`, `match` and
//! `if` around storage and monoid operations, `birds_eye`, a `readonly!`
//! transition and a `property!` combining `have` with `guard`. Unlike the
//! trusted macro, the raw backend accepts monoid and storage operations inside
//! conditionals; a path that only removes or only adds uses the unit for the
//! other part of the field's effect.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;

verus! {

pub struct Tok { pub v: int }
pub enum Cmd { Put(int), Take, Nop }
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    Control {
        fields {
            #[sharding(variable)] pub auth: Map<int, Tok>,
            #[sharding(storage_map)] pub stored: Map<int, Tok>,
            #[sharding(variable)] pub n: int,
            #[sharding(constant)] pub k: int,
            #[sharding(count)] pub c: nat,
            #[sharding(multiset)] pub bag: Multiset<int>,
            #[sharding(not_tokenized)] pub ghosty: int,
        }
        #[invariant] pub fn same(&self) -> bool { self.auth == self.stored }
        init! { initialize(k: int) {
            init auth = Map::empty(); init stored = Map::empty(); init k = k; init c = 0;
            init bag = Multiset::empty(); init ghosty = 0;
            if k > 0 { init n = 1; } else { init n = 0; }
        } }
        transition! { branchy(cmd: Cmd, t: Tok) {
            let key = pre.k + 1;
            require let Some(m) = Some(pre.n);
            match cmd {
                Cmd::Put(v) => {
                    require(!pre.auth.contains_key(key));
                    deposit stored += [key => t];
                    update auth = pre.auth.insert(key, t);
                    update n = m + v;
                }
                Cmd::Take => {
                    require(pre.auth.contains_key(key) && pre.auth[key] == t);
                    withdraw stored -= [key => t];
                    update auth = pre.auth.remove(key);
                }
                Cmd::Nop => {}
            }
            if pre.n > 5 { add c += (1); } else { add bag += {pre.n}; }
            assert(pre.auth.dom().finite() || true);
        } }
        transition! { birds(x: int) {
            birds_eye let g = pre.ghosty;
            update ghosty = g + x;
            assert let Some(y) = Some(x);
            update n = y;
        } }
        readonly! { look(key: int, t: Tok) {
            require(pre.auth.contains_key(key) && pre.auth[key] == t);
            have bag >= {key};
            guard stored >= [key => t];
        } }
        property! { have_and_guard(key: int, t: Tok) {
            require(pre.auth.contains_key(key) && pre.auth[key] == t);
            have c >= (1);
            guard stored >= [key => t];
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, k: int) {}
        #[inductive(branchy)] fn branchy_inductive(pre: Self, post: Self, cmd: Cmd, t: Tok) {}
        #[inductive(birds)] fn birds_inductive(pre: Self, post: Self, x: int) {}
    }
}
proof fn control_history() {
    // The storage is one `IMap<__StorageKey, __StorageValue>`: here the tagged
    // `storage_map` field's map, `__tag_stored(s.stored.to_imap())`.
    let tracked base = IMap::tracked_empty();
    assert forall|s: Control::State| Control::State::initialize_strong(s, 0)
        implies base == s.__storage() by {
        assert(base =~= s.__storage());
    }
    let tracked token = Control::Protocol::initialize(base, 0);
    let tracked token = Control::Protocol::birds(token, 7);
    assert(token.fragment().n->Some_0->Exclusive_0 == 7);
}

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    Branchy {
        fields {
            #[sharding(variable)] pub auth: Set<int>,
            #[sharding(set)] pub s: Set<int>,
            #[sharding(variable)] pub total: nat,
            #[sharding(count)] pub c: nat,
        }
        #[invariant] pub fn same(&self) -> bool { self.auth == self.s && self.total == self.c }
        init! { initialize() { init auth = Set::empty(); init s = Set::empty(); init total = 0; init c = 0; } }
        transition! { maybe_replace(flag: bool, a: int, b: int) {
            require(!pre.auth.contains(b) && a != b);
            if flag {
                remove s -= set {a};
                update auth = pre.auth.remove(a).insert(b);
            } else {
                update auth = pre.auth.insert(b);
            }
            add s += set {b};
        } }
        transition! { pick(flag: bool, n: nat) {
            if flag {
                remove c -= (n);
                update total = (pre.total - n) as nat;
            } else {
                add c += (n);
                add c += (1);
                update total = pre.total + n + 1;
            }
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(maybe_replace)] fn maybe_replace_inductive(pre: Self, post: Self, flag: bool, a: int, b: int) {}
        #[inductive(pick)] fn pick_inductive(pre: Self, post: Self, flag: bool, n: nat) {}
    }
}
proof fn branchy_history() {
    let tracked token = Branchy::Protocol::initialize();
    let tracked token = Branchy::Protocol::maybe_replace(token, false, 0, 1);
    let tracked token = Branchy::Protocol::maybe_replace(token, true, 1, 2);
    let tracked token = Branchy::Protocol::pick(token, false, 3);
    let tracked token = Branchy::Protocol::pick(token, true, 2);
    assert(token.fragment().total->Some_0->Exclusive_0 == 2);
}
fn main() {}

} // verus!
