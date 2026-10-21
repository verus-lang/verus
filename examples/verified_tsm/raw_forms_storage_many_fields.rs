// Regression (df5c0980d): storage reasoning that scales with the number of storage
// fields, on the raw interface.
//! Raw backend storage with many (nine) storage fields. The raw protocol's
//! storage is one `IMap<__StorageKey, __StorageValue>`, tagged by field, as for
//! any number of storage fields (`raw_forms_storage_option.rs`); with a map
//! field among them, it is defined per key (`State::__storage_dom`/
//! `__storage_val`).
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;

verus! {

pub struct Tok {
    pub v: int,
}

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    ManyCells {
        fields {
            #[sharding(variable)] pub vals: Option<(Tok, Tok)>,
            #[sharding(storage_option)] pub left: Option<Tok>,
            #[sharding(storage_option)] pub c1: Option<Tok>,
            #[sharding(storage_option)] pub c2: Option<Tok>,
            #[sharding(storage_option)] pub c3: Option<Tok>,
            #[sharding(storage_option)] pub c4: Option<Tok>,
            #[sharding(storage_option)] pub c5: Option<Tok>,
            #[sharding(storage_option)] pub c6: Option<Tok>,
            #[sharding(storage_map)] pub m7: Map<int, Tok>,
            #[sharding(storage_option)] pub right: Option<Tok>,
        }
        #[invariant] pub fn same(&self) -> bool {
            &&& self.vals is Some ==> self.left == Some(self.vals->Some_0.0)
                && self.right == Some(self.vals->Some_0.1)
            &&& self.vals is None ==> self.left is None && self.right is None
        }
        init! { initialize() {
            init vals = None;
            init left = None;
            init c1 = None;
            init c2 = None;
            init c3 = None;
            init c4 = None;
            init c5 = None;
            init c6 = None;
            init m7 = Map::empty();
            init right = None;
        } }
        transition! { fill(a: Tok, b: Tok) {
            require(pre.vals is None);
            deposit left += Some(a);
            deposit right += Some(b);
            update vals = Some((a, b));
        } }
        transition! { drain() {
            require(pre.vals is Some);
            withdraw left -= Some(let _a);
            withdraw right -= Some(let _b);
            update vals = None;
        } }
        property! { both(a: Tok, b: Tok) {
            require(pre.vals == Some((a, b)));
            guard left >= Some(a);
            guard right >= Some(b);
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(fill)] fn fill_inductive(pre: Self, post: Self, a: Tok, b: Tok) {}
        #[inductive(drain)] fn drain_inductive(pre: Self, post: Self) {}
    }
}

proof fn many_cells(tracked a: Tok, tracked b: Tok) {
    assert forall|s: ManyCells::State| ManyCells::State::initialize_strong(s)
        implies IMap::<ManyCells::__StorageKey, ManyCells::__StorageValue>::empty() == s.__storage() by {
        assert(IMap::<ManyCells::__StorageKey, ManyCells::__StorageValue>::empty() =~= s.__storage());
    }
    let tracked token = ManyCells::Protocol::initialize(IMap::tracked_empty());
    let ghost f = token.fragment();
    let tracked mut d = IMap::tracked_empty();
    d.tracked_insert(ManyCells::__StorageKey::left, ManyCells::__StorageValue::left(a));
    d.tracked_insert(ManyCells::__StorageKey::right, ManyCells::__StorageValue::right(b));
    assert forall|z: ManyCells::Fragment, pre: ManyCells::State|
        pre.invariant() && ManyCells::Fragment::op(ManyCells::Fragment::op(f, ManyCells::Fragment::unit()), z)
            == ManyCells::Protocol::embed(pre)
        implies ManyCells::State::fill_deposited(pre, a, b) == d by {
        assert(ManyCells::State::fill_deposited(pre, a, b) =~= d);
    }
    let tracked token = ManyCells::Protocol::fill(token, d, a, b);
    let tracked both = ManyCells::Protocol::both(&token, a, b);
    assert(both[ManyCells::__StorageKey::left] == ManyCells::__StorageValue::left(a)
        && both[ManyCells::__StorageKey::right] == ManyCells::__StorageValue::right(b));
    let ghost before = token.fragment();
    let tracked (token, mut w) = ManyCells::Protocol::drain(token);
    let (pre, post, frame) = ManyCells::Protocol::drain_witness(
        before, ManyCells::Fragment::unit(), token.fragment(), IMap::empty(), w);
    assert(w.contains_key(ManyCells::__StorageKey::left) && w[ManyCells::__StorageKey::left] is left);
    let tracked a2 = ManyCells::__unwrap_left(w.tracked_remove(ManyCells::__StorageKey::left));
    assert(a2 == a);
}

fn main() {}

} // verus!
