//! Raw backend statement forms over several `storage_option` fields: deposits
//! into, withdrawals from and guards of two cells on one path, for cells of one
//! permission type and of different permission types (both stored as one
//! `IMap<__StorageKey, __StorageValue>`, tagged by field).
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;

verus! {

pub struct Tok {
    pub v: int,
}

pub struct Other {
    pub w: nat,
}

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    SameCells {
        fields {
            #[sharding(variable)] pub vals: Option<(Tok, Tok)>,
            #[sharding(storage_option)] pub left: Option<Tok>,
            #[sharding(storage_option)] pub right: Option<Tok>,
        }
        #[invariant] pub fn same(&self) -> bool {
            &&& self.vals is Some ==> self.left == Some(self.vals->Some_0.0)
                && self.right == Some(self.vals->Some_0.1)
            &&& self.vals is None ==> self.left is None && self.right is None
        }
        init! { initialize() { init vals = None; init left = None; init right = None; } }
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

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    MixedCells {
        fields {
            #[sharding(variable)] pub vals: Option<(Tok, Other)>,
            #[sharding(storage_option)] pub left: Option<Tok>,
            #[sharding(storage_option)] pub right: Option<Other>,
        }
        #[invariant] pub fn same(&self) -> bool {
            &&& self.vals is Some ==> self.left == Some(self.vals->Some_0.0)
                && self.right == Some(self.vals->Some_0.1)
            &&& self.vals is None ==> self.left is None && self.right is None
        }
        init! { initialize() { init vals = None; init left = None; init right = None; } }
        transition! { fill(a: Tok, b: Other) {
            require(pre.vals is None);
            deposit left += Some(a);
            deposit right += Some(b);
            update vals = Some((a, b));
        } }
        transition! { drain(a: Tok, b: Other) {
            require(pre.vals == Some((a, b)));
            withdraw left -= Some(a);
            withdraw right -= Some(b);
            update vals = None;
        } }
        property! { both(a: Tok, b: Other) {
            require(pre.vals == Some((a, b)));
            guard left >= Some(a);
            guard right >= Some(b);
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(fill)] fn fill_inductive(pre: Self, post: Self, a: Tok, b: Other) {}
        #[inductive(drain)] fn drain_inductive(pre: Self, post: Self, a: Tok, b: Other) {}
    }
}

proof fn same_cells(tracked a: Tok, tracked b: Tok) {
    assert forall|s: SameCells::State| SameCells::State::initialize_strong(s)
        implies IMap::<SameCells::__StorageKey, SameCells::__StorageValue>::empty() == s.__storage() by {
        assert(IMap::<SameCells::__StorageKey, SameCells::__StorageValue>::empty() =~= s.__storage());
    }
    let tracked token = SameCells::Protocol::initialize(IMap::tracked_empty());
    let ghost f = token.fragment();
    let tracked mut d = IMap::tracked_empty();
    d.tracked_insert(SameCells::__StorageKey::left, SameCells::__StorageValue::left(a));
    d.tracked_insert(SameCells::__StorageKey::right, SameCells::__StorageValue::right(b));
    assert forall|z: SameCells::Fragment, pre: SameCells::State|
        pre.invariant() && SameCells::Fragment::op(SameCells::Fragment::op(f, SameCells::Fragment::unit()), z)
            == SameCells::Protocol::embed(pre)
        implies SameCells::State::fill_deposited(pre, a, b) == d by {
        assert(SameCells::State::fill_deposited(pre, a, b) =~= d);
    }
    let tracked token = SameCells::Protocol::fill(token, d, a, b);
    let tracked both = SameCells::Protocol::both(&token, a, b);
    assert(both[SameCells::__StorageKey::left] == SameCells::__StorageValue::left(a)
        && both[SameCells::__StorageKey::right] == SameCells::__StorageValue::right(b));
    let ghost before = token.fragment();
    let tracked (token, mut w) = SameCells::Protocol::drain(token);
    let (pre, post, frame) = SameCells::Protocol::drain_witness(
        before, SameCells::Fragment::unit(), token.fragment(), IMap::empty(), w);
    assert(w.contains_key(SameCells::__StorageKey::left) && w[SameCells::__StorageKey::left] is left);
    let tracked a2 = SameCells::__unwrap_left(w.tracked_remove(SameCells::__StorageKey::left));
    assert(a2 == a);
}

proof fn mixed_cells(tracked a: Tok, tracked b: Other) {
    // Payloads of different types are tagged by field, as for one type.
    assert forall|s: MixedCells::State| MixedCells::State::initialize_strong(s)
        implies IMap::<MixedCells::__StorageKey, MixedCells::__StorageValue>::empty() == s.__storage() by {
        assert(IMap::<MixedCells::__StorageKey, MixedCells::__StorageValue>::empty() =~= s.__storage());
    }
    let tracked token = MixedCells::Protocol::initialize(IMap::tracked_empty());
    let ghost f = token.fragment();
    let tracked mut d = IMap::tracked_empty();
    d.tracked_insert(MixedCells::__StorageKey::left, MixedCells::__StorageValue::left(a));
    d.tracked_insert(MixedCells::__StorageKey::right, MixedCells::__StorageValue::right(b));
    assert forall|z: MixedCells::Fragment, pre: MixedCells::State|
        pre.invariant() && MixedCells::Fragment::op(MixedCells::Fragment::op(f, MixedCells::Fragment::unit()), z)
            == MixedCells::Protocol::embed(pre)
        implies MixedCells::State::fill_deposited(pre, a, b) == d by {
        assert(MixedCells::State::fill_deposited(pre, a, b) =~= d);
    }
    let tracked token = MixedCells::Protocol::fill(token, d, a, b);
    let ghost before = token.fragment();
    let tracked (token, mut w) = MixedCells::Protocol::drain(token, a, b);
    let (pre, post, frame) = MixedCells::Protocol::drain_witness(
        before, MixedCells::Fragment::unit(), token.fragment(), IMap::empty(), w, a, b);
    assert(w.contains_key(MixedCells::__StorageKey::right) && w[MixedCells::__StorageKey::right] is right);
    let tracked b2 = MixedCells::__unwrap_right(w.tracked_remove(MixedCells::__StorageKey::right));
    assert(b2 == b);
}

fn main() {}

} // verus!
