//! A statement calculus for the operation proofs of `verified_tokenized_state_machine!`.
//!
//! The completion invariant of a transition's proof at statement `i` is, per field,
//! the component configuration `cfg(o, h, z, e)`: the owned fragment `o` (as the
//! ownership compiler computes it after `i` statements), the borrowed fragment `h`
//! and the completion frame `z` compose to `e`, the embedding of the field's
//! intermediate value (the frontend's `update_tmp_f` after `i` statements).
//!
//! Each lemma below is a Hoare triple of one statement form of one sharding kind:
//! its precondition is the configuration before the statement and the statement's
//! ownership condition (`remove`, `have`) or safety condition (`add`); its
//! postcondition is the statement's enabling fact on the state (`remove`, `have`;
//! with the agreement of a pattern-bound value) and the configuration after it
//! (`remove`, `add`). The states are stated in the forms the frontend's
//! `simplification` produces (`contains_pair`, `remove`, `insert`, `remove_keys`,
//! `union_prefer_right`, ...) and the fragments in the ownership compiler's forms
//! (`map_remove_many`, `op(o, map_frag(x))`, ...), so that a generated proof is a
//! sequence of lemma calls on ground terms, with no quantifier of its own.
//!
//! A machine's fragment is a product of components: its configuration splits into
//! (and joins from) the conjunction of the field configurations by `cfg_iff` on each
//! field (`cfg_split`/`cfg_join` per machine, see the tests).
use super::super::prelude::*;
use super::super::imap::IMap;
use super::super::iset::ISet;
use super::super::map::Map;
use super::super::set::Set;
use super::super::state_machine_internal as smi;
use super::algebra::ResourceAlgebra;
use super::exclusive::ExclusiveRA;
use super::pcm::PCM;
use super::tsm::CountRA;
use super::tsm_bool::*;
use super::tsm_collections::*;
use super::tsm_finite_multiset::*;
use super::tsm_persistent::*;
use super::agree::AgreementRA;
use super::super::multiset::Multiset;

verus! {

broadcast use {
    super::super::imap::group_imap_lemmas,
    super::super::iset::group_iset_lemmas,
    super::super::map::group_map_lemmas,
    super::super::set::group_set_lemmas,
    super::super::multiset::group_multiset_axioms,
    super::tsm_collections::group_tsm_fragment_lemmas,
};

// ---------------------------------------------------------------------------
// Configurations
/// The component configuration: `o`, `h` and `z` compose to `e`. Closed, so that a
/// chain passes it from one step to the next as an atom.
pub closed spec fn cfg<P: PCM>(o: P, h: P, z: P, e: P) -> bool {
    P::op(P::op(o, h), z) == e
}

/// The definition of `cfg` (for a machine's `cfg_split`/`cfg_join`).
pub proof fn cfg_iff<P: PCM>(o: P, h: P, z: P, e: P)
    ensures
        cfg(o, h, z, e) <==> P::op(P::op(o, h), z) == e,
{
}

// ---------------------------------------------------------------------------
// Ownership conditions (the forms the ownership compiler emits)
/// `o` owns every entry of `x`.
pub open spec fn map_owns<K, V>(o: MapFragment<K, V>, x: IMap<K, V>) -> bool {
    forall|k: K| x.contains_key(k) ==> #[trigger] o.at(k) == Some(ExclusiveRA::Exclusive(x[k]))
}

/// `o` owns every member of `x`.
pub open spec fn set_owns<K>(o: SetFragment<K>, x: ISet<K>) -> bool {
    forall|k: K| x.contains(k) ==> #[trigger] o.at(k) == Some(ExclusiveRA::Exclusive(()))
}

/// `o` holds every entry of `x` (persistent maps).
pub open spec fn pmap_owns<K, V>(o: PersistentMapFragment<K, V>, x: IMap<K, V>) -> bool {
    forall|k: K| x.contains_key(k) ==> #[trigger] o.at(k) == Some(AgreementRA::Agree(x[k]))
}

/// `o` holds every member of `x` (persistent sets).
pub open spec fn pset_owns<K>(o: PersistentSetFragment<K>, x: ISet<K>) -> bool {
    forall|k: K| x.contains(k) ==> #[trigger] o.at(k) == Some(AgreementRA::Agree(()))
}

/// The count a `bool` operand stands for.
pub open spec fn bool_count(x: bool) -> nat {
    if x { 1nat } else { 0nat }
}

// ---------------------------------------------------------------------------
// `map` / `imap`: general operands (`IMap` state)
/// `remove f -= (x)`: {cfg(o, h, z, v), o owns x} ⟹ {x ⊆ v, cfg(o \ dom x, h, z, v \ dom x)}.
pub proof fn imap_remove<K, V>(
    o: MapFragment<K, V>,
    h: MapFragment<K, V>,
    z: MapFragment<K, V>,
    v: IMap<K, V>,
    x: IMap<K, V>,
)
    requires
        cfg(o, h, z, map_frag(v)),
        map_owns(o, x),
    ensures
        x.submap_of(v),
        cfg(map_remove_many(o, x.dom()), h, z, map_frag(v.remove_keys(x.dom()))),
{
    MapFragment::associative(o, h, z);
    map_remove_many_frame(o, MapFragment::op(h, z), v, x);
    MapFragment::associative(map_remove_many(o, x.dom()), h, z);
}

/// `have f >= (x)`: {cfg(o, h, z, v), o·h owns x} ⟹ {x ⊆ v}.
pub proof fn imap_have<K, V>(
    o: MapFragment<K, V>,
    h: MapFragment<K, V>,
    z: MapFragment<K, V>,
    v: IMap<K, V>,
    x: IMap<K, V>,
)
    requires
        cfg(o, h, z, map_frag(v)),
        map_owns(MapFragment::op(o, h), x),
    ensures
        x.submap_of(v),
{
    map_have_many_frame(MapFragment::op(o, h), z, v, x);
}

/// `add f += (x)`: {cfg(o, h, z, v), dom v ⊥ dom x} ⟹ {cfg(o·x, h, z, v ∪ x)}.
pub proof fn imap_add<K, V>(
    o: MapFragment<K, V>,
    h: MapFragment<K, V>,
    z: MapFragment<K, V>,
    v: IMap<K, V>,
    x: IMap<K, V>,
)
    requires
        cfg(o, h, z, map_frag(v)),
        v.dom().disjoint(x.dom()),
    ensures
        cfg(MapFragment::op(o, map_frag(x)), h, z, map_frag(v.union_prefer_right(x))),
{
    MapFragment::associative(o, h, z);
    map_add_many_frame(o, MapFragment::op(h, z), v, x);
    MapFragment::associative(MapFragment::op(o, map_frag(x)), h, z);
}

// `imap`: singleton operands `[k => x]` (and `[k => let p]`, with `x` the owned value)
/// `remove f -= [k => x]`: {cfg(o, h, z, v), o owns [k => x]} ⟹ {v ∋ (k, x), cfg(o \ {k}, h, z, v.remove(k))}.
pub proof fn imap_remove_one<K, V>(
    o: MapFragment<K, V>,
    h: MapFragment<K, V>,
    z: MapFragment<K, V>,
    v: IMap<K, V>,
    k: K,
    x: V,
)
    requires
        cfg(o, h, z, map_frag(v)),
        map_owns(o, IMap::empty().insert(k, x)),
    ensures
        v.contains_pair(k, x),
        cfg(map_remove_many(o, IMap::empty().insert(k, x).dom()), h, z, map_frag(v.remove(k))),
{
    let r = IMap::<K, V>::empty().insert(k, x);
    imap_remove(o, h, z, v, r);
    assert(r.contains_key(k));
    assert(v.remove_keys(r.dom()) =~= v.remove(k));
}

/// `have f >= [k => x]`: {cfg(o, h, z, v), o·h owns [k => x]} ⟹ {v ∋ (k, x)}.
pub proof fn imap_have_one<K, V>(
    o: MapFragment<K, V>,
    h: MapFragment<K, V>,
    z: MapFragment<K, V>,
    v: IMap<K, V>,
    k: K,
    x: V,
)
    requires
        cfg(o, h, z, map_frag(v)),
        map_owns(MapFragment::op(o, h), IMap::empty().insert(k, x)),
    ensures
        v.contains_pair(k, x),
{
    let r = IMap::<K, V>::empty().insert(k, x);
    imap_have(o, h, z, v, r);
    assert(r.contains_key(k));
}

/// `add f += [k => x]`: {cfg(o, h, z, v), k ∉ dom v} ⟹ {cfg(o·[k => x], h, z, v.insert(k, x))}.
pub proof fn imap_add_one<K, V>(
    o: MapFragment<K, V>,
    h: MapFragment<K, V>,
    z: MapFragment<K, V>,
    v: IMap<K, V>,
    k: K,
    x: V,
)
    requires
        cfg(o, h, z, map_frag(v)),
        !v.dom().contains(k),
    ensures
        cfg(
            MapFragment::op(o, map_frag(IMap::empty().insert(k, x))),
            h,
            z,
            map_frag(v.insert(k, x)),
        ),
{
    let r = IMap::<K, V>::empty().insert(k, x);
    imap_add(o, h, z, v, r);
    assert(v.union_prefer_right(r) =~= v.insert(k, x));
}

// `map`: general operands (finite `Map` state and operand)
/// `remove f -= (x)` (finite): {cfg(o, h, z, v), o owns x} ⟹ {x ⊆ v, cfg(o \ dom x, h, z, v \ dom x)}.
pub proof fn map_remove<K, V>(
    o: MapFragment<K, V>,
    h: MapFragment<K, V>,
    z: MapFragment<K, V>,
    v: Map<K, V>,
    x: Map<K, V>,
)
    requires
        cfg(o, h, z, map_frag(v.to_imap())),
        map_owns(o, x.to_imap()),
    ensures
        x.submap_of(v),
        cfg(
            map_remove_many(o, x.to_imap().dom()),
            h,
            z,
            map_frag(v.remove_keys(x.dom()).to_imap()),
        ),
{
    imap_remove(o, h, z, v.to_imap(), x.to_imap());
    assert forall|k: K| #[trigger] x.dom().contains(k) implies v.dom().contains(k) && v[k]
        == x[k] by {
        assert(x.to_imap().contains_key(k));
        assert(v.to_imap().contains_key(k));
    };
    assert(v.to_imap().remove_keys(x.to_imap().dom()) =~= v.remove_keys(x.dom()).to_imap());
}

/// `have f >= (x)` (finite): {cfg(o, h, z, v), o·h owns x} ⟹ {x ⊆ v}.
pub proof fn map_have<K, V>(
    o: MapFragment<K, V>,
    h: MapFragment<K, V>,
    z: MapFragment<K, V>,
    v: Map<K, V>,
    x: Map<K, V>,
)
    requires
        cfg(o, h, z, map_frag(v.to_imap())),
        map_owns(MapFragment::op(o, h), x.to_imap()),
    ensures
        x.submap_of(v),
{
    imap_have(o, h, z, v.to_imap(), x.to_imap());
    assert forall|k: K| #[trigger] x.dom().contains(k) implies v.dom().contains(k) && v[k]
        == x[k] by {
        assert(x.to_imap().contains_key(k));
        assert(v.to_imap().contains_key(k));
    };
}

/// `add f += (x)` (finite): {cfg(o, h, z, v), dom v ⊥ dom x} ⟹ {cfg(o·x, h, z, v ∪ x)}.
pub proof fn map_add<K, V>(
    o: MapFragment<K, V>,
    h: MapFragment<K, V>,
    z: MapFragment<K, V>,
    v: Map<K, V>,
    x: Map<K, V>,
)
    requires
        cfg(o, h, z, map_frag(v.to_imap())),
        v.dom().disjoint(x.dom()),
    ensures
        cfg(
            MapFragment::op(o, map_frag(x.to_imap())),
            h,
            z,
            map_frag(v.union_prefer_right(x).to_imap()),
        ),
{
    assert(v.to_imap().dom().disjoint(x.to_imap().dom())) by {
        assert forall|k: K| #[trigger] v.to_imap().dom().contains(k) implies !x.to_imap().dom().contains(k) by {
            assert(v.dom().contains(k));
        };
    };
    imap_add(o, h, z, v.to_imap(), x.to_imap());
    assert(v.to_imap().union_prefer_right(x.to_imap()) =~= v.union_prefer_right(x).to_imap());
}

// `map`: singleton operands (finite `Map` state)
/// `remove f -= [k => x]` (finite): {cfg(o, h, z, v), o owns [k => x]} ⟹ {v ∋ (k, x), cfg(o \ {k}, h, z, v.remove(k))}.
pub proof fn map_remove_one<K, V>(
    o: MapFragment<K, V>,
    h: MapFragment<K, V>,
    z: MapFragment<K, V>,
    v: Map<K, V>,
    k: K,
    x: V,
)
    requires
        cfg(o, h, z, map_frag(v.to_imap())),
        map_owns(o, IMap::empty().insert(k, x)),
    ensures
        v.contains_pair(k, x),
        cfg(
            map_remove_many(o, IMap::empty().insert(k, x).dom()),
            h,
            z,
            map_frag(v.remove(k).to_imap()),
        ),
{
    imap_remove_one(o, h, z, v.to_imap(), k, x);
    assert(v.to_imap().dom().contains(k));
    assert(v.to_imap().remove(k) =~= v.remove(k).to_imap());
}

/// `have f >= [k => x]` (finite): {cfg(o, h, z, v), o·h owns [k => x]} ⟹ {v ∋ (k, x)}.
pub proof fn map_have_one<K, V>(
    o: MapFragment<K, V>,
    h: MapFragment<K, V>,
    z: MapFragment<K, V>,
    v: Map<K, V>,
    k: K,
    x: V,
)
    requires
        cfg(o, h, z, map_frag(v.to_imap())),
        map_owns(MapFragment::op(o, h), IMap::empty().insert(k, x)),
    ensures
        v.contains_pair(k, x),
{
    imap_have_one(o, h, z, v.to_imap(), k, x);
    assert(v.to_imap().dom().contains(k));
}

/// `add f += [k => x]` (finite): {cfg(o, h, z, v), k ∉ dom v} ⟹ {cfg(o·[k => x], h, z, v.insert(k, x))}.
pub proof fn map_add_one<K, V>(
    o: MapFragment<K, V>,
    h: MapFragment<K, V>,
    z: MapFragment<K, V>,
    v: Map<K, V>,
    k: K,
    x: V,
)
    requires
        cfg(o, h, z, map_frag(v.to_imap())),
        !v.dom().contains(k),
    ensures
        cfg(
            MapFragment::op(o, map_frag(IMap::empty().insert(k, x))),
            h,
            z,
            map_frag(v.insert(k, x).to_imap()),
        ),
{
    imap_add_one(o, h, z, v.to_imap(), k, x);
    assert(v.to_imap().insert(k, x) =~= v.insert(k, x).to_imap());
}

/// A borrowed singleton map token's entry `[k => x]` (`h` holds it with any rest `c`) is
/// observed in the owned fragment joined with `h` after any removal from the owned part
/// (generic interface): {cfg(o, h, z, v), h == [k => x]·c} ⟹ {(o \ removed)·h owns [k => x]}.
pub proof fn map_token_observed<K, V>(
    o: MapFragment<K, V>,
    h: MapFragment<K, V>,
    z: MapFragment<K, V>,
    v: IMap<K, V>,
    c: MapFragment<K, V>,
    removed: ISet<K>,
    k: K,
    x: V,
)
    requires
        cfg(o, h, z, map_frag(v)),
        h == MapFragment::op(map_frag(IMap::empty().insert(k, x)), c),
    ensures
        map_owns(MapFragment::op(map_remove_many(o, removed), h), IMap::empty().insert(k, x)),
{
    let r = IMap::<K, V>::empty().insert(k, x);
    assert(r.contains_key(k));
    map_frag_valid(v);
    assert(MapFragment::op(MapFragment::op(o, h), z).at(k).valid());
    assert forall|j: K| r.contains_key(j) implies #[trigger] MapFragment::op(
        map_remove_many(o, removed),
        h,
    ).at(j) == Some(ExclusiveRA::Exclusive(r[j])) by {
        assert(j == k);
    };
}

// ---------------------------------------------------------------------------
// `set` / `iset`: general operands (`ISet` state)
/// `remove f -= (x)`: {cfg(o, h, z, v), o owns x} ⟹ {x ⊆ v, cfg(o \ x, h, z, v \ x)}.
pub proof fn iset_remove<K>(
    o: SetFragment<K>,
    h: SetFragment<K>,
    z: SetFragment<K>,
    v: ISet<K>,
    x: ISet<K>,
)
    requires
        cfg(o, h, z, set_frag(v)),
        set_owns(o, x),
    ensures
        x.subset_of(v),
        cfg(set_remove_many(o, x), h, z, set_frag(v.difference(x))),
{
    SetFragment::associative(o, h, z);
    set_remove_many_frame(o, SetFragment::op(h, z), v, x);
    SetFragment::associative(set_remove_many(o, x), h, z);
}

/// `have f >= (x)`: {cfg(o, h, z, v), o·h owns x} ⟹ {x ⊆ v}.
pub proof fn iset_have<K>(
    o: SetFragment<K>,
    h: SetFragment<K>,
    z: SetFragment<K>,
    v: ISet<K>,
    x: ISet<K>,
)
    requires
        cfg(o, h, z, set_frag(v)),
        set_owns(SetFragment::op(o, h), x),
    ensures
        x.subset_of(v),
{
    set_have_many_frame(SetFragment::op(o, h), z, v, x);
}

/// `add f += (x)`: {cfg(o, h, z, v), v ⊥ x} ⟹ {cfg(o·x, h, z, v ∪ x)}.
pub proof fn iset_add<K>(
    o: SetFragment<K>,
    h: SetFragment<K>,
    z: SetFragment<K>,
    v: ISet<K>,
    x: ISet<K>,
)
    requires
        cfg(o, h, z, set_frag(v)),
        v.disjoint(x),
    ensures
        cfg(SetFragment::op(o, set_frag(x)), h, z, set_frag(v.union(x))),
{
    SetFragment::associative(o, h, z);
    set_add_many_frame(o, SetFragment::op(h, z), v, x);
    SetFragment::associative(SetFragment::op(o, set_frag(x)), h, z);
}

// `iset`: singleton operands `set {k}`
/// `remove f -= set {k}`: {cfg(o, h, z, v), o owns {k}} ⟹ {k ∈ v, cfg(o \ {k}, h, z, v.remove(k))}.
pub proof fn iset_remove_one<K>(
    o: SetFragment<K>,
    h: SetFragment<K>,
    z: SetFragment<K>,
    v: ISet<K>,
    k: K,
)
    requires
        cfg(o, h, z, set_frag(v)),
        set_owns(o, ISet::empty().insert(k)),
    ensures
        v.contains(k),
        cfg(set_remove_many(o, ISet::empty().insert(k)), h, z, set_frag(v.remove(k))),
{
    let r = ISet::<K>::empty().insert(k);
    iset_remove(o, h, z, v, r);
    assert(r.contains(k));
    assert(v.difference(r) =~= v.remove(k));
}

/// `have f >= set {k}`: {cfg(o, h, z, v), o·h owns {k}} ⟹ {k ∈ v}.
pub proof fn iset_have_one<K>(
    o: SetFragment<K>,
    h: SetFragment<K>,
    z: SetFragment<K>,
    v: ISet<K>,
    k: K,
)
    requires
        cfg(o, h, z, set_frag(v)),
        set_owns(SetFragment::op(o, h), ISet::empty().insert(k)),
    ensures
        v.contains(k),
{
    let r = ISet::<K>::empty().insert(k);
    iset_have(o, h, z, v, r);
    assert(r.contains(k));
}

/// `add f += set {k}`: {cfg(o, h, z, v), k ∉ v} ⟹ {cfg(o·{k}, h, z, v.insert(k))}.
pub proof fn iset_add_one<K>(
    o: SetFragment<K>,
    h: SetFragment<K>,
    z: SetFragment<K>,
    v: ISet<K>,
    k: K,
)
    requires
        cfg(o, h, z, set_frag(v)),
        !v.contains(k),
    ensures
        cfg(SetFragment::op(o, set_frag(ISet::empty().insert(k))), h, z, set_frag(v.insert(k))),
{
    let r = ISet::<K>::empty().insert(k);
    iset_add(o, h, z, v, r);
    assert(v.union(r) =~= v.insert(k));
}

// `set`: general operands (finite `Set` state and operand)
/// `remove f -= (x)` (finite): {cfg(o, h, z, v), o owns x} ⟹ {x ⊆ v, cfg(o \ x, h, z, v \ x)}.
pub proof fn set_remove<K>(
    o: SetFragment<K>,
    h: SetFragment<K>,
    z: SetFragment<K>,
    v: Set<K>,
    x: Set<K>,
)
    requires
        cfg(o, h, z, set_frag(v.to_iset())),
        set_owns(o, x.to_iset()),
    ensures
        x.subset_of(v),
        cfg(set_remove_many(o, x.to_iset()), h, z, set_frag(v.difference(x).to_iset())),
{
    iset_remove(o, h, z, v.to_iset(), x.to_iset());
    assert forall|k: K| #[trigger] x.contains(k) implies v.contains(k) by {
        assert(x.to_iset().contains(k));
    };
    assert(v.to_iset().difference(x.to_iset()) =~= v.difference(x).to_iset());
}

/// `have f >= (x)` (finite): {cfg(o, h, z, v), o·h owns x} ⟹ {x ⊆ v}.
pub proof fn set_have<K>(
    o: SetFragment<K>,
    h: SetFragment<K>,
    z: SetFragment<K>,
    v: Set<K>,
    x: Set<K>,
)
    requires
        cfg(o, h, z, set_frag(v.to_iset())),
        set_owns(SetFragment::op(o, h), x.to_iset()),
    ensures
        x.subset_of(v),
{
    iset_have(o, h, z, v.to_iset(), x.to_iset());
    assert forall|k: K| #[trigger] x.contains(k) implies v.contains(k) by {
        assert(x.to_iset().contains(k));
    };
}

/// `add f += (x)` (finite): {cfg(o, h, z, v), v ⊥ x} ⟹ {cfg(o·x, h, z, v ∪ x)}.
pub proof fn set_add<K>(
    o: SetFragment<K>,
    h: SetFragment<K>,
    z: SetFragment<K>,
    v: Set<K>,
    x: Set<K>,
)
    requires
        cfg(o, h, z, set_frag(v.to_iset())),
        v.disjoint(x),
    ensures
        cfg(SetFragment::op(o, set_frag(x.to_iset())), h, z, set_frag(v.union(x).to_iset())),
{
    assert(v.to_iset().disjoint(x.to_iset())) by {
        assert forall|k: K| #[trigger] v.to_iset().contains(k) implies !x.to_iset().contains(k) by {
            assert(v.contains(k));
        };
    };
    iset_add(o, h, z, v.to_iset(), x.to_iset());
    assert(v.to_iset().union(x.to_iset()) =~= v.union(x).to_iset());
}

// `set`: singleton operands (finite `Set` state)
/// `remove f -= set {k}` (finite): {cfg(o, h, z, v), o owns {k}} ⟹ {k ∈ v, cfg(o \ {k}, h, z, v.remove(k))}.
pub proof fn set_remove_one<K>(
    o: SetFragment<K>,
    h: SetFragment<K>,
    z: SetFragment<K>,
    v: Set<K>,
    k: K,
)
    requires
        cfg(o, h, z, set_frag(v.to_iset())),
        set_owns(o, ISet::empty().insert(k)),
    ensures
        v.contains(k),
        cfg(set_remove_many(o, ISet::empty().insert(k)), h, z, set_frag(v.remove(k).to_iset())),
{
    iset_remove_one(o, h, z, v.to_iset(), k);
    assert(v.to_iset().remove(k) =~= v.remove(k).to_iset());
}

/// `have f >= set {k}` (finite): {cfg(o, h, z, v), o·h owns {k}} ⟹ {k ∈ v}.
pub proof fn set_have_one<K>(
    o: SetFragment<K>,
    h: SetFragment<K>,
    z: SetFragment<K>,
    v: Set<K>,
    k: K,
)
    requires
        cfg(o, h, z, set_frag(v.to_iset())),
        set_owns(SetFragment::op(o, h), ISet::empty().insert(k)),
    ensures
        v.contains(k),
{
    iset_have_one(o, h, z, v.to_iset(), k);
}

/// `add f += set {k}` (finite): {cfg(o, h, z, v), k ∉ v} ⟹ {cfg(o·{k}, h, z, v.insert(k))}.
pub proof fn set_add_one<K>(
    o: SetFragment<K>,
    h: SetFragment<K>,
    z: SetFragment<K>,
    v: Set<K>,
    k: K,
)
    requires
        cfg(o, h, z, set_frag(v.to_iset())),
        !v.contains(k),
    ensures
        cfg(SetFragment::op(o, set_frag(ISet::empty().insert(k))), h, z, set_frag(v.insert(k).to_iset())),
{
    iset_add_one(o, h, z, v.to_iset(), k);
    assert(v.to_iset().insert(k) =~= v.insert(k).to_iset());
}

// ---------------------------------------------------------------------------
// `option`: general operands
/// `remove f -= (x)`: {cfg(o, h, z, v), o holds x} ⟹ {x is Some ⟹ v == x, cfg(o − x, h, z, opt_sub(v, x))}.
pub proof fn opt_remove<V>(
    o: OptionFragment<V>,
    h: OptionFragment<V>,
    z: OptionFragment<V>,
    v: Option<V>,
    x: Option<V>,
)
    requires
        cfg(o, h, z, option_frag(v)),
        option_contains_operand(o, x),
    ensures
        smi::opt_ge(v, x),
        cfg(option_remove_operand(o, x), h, z, option_frag(smi::opt_sub(v, x))),
{
    OptionFragment::associative(o, h, z);
    option_remove_general_frame(o, OptionFragment::op(h, z), v, x);
    OptionFragment::associative(option_remove_operand(o, x), h, z);
}

/// `have f >= (x)`: {cfg(o, h, z, v), o·h holds x} ⟹ {x is Some ⟹ v == x}.
pub proof fn opt_have<V>(
    o: OptionFragment<V>,
    h: OptionFragment<V>,
    z: OptionFragment<V>,
    v: Option<V>,
    x: Option<V>,
)
    requires
        cfg(o, h, z, option_frag(v)),
        option_contains_operand(OptionFragment::op(o, h), x),
    ensures
        smi::opt_ge(v, x),
{
    option_have_general_frame(OptionFragment::op(o, h), z, v, x);
}

/// `add f += (x)`: {cfg(o, h, z, v), x is None or v is None} ⟹ {cfg(o·x, h, z, opt_add(v, x))}.
pub proof fn opt_add<V>(
    o: OptionFragment<V>,
    h: OptionFragment<V>,
    z: OptionFragment<V>,
    v: Option<V>,
    x: Option<V>,
)
    requires
        cfg(o, h, z, option_frag(v)),
        smi::opt_is_none(x) || v is None,
    ensures
        cfg(OptionFragment::op(o, option_frag(x)), h, z, option_frag(smi::opt_add(v, x))),
{
    OptionFragment::associative(o, h, z);
    option_add_general_frame(o, OptionFragment::op(h, z), v, x);
    OptionFragment::associative(OptionFragment::op(o, option_frag(x)), h, z);
}

// `option`: `Some(x)` operands (and `Some(let p)`, with `x` the owned value)
/// `remove f -= Some(x)` (and `Some(let p)`, `x` the owned value): {cfg(o, h, z, v), o holds Some(x)} ⟹ {v == Some(x), cfg(None, h, z, None)}.
pub proof fn opt_remove_some<V>(
    o: OptionFragment<V>,
    h: OptionFragment<V>,
    z: OptionFragment<V>,
    v: Option<V>,
    x: V,
)
    requires
        cfg(o, h, z, option_frag(v)),
        option_contains_operand(o, Some(x)),
    ensures
        v == Some(x),
        cfg(option_remove_operand(o, Some(x)), h, z, option_frag(None)),
{
    opt_remove(o, h, z, v, Some(x));
}

/// `have f >= Some(x)` (and `Some(let p)`, `x` the observed value): {cfg(o, h, z, v), o·h holds Some(x)} ⟹ {v == Some(x)}.
pub proof fn opt_have_some<V>(
    o: OptionFragment<V>,
    h: OptionFragment<V>,
    z: OptionFragment<V>,
    v: Option<V>,
    x: V,
)
    requires
        cfg(o, h, z, option_frag(v)),
        option_contains_operand(OptionFragment::op(o, h), Some(x)),
    ensures
        v == Some(x),
{
    opt_have(o, h, z, v, Some(x));
}

/// `add f += Some(x)`: {cfg(o, h, z, v), v is None} ⟹ {cfg(o·Some(x), h, z, Some(x))}.
pub proof fn opt_add_some<V>(
    o: OptionFragment<V>,
    h: OptionFragment<V>,
    z: OptionFragment<V>,
    v: Option<V>,
    x: V,
)
    requires
        cfg(o, h, z, option_frag(v)),
        v is None,
    ensures
        cfg(OptionFragment::op(o, option_frag(Some(x))), h, z, option_frag(Some(x))),
{
    opt_add(o, h, z, v, Some(x));
}

// ---------------------------------------------------------------------------
// `persistent_map` / `persistent_imap` (`IMap` state)
/// `have f >= (x)`: {cfg(o, h, z, v), o·h holds x} ⟹ {x ⊆ v}.
pub proof fn pimap_have<K, V>(
    o: PersistentMapFragment<K, V>,
    h: PersistentMapFragment<K, V>,
    z: PersistentMapFragment<K, V>,
    v: IMap<K, V>,
    x: IMap<K, V>,
)
    requires
        cfg(o, h, z, persistent_map_frag(v)),
        pmap_owns(PersistentMapFragment::op(o, h), x),
    ensures
        x.submap_of(v),
{
    persistent_map_have_many_frame(PersistentMapFragment::op(o, h), z, v, x);
}

/// `add f (union)= (x)`: {cfg(o, h, z, v), v agrees with x} ⟹ {cfg(o·x, h, z, v ∪ x)}.
pub proof fn pimap_add<K, V>(
    o: PersistentMapFragment<K, V>,
    h: PersistentMapFragment<K, V>,
    z: PersistentMapFragment<K, V>,
    v: IMap<K, V>,
    x: IMap<K, V>,
)
    requires
        cfg(o, h, z, persistent_map_frag(v)),
        v.agrees(x),
    ensures
        cfg(PersistentMapFragment::op(o, persistent_map_frag(x)), h, z, persistent_map_frag(v.union_prefer_right(x))),
{
    PersistentMapFragment::associative(o, h, z);
    persistent_map_union_frame(o, PersistentMapFragment::op(h, z), v, x);
    PersistentMapFragment::associative(PersistentMapFragment::op(o, persistent_map_frag(x)), h, z);
}

/// `have f >= [k => x]`: {cfg(o, h, z, v), o·h holds [k => x]} ⟹ {v ∋ (k, x)}.
pub proof fn pimap_have_one<K, V>(
    o: PersistentMapFragment<K, V>,
    h: PersistentMapFragment<K, V>,
    z: PersistentMapFragment<K, V>,
    v: IMap<K, V>,
    k: K,
    x: V,
)
    requires
        cfg(o, h, z, persistent_map_frag(v)),
        pmap_owns(PersistentMapFragment::op(o, h), IMap::empty().insert(k, x)),
    ensures
        v.contains_pair(k, x),
{
    let r = IMap::<K, V>::empty().insert(k, x);
    pimap_have(o, h, z, v, r);
    assert(r.contains_key(k));
}

/// `add f (union)= [k => x]`: {cfg(o, h, z, v), k ∈ dom v ⟹ v[k] == x} ⟹
/// {cfg(o·[k => x], h, z, v.insert(k, x))}.
pub proof fn pimap_add_one<K, V>(
    o: PersistentMapFragment<K, V>,
    h: PersistentMapFragment<K, V>,
    z: PersistentMapFragment<K, V>,
    v: IMap<K, V>,
    k: K,
    x: V,
)
    requires
        cfg(o, h, z, persistent_map_frag(v)),
        v.dom().contains(k) ==> v[k] == x,
    ensures
        cfg(
            PersistentMapFragment::op(o, persistent_map_frag(IMap::empty().insert(k, x))),
            h,
            z,
            persistent_map_frag(v.insert(k, x)),
        ),
{
    let r = IMap::<K, V>::empty().insert(k, x);
    assert(v.agrees(r));
    pimap_add(o, h, z, v, r);
    assert(v.union_prefer_right(r) =~= v.insert(k, x));
}

// `persistent_map` (finite `Map` state and operands)
/// `have f >= (x)` (finite): {cfg(o, h, z, v), o·h holds x} ⟹ {x ⊆ v}.
pub proof fn pmap_have<K, V>(
    o: PersistentMapFragment<K, V>,
    h: PersistentMapFragment<K, V>,
    z: PersistentMapFragment<K, V>,
    v: Map<K, V>,
    x: Map<K, V>,
)
    requires
        cfg(o, h, z, persistent_map_frag(v.to_imap())),
        pmap_owns(PersistentMapFragment::op(o, h), x.to_imap()),
    ensures
        x.submap_of(v),
{
    pimap_have(o, h, z, v.to_imap(), x.to_imap());
    assert forall|k: K| #[trigger] x.dom().contains(k) implies v.dom().contains(k) && v[k]
        == x[k] by {
        assert(x.to_imap().contains_key(k));
        assert(v.to_imap().contains_key(k));
    };
}

/// `add f (union)= (x)` (finite): {cfg(o, h, z, v), v agrees with x} ⟹ {cfg(o·x, h, z, v ∪ x)}.
pub proof fn pmap_add<K, V>(
    o: PersistentMapFragment<K, V>,
    h: PersistentMapFragment<K, V>,
    z: PersistentMapFragment<K, V>,
    v: Map<K, V>,
    x: Map<K, V>,
)
    requires
        cfg(o, h, z, persistent_map_frag(v.to_imap())),
        v.agrees(x),
    ensures
        cfg(
            PersistentMapFragment::op(o, persistent_map_frag(x.to_imap())),
            h,
            z,
            persistent_map_frag(v.union_prefer_right(x).to_imap()),
        ),
{
    assert(v.to_imap().agrees(x.to_imap())) by {
        assert forall|k: K| v.to_imap().dom().contains(k) && x.to_imap().dom().contains(k)
            implies #[trigger] v.to_imap()[k] == x.to_imap()[k] by {
            assert(v.dom().contains(k) && x.dom().contains(k));
        };
    };
    pimap_add(o, h, z, v.to_imap(), x.to_imap());
    assert(v.to_imap().union_prefer_right(x.to_imap()) =~= v.union_prefer_right(x).to_imap());
}

/// `have f >= [k => x]` (finite): {cfg(o, h, z, v), o·h holds [k => x]} ⟹ {v ∋ (k, x)}.
pub proof fn pmap_have_one<K, V>(
    o: PersistentMapFragment<K, V>,
    h: PersistentMapFragment<K, V>,
    z: PersistentMapFragment<K, V>,
    v: Map<K, V>,
    k: K,
    x: V,
)
    requires
        cfg(o, h, z, persistent_map_frag(v.to_imap())),
        pmap_owns(PersistentMapFragment::op(o, h), IMap::empty().insert(k, x)),
    ensures
        v.contains_pair(k, x),
{
    pimap_have_one(o, h, z, v.to_imap(), k, x);
    assert(v.to_imap().dom().contains(k));
}

/// `add f (union)= [k => x]` (finite): {cfg(o, h, z, v), k ∈ dom v ⟹ v[k] == x} ⟹
/// {cfg(o·[k => x], h, z, v.insert(k, x))}.
pub proof fn pmap_add_one<K, V>(
    o: PersistentMapFragment<K, V>,
    h: PersistentMapFragment<K, V>,
    z: PersistentMapFragment<K, V>,
    v: Map<K, V>,
    k: K,
    x: V,
)
    requires
        cfg(o, h, z, persistent_map_frag(v.to_imap())),
        v.dom().contains(k) ==> v[k] == x,
    ensures
        cfg(
            PersistentMapFragment::op(o, persistent_map_frag(IMap::empty().insert(k, x))),
            h,
            z,
            persistent_map_frag(v.insert(k, x).to_imap()),
        ),
{
    pimap_add_one(o, h, z, v.to_imap(), k, x);
    assert(v.to_imap().insert(k, x) =~= v.insert(k, x).to_imap());
}

// ---------------------------------------------------------------------------
// `persistent_set` / `persistent_iset` (`ISet` state)
/// `have f >= (x)`: {cfg(o, h, z, v), o·h holds x} ⟹ {x ⊆ v}.
pub proof fn piset_have<K>(
    o: PersistentSetFragment<K>,
    h: PersistentSetFragment<K>,
    z: PersistentSetFragment<K>,
    v: ISet<K>,
    x: ISet<K>,
)
    requires
        cfg(o, h, z, persistent_set_frag(v)),
        pset_owns(PersistentSetFragment::op(o, h), x),
    ensures
        x.subset_of(v),
{
    persistent_set_have_many_frame(PersistentSetFragment::op(o, h), z, v, x);
}

/// `add f (union)= (x)`: {cfg(o, h, z, v)} ⟹ {cfg(o·x, h, z, v ∪ x)}.
pub proof fn piset_add<K>(
    o: PersistentSetFragment<K>,
    h: PersistentSetFragment<K>,
    z: PersistentSetFragment<K>,
    v: ISet<K>,
    x: ISet<K>,
)
    requires
        cfg(o, h, z, persistent_set_frag(v)),
    ensures
        cfg(PersistentSetFragment::op(o, persistent_set_frag(x)), h, z, persistent_set_frag(v.union(x))),
{
    PersistentSetFragment::associative(o, h, z);
    persistent_set_union_frame(o, PersistentSetFragment::op(h, z), v, x);
    PersistentSetFragment::associative(PersistentSetFragment::op(o, persistent_set_frag(x)), h, z);
}

/// `have f >= set {k}`: {cfg(o, h, z, v), o·h holds {k}} ⟹ {k ∈ v}.
pub proof fn piset_have_one<K>(
    o: PersistentSetFragment<K>,
    h: PersistentSetFragment<K>,
    z: PersistentSetFragment<K>,
    v: ISet<K>,
    k: K,
)
    requires
        cfg(o, h, z, persistent_set_frag(v)),
        pset_owns(PersistentSetFragment::op(o, h), ISet::empty().insert(k)),
    ensures
        v.contains(k),
{
    let r = ISet::<K>::empty().insert(k);
    piset_have(o, h, z, v, r);
    assert(r.contains(k));
}

/// `add f (union)= set {k}`: {cfg(o, h, z, v)} ⟹ {cfg(o·{k}, h, z, v.insert(k))}.
pub proof fn piset_add_one<K>(
    o: PersistentSetFragment<K>,
    h: PersistentSetFragment<K>,
    z: PersistentSetFragment<K>,
    v: ISet<K>,
    k: K,
)
    requires
        cfg(o, h, z, persistent_set_frag(v)),
    ensures
        cfg(
            PersistentSetFragment::op(o, persistent_set_frag(ISet::empty().insert(k))),
            h,
            z,
            persistent_set_frag(v.insert(k)),
        ),
{
    let r = ISet::<K>::empty().insert(k);
    piset_add(o, h, z, v, r);
    assert(v.union(r) =~= v.insert(k));
}

// `persistent_set` (finite `Set` state and operands)
/// `have f >= (x)` (finite): {cfg(o, h, z, v), o·h holds x} ⟹ {x ⊆ v}.
pub proof fn pset_have<K>(
    o: PersistentSetFragment<K>,
    h: PersistentSetFragment<K>,
    z: PersistentSetFragment<K>,
    v: Set<K>,
    x: Set<K>,
)
    requires
        cfg(o, h, z, persistent_set_frag(v.to_iset())),
        pset_owns(PersistentSetFragment::op(o, h), x.to_iset()),
    ensures
        x.subset_of(v),
{
    piset_have(o, h, z, v.to_iset(), x.to_iset());
    assert forall|k: K| #[trigger] x.contains(k) implies v.contains(k) by {
        assert(x.to_iset().contains(k));
    };
}

/// `add f (union)= (x)` (finite): {cfg(o, h, z, v)} ⟹ {cfg(o·x, h, z, v ∪ x)}.
pub proof fn pset_add<K>(
    o: PersistentSetFragment<K>,
    h: PersistentSetFragment<K>,
    z: PersistentSetFragment<K>,
    v: Set<K>,
    x: Set<K>,
)
    requires
        cfg(o, h, z, persistent_set_frag(v.to_iset())),
    ensures
        cfg(
            PersistentSetFragment::op(o, persistent_set_frag(x.to_iset())),
            h,
            z,
            persistent_set_frag(v.union(x).to_iset()),
        ),
{
    piset_add(o, h, z, v.to_iset(), x.to_iset());
    assert(v.to_iset().union(x.to_iset()) =~= v.union(x).to_iset());
}

/// `have f >= set {k}` (finite): {cfg(o, h, z, v), o·h holds {k}} ⟹ {k ∈ v}.
pub proof fn pset_have_one<K>(
    o: PersistentSetFragment<K>,
    h: PersistentSetFragment<K>,
    z: PersistentSetFragment<K>,
    v: Set<K>,
    k: K,
)
    requires
        cfg(o, h, z, persistent_set_frag(v.to_iset())),
        pset_owns(PersistentSetFragment::op(o, h), ISet::empty().insert(k)),
    ensures
        v.contains(k),
{
    piset_have_one(o, h, z, v.to_iset(), k);
}

/// `add f (union)= set {k}` (finite): {cfg(o, h, z, v)} ⟹ {cfg(o·{k}, h, z, v.insert(k))}.
pub proof fn pset_add_one<K>(
    o: PersistentSetFragment<K>,
    h: PersistentSetFragment<K>,
    z: PersistentSetFragment<K>,
    v: Set<K>,
    k: K,
)
    requires
        cfg(o, h, z, persistent_set_frag(v.to_iset())),
    ensures
        cfg(
            PersistentSetFragment::op(o, persistent_set_frag(ISet::empty().insert(k))),
            h,
            z,
            persistent_set_frag(v.insert(k).to_iset()),
        ),
{
    piset_add_one(o, h, z, v.to_iset(), k);
    assert(v.to_iset().insert(k) =~= v.insert(k).to_iset());
}

// ---------------------------------------------------------------------------
// `persistent_option`
/// `have f >= (x)`: {cfg(o, h, z, v), o·h holds x} ⟹ {x is Some ⟹ v == x}.
pub proof fn popt_have<V>(
    o: PersistentOptionFragment<V>,
    h: PersistentOptionFragment<V>,
    z: PersistentOptionFragment<V>,
    v: Option<V>,
    x: Option<V>,
)
    requires
        cfg(o, h, z, persistent_option_frag(v)),
        persistent_option_contains_operand(PersistentOptionFragment::op(o, h), x),
    ensures
        smi::opt_ge(v, x),
{
    persistent_option_have_general_frame(PersistentOptionFragment::op(o, h), z, v, x);
}

/// `add f (union)= (x)`: {cfg(o, h, z, v), v and x agree} ⟹ {cfg(o·x, h, z, opt_add(v, x))}.
pub proof fn popt_add<V>(
    o: PersistentOptionFragment<V>,
    h: PersistentOptionFragment<V>,
    z: PersistentOptionFragment<V>,
    v: Option<V>,
    x: Option<V>,
)
    requires
        cfg(o, h, z, persistent_option_frag(v)),
        smi::opt_agree(v, x),
    ensures
        cfg(PersistentOptionFragment::op(o, persistent_option_frag(x)), h, z, persistent_option_frag(smi::opt_add(v, x))),
{
    PersistentOptionFragment::associative(o, h, z);
    persistent_option_union_general_frame(o, PersistentOptionFragment::op(h, z), v, x);
    PersistentOptionFragment::associative(PersistentOptionFragment::op(o, persistent_option_frag(x)), h, z);
}

/// `have f >= Some(x)` (and `Some(let p)`, `x` the observed value):
/// {cfg(o, h, z, v), o·h holds Some(x)} ⟹ {v == Some(x)}.
pub proof fn popt_have_some<V>(
    o: PersistentOptionFragment<V>,
    h: PersistentOptionFragment<V>,
    z: PersistentOptionFragment<V>,
    v: Option<V>,
    x: V,
)
    requires
        cfg(o, h, z, persistent_option_frag(v)),
        persistent_option_contains_operand(PersistentOptionFragment::op(o, h), Some(x)),
    ensures
        v == Some(x),
{
    popt_have(o, h, z, v, Some(x));
}

/// `add f (union)= Some(x)`: {cfg(o, h, z, v), v is Some ⟹ v == Some(x)} ⟹
/// {cfg(o·Some(x), h, z, Some(x))}.
pub proof fn popt_add_some<V>(
    o: PersistentOptionFragment<V>,
    h: PersistentOptionFragment<V>,
    z: PersistentOptionFragment<V>,
    v: Option<V>,
    x: V,
)
    requires
        cfg(o, h, z, persistent_option_frag(v)),
        v is Some ==> v->0 == x,
    ensures
        cfg(PersistentOptionFragment::op(o, persistent_option_frag(Some(x))), h, z, persistent_option_frag(Some(x))),
{
    popt_add(o, h, z, v, Some(x));
}

// ---------------------------------------------------------------------------
// `multiset`
/// `remove f -= (x)`: {cfg(o, h, z, v), x ⊆ o} ⟹ {x ⊆ v, cfg(o − x, h, z, v − x)}.
pub proof fn mset_remove<V>(
    o: FiniteMultisetRA<V>,
    h: FiniteMultisetRA<V>,
    z: FiniteMultisetRA<V>,
    v: Multiset<V>,
    x: Multiset<V>,
)
    requires
        cfg(o, h, z, finite_multiset_frag(v)),
        x.subset_of(o.values),
    ensures
        x.subset_of(v),
        cfg(finite_multiset_frag(o.values.sub(x)), h, z, finite_multiset_frag(v.sub(x))),
{
    FiniteMultisetRA::associative(o, h, z);
    finite_multiset_remove_many_frame(o, FiniteMultisetRA::op(h, z), v, x);
    FiniteMultisetRA::associative(finite_multiset_frag(o.values.sub(x)), h, z);
}

/// `have f >= (x)`: {cfg(o, h, z, v), x ⊆ o·h} ⟹ {x ⊆ v}.
pub proof fn mset_have<V>(
    o: FiniteMultisetRA<V>,
    h: FiniteMultisetRA<V>,
    z: FiniteMultisetRA<V>,
    v: Multiset<V>,
    x: Multiset<V>,
)
    requires
        cfg(o, h, z, finite_multiset_frag(v)),
        x.subset_of(FiniteMultisetRA::op(o, h).values),
    ensures
        x.subset_of(v),
{
    finite_multiset_owned_subset(FiniteMultisetRA::op(o, h), z, v);
}

/// `add f += (x)`: {cfg(o, h, z, v)} ⟹ {cfg(o + x, h, z, v + x)}.
pub proof fn mset_add<V>(
    o: FiniteMultisetRA<V>,
    h: FiniteMultisetRA<V>,
    z: FiniteMultisetRA<V>,
    v: Multiset<V>,
    x: Multiset<V>,
)
    requires
        cfg(o, h, z, finite_multiset_frag(v)),
    ensures
        cfg(finite_multiset_frag(o.values.add(x)), h, z, finite_multiset_frag(v.add(x))),
{
    FiniteMultisetRA::associative(o, h, z);
    finite_multiset_add_many_frame(o, FiniteMultisetRA::op(h, z), v, x);
    FiniteMultisetRA::associative(finite_multiset_frag(o.values.add(x)), h, z);
}

/// `remove f -= {e}`: {cfg(o, h, z, v), {e} ⊆ o} ⟹ {v.count(e) ≥ 1, cfg(o − {e}, h, z, v.remove(e))}.
pub proof fn mset_remove_one<V>(
    o: FiniteMultisetRA<V>,
    h: FiniteMultisetRA<V>,
    z: FiniteMultisetRA<V>,
    v: Multiset<V>,
    e: V,
)
    requires
        cfg(o, h, z, finite_multiset_frag(v)),
        Multiset::empty().insert(e).subset_of(o.values),
    ensures
        v.count(e) >= 1,
        cfg(finite_multiset_frag(o.values.sub(Multiset::empty().insert(e))), h, z, finite_multiset_frag(v.remove(e))),
{
    let r = Multiset::<V>::empty().insert(e);
    mset_remove(o, h, z, v, r);
    assert(r.count(e) == 1);
    assert(v.sub(r) =~= v.remove(e));
}

/// `have f >= {e}`: {cfg(o, h, z, v), {e} ⊆ o·h} ⟹ {v.count(e) ≥ 1}.
pub proof fn mset_have_one<V>(
    o: FiniteMultisetRA<V>,
    h: FiniteMultisetRA<V>,
    z: FiniteMultisetRA<V>,
    v: Multiset<V>,
    e: V,
)
    requires
        cfg(o, h, z, finite_multiset_frag(v)),
        Multiset::empty().insert(e).subset_of(FiniteMultisetRA::op(o, h).values),
    ensures
        v.count(e) >= 1,
{
    let r = Multiset::<V>::empty().insert(e);
    mset_have(o, h, z, v, r);
    assert(r.count(e) == 1);
}

/// `add f += {e}`: {cfg(o, h, z, v)} ⟹ {cfg(o + {e}, h, z, v.insert(e))}.
pub proof fn mset_add_one<V>(
    o: FiniteMultisetRA<V>,
    h: FiniteMultisetRA<V>,
    z: FiniteMultisetRA<V>,
    v: Multiset<V>,
    e: V,
)
    requires
        cfg(o, h, z, finite_multiset_frag(v)),
    ensures
        cfg(finite_multiset_frag(o.values.add(Multiset::empty().insert(e))), h, z, finite_multiset_frag(v.insert(e))),
{
    let r = Multiset::<V>::empty().insert(e);
    mset_add(o, h, z, v, r);
    assert(v.add(r) =~= v.insert(e));
}

// ---------------------------------------------------------------------------
// `count`
/// `remove f -= (x)`: {cfg(o, h, z, v), o ≥ x} ⟹ {v ≥ x, cfg(o − x, h, z, v − x)}.
pub proof fn count_remove(o: CountRA, h: CountRA, z: CountRA, v: nat, x: nat)
    requires
        cfg(o, h, z, CountRA { count: v }),
        o.count >= x,
    ensures
        v >= x,
        cfg(CountRA { count: (o.count - x) as nat }, h, z, CountRA { count: (v - x) as nat }),
{
}

/// `have f >= (x)`: {cfg(o, h, z, v), o·h ≥ x} ⟹ {v ≥ x}.
pub proof fn count_have(o: CountRA, h: CountRA, z: CountRA, v: nat, x: nat)
    requires
        cfg(o, h, z, CountRA { count: v }),
        CountRA::op(o, h).count >= x,
    ensures
        v >= x,
{
}

/// `add f += (x)`: {cfg(o, h, z, v)} ⟹ {cfg(o + x, h, z, v + x)}.
pub proof fn count_add(o: CountRA, h: CountRA, z: CountRA, v: nat, x: nat)
    requires
        cfg(o, h, z, CountRA { count: v }),
    ensures
        cfg(CountRA { count: o.count + x }, h, z, CountRA { count: v + x }),
{
}

// ---------------------------------------------------------------------------
// `bool`
/// `remove f -= (x)`: {cfg(o, h, z, v), o ≥ [x]} ⟹ {x ⟹ v, cfg(o − [x], h, z, v ∧ ¬x)}.
pub proof fn bool_remove(o: CountRA, h: CountRA, z: CountRA, v: bool, x: bool)
    requires
        cfg(o, h, z, bool_frag(v)),
        o.count >= bool_count(x),
    ensures
        x ==> v,
        cfg(CountRA { count: (o.count - bool_count(x)) as nat }, h, z, bool_frag(v && !x)),
{
}

/// `have f >= (x)`: {cfg(o, h, z, v), o·h ≥ [x]} ⟹ {x ⟹ v}.
pub proof fn bool_have(o: CountRA, h: CountRA, z: CountRA, v: bool, x: bool)
    requires
        cfg(o, h, z, bool_frag(v)),
        CountRA::op(o, h).count >= bool_count(x),
    ensures
        x ==> v,
{
}

/// `add f += (x)`: {cfg(o, h, z, v), ¬v ∨ ¬x} ⟹ {cfg(o + [x], h, z, v ∨ x)}.
pub proof fn bool_add(o: CountRA, h: CountRA, z: CountRA, v: bool, x: bool)
    requires
        cfg(o, h, z, bool_frag(v)),
        !v || !x,
    ensures
        cfg(CountRA { count: o.count + bool_count(x) }, h, z, bool_frag(v || x)),
{
}

/// `remove f -= true`: {cfg(o, h, z, v), o ≥ 1} ⟹ {v, cfg(o − 1, h, z, false)}.
pub proof fn bool_remove_true(o: CountRA, h: CountRA, z: CountRA, v: bool)
    requires
        cfg(o, h, z, bool_frag(v)),
        o.count >= bool_count(true),
    ensures
        v,
        cfg(CountRA { count: (o.count - bool_count(true)) as nat }, h, z, bool_frag(false)),
{
}

/// `have f >= true`: {cfg(o, h, z, v), o·h ≥ 1} ⟹ {v}.
pub proof fn bool_have_true(o: CountRA, h: CountRA, z: CountRA, v: bool)
    requires
        cfg(o, h, z, bool_frag(v)),
        CountRA::op(o, h).count >= bool_count(true),
    ensures
        v,
{
}

/// `add f += true`: {cfg(o, h, z, v), ¬v} ⟹ {cfg(o + 1, h, z, true)}.
pub proof fn bool_add_true(o: CountRA, h: CountRA, z: CountRA, v: bool)
    requires
        cfg(o, h, z, bool_frag(v)),
        !v,
    ensures
        cfg(CountRA { count: o.count + bool_count(true) }, h, z, bool_frag(true)),
{
}

// ---------------------------------------------------------------------------
// `persistent_count`
/// `have f >= (x)`: {cfg(o, h, z, v), o·h ≥ x} ⟹ {v ≥ x}.
pub proof fn pcount_have(o: PersistentCountRA, h: PersistentCountRA, z: PersistentCountRA, v: nat, x: nat)
    requires
        cfg(o, h, z, PersistentCountRA { count: v }),
        PersistentCountRA::op(o, h).count >= x,
    ensures
        v >= x,
{
}

/// `add f (union)= (x)`: {cfg(o, h, z, v)} ⟹ {cfg(o·x, h, z, max(v, x))}.
pub proof fn pcount_add(o: PersistentCountRA, h: PersistentCountRA, z: PersistentCountRA, v: nat, x: nat)
    requires
        cfg(o, h, z, PersistentCountRA { count: v }),
    ensures
        cfg(PersistentCountRA::op(o, PersistentCountRA { count: x }), h, z, PersistentCountRA { count: smi::nat_max(v, x) }),
{
}

// ---------------------------------------------------------------------------
// `persistent_bool`
/// `have f >= (x)`: {cfg(o, h, z, v), o·h ≥ [x]} ⟹ {x ⟹ v}.
pub proof fn pbool_have(o: PersistentCountRA, h: PersistentCountRA, z: PersistentCountRA, v: bool, x: bool)
    requires
        cfg(o, h, z, persistent_bool_frag(v)),
        PersistentCountRA::op(o, h).count >= bool_count(x),
    ensures
        x ==> v,
{
}

/// `add f (union)= (x)`: {cfg(o, h, z, v)} ⟹ {cfg(o·[x], h, z, v ∨ x)}.
pub proof fn pbool_add(o: PersistentCountRA, h: PersistentCountRA, z: PersistentCountRA, v: bool, x: bool)
    requires
        cfg(o, h, z, persistent_bool_frag(v)),
    ensures
        cfg(PersistentCountRA::op(o, persistent_bool_frag(x)), h, z, persistent_bool_frag(v || x)),
{
}

/// `have f >= true`: {cfg(o, h, z, v), o·h ≥ 1} ⟹ {v}.
pub proof fn pbool_have_true(o: PersistentCountRA, h: PersistentCountRA, z: PersistentCountRA, v: bool)
    requires
        cfg(o, h, z, persistent_bool_frag(v)),
        PersistentCountRA::op(o, h).count >= bool_count(true),
    ensures
        v,
{
}

/// `add f (union)= true`: {cfg(o, h, z, v)} ⟹ {cfg(o·1, h, z, true)}.
pub proof fn pbool_add_true(o: PersistentCountRA, h: PersistentCountRA, z: PersistentCountRA, v: bool)
    requires
        cfg(o, h, z, persistent_bool_frag(v)),
    ensures
        cfg(PersistentCountRA::op(o, persistent_bool_frag(true)), h, z, persistent_bool_frag(true)),
{
}

// ---------------------------------------------------------------------------
// `variable`
/// `update f = e`: {cfg(o, h, z, Some(Exclusive(v))), o owns f} ⟹
/// {cfg(Some(Exclusive(e)), h, z, Some(Exclusive(e)))}.
pub proof fn var_update<V>(
    o: Option<ExclusiveRA<V>>,
    h: Option<ExclusiveRA<V>>,
    z: Option<ExclusiveRA<V>>,
    v: V,
    e: V,
)
    requires
        cfg(o, h, z, Some(ExclusiveRA::Exclusive(v))),
        o is Some && o->Some_0 is Exclusive,
    ensures
        cfg(Some(ExclusiveRA::Exclusive(e)), h, z, Some(ExclusiveRA::Exclusive(e))),
{
}

} // verus!
