//! Pointwise resource algebras for separable collection fields.
//!
//! Exclusive maps and sets use an optional exclusive fragment at each key;
//! persistent maps and sets use agreement; multisets use additive counts.
//! The algebra laws and local map updates below are checked proof bodies.
use super::super::prelude::*;
use super::super::multiset::Multiset;
use super::agree::AgreementRA;
use super::algebra::ResourceAlgebra;
use super::exclusive::ExclusiveRA;
use super::pcm::PCM;
use super::tsm::CountRA;

verus! {

broadcast use {super::super::imap::group_imap_lemmas, super::super::iset::group_iset_lemmas};

#[verifier::reject_recursive_types(K)]
pub struct Pointwise<K, P: PCM> {
    pub values: spec_fn(K) -> P,
}

impl<K, P: PCM> Pointwise<K, P> {
    pub open spec fn at(self, key: K) -> P {
        (self.values)(key)
    }

    pub proof fn extensionality(a: Self, b: Self)
        requires
            forall|key: K| #[trigger] a.at(key) == b.at(key),
        ensures
            a == b,
    {
        assert forall|key: K| #[trigger] (a.values)(key) == (b.values)(key) by {
            assert(a.at(key) == b.at(key));
        };
        assert(a.values =~= b.values);
    }
}

impl<K, P: PCM> ResourceAlgebra for Pointwise<K, P> {
    open spec fn valid(self) -> bool {
        forall|key: K| #[trigger] self.at(key).valid()
    }

    open spec fn op(a: Self, b: Self) -> Self {
        Self { values: |key: K| P::op(a.at(key), b.at(key)) }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        let left = Self::op(a, Self::op(b, c));
        let right = Self::op(Self::op(a, b), c);
        assert forall|key: K| #[trigger] left.at(key) == right.at(key) by {
            P::associative(a.at(key), b.at(key), c.at(key));
        };
        Self::extensionality(left, right);
    }

    proof fn commutative(a: Self, b: Self) {
        let left = Self::op(a, b);
        let right = Self::op(b, a);
        assert forall|key: K| #[trigger] left.at(key) == right.at(key) by {
            P::commutative(a.at(key), b.at(key));
        };
        Self::extensionality(left, right);
    }

    proof fn valid_op(a: Self, b: Self) {
        assert forall|key: K| #[trigger] a.at(key).valid() by {
            assert(Self::op(a, b).at(key).valid());
            P::valid_op(a.at(key), b.at(key));
        };
    }
}

impl<K, P: PCM> PCM for Pointwise<K, P> {
    open spec fn unit() -> Self {
        Self { values: |key: K| P::unit() }
    }

    proof fn op_unit(self) {
        let combined = Self::op(self, Self::unit());
        assert forall|key: K| #[trigger] combined.at(key) == self.at(key) by {
            P::op_unit(self.at(key));
        };
        Self::extensionality(combined, self);
    }

    proof fn unit_valid() {
        P::unit_valid();
    }
}

pub type MapFragment<K, V> = Pointwise<K, Option<ExclusiveRA<V>>>;
pub type PersistentMapFragment<K, V> = Pointwise<K, Option<AgreementRA<V>>>;
pub type SetFragment<K> = Pointwise<K, Option<ExclusiveRA<()>>>;
pub type PersistentSetFragment<K> = Pointwise<K, Option<AgreementRA<()>>>;
pub type MultisetFragment<V> = Pointwise<V, CountRA>;
pub type OptionFragment<V> = Option<ExclusiveRA<V>>;
pub type PersistentOptionFragment<V> = Option<AgreementRA<V>>;

pub open spec fn option_frag<V>(value: Option<V>) -> OptionFragment<V> {
    match value {
        None => None,
        Some(value) => Some(ExclusiveRA::Exclusive(value)),
    }
}

pub open spec fn persistent_option_frag<V>(value: Option<V>) -> PersistentOptionFragment<V> {
    match value {
        None => None,
        Some(value) => Some(AgreementRA::Agree(value)),
    }
}

pub proof fn option_join<V>(left: Option<V>, right: Option<V>)
    requires
        left is None || right is None,
    ensures
        OptionFragment::op(option_frag(left), option_frag(right))
            == option_frag(if right is Some { right } else { left }),
{
}

pub proof fn option_owned_frame<V>(
    owned: OptionFragment<V>, frame: OptionFragment<V>, whole: Option<V>, value: V,
)
    requires
        OptionFragment::op(owned, frame) == option_frag(whole),
        owned == Some(ExclusiveRA::Exclusive(value)),
    ensures
        whole == Some(value),
        frame is None,
{
}

pub proof fn option_add_frame<V>(
    owned: OptionFragment<V>, frame: OptionFragment<V>, whole: Option<V>, value: V,
)
    requires
        OptionFragment::op(owned, frame) == option_frag(whole),
        whole is None,
    ensures
        owned is None,
        frame is None,
        OptionFragment::op(Some(ExclusiveRA::Exclusive(value)), frame) == option_frag(Some(value)),
{
}

pub proof fn option_remove_frame<V>(
    owned: OptionFragment<V>, frame: OptionFragment<V>, whole: Option<V>, value: V,
)
    requires
        OptionFragment::op(owned, frame) == option_frag(whole),
        owned == Some(ExclusiveRA::Exclusive(value)),
    ensures
        whole == Some(value),
        frame is None,
        OptionFragment::<V>::op(None, frame) == option_frag(None),
{
    option_owned_frame(owned, frame, whole, value);
}

/// Replace an exclusively owned optional value in one protocol step.
/// This is the remove-then-add case: ownership forces the frame to be empty.
pub proof fn option_replace_frame<V>(
    owned: OptionFragment<V>, frame: OptionFragment<V>, whole: Option<V>,
    previous: V, replacement: V,
)
    requires
        OptionFragment::op(owned, frame) == option_frag(whole),
        owned == Some(ExclusiveRA::Exclusive(previous)),
    ensures
        whole == Some(previous),
        frame is None,
        OptionFragment::op(Some(ExclusiveRA::Exclusive(replacement)), frame)
            == option_frag(Some(replacement)),
{
    option_owned_frame(owned, frame, whole, previous);
}

pub proof fn persistent_option_owned_frame<V>(
    owned: PersistentOptionFragment<V>,
    frame: PersistentOptionFragment<V>,
    whole: Option<V>,
    value: V,
)
    requires
        PersistentOptionFragment::op(owned, frame) == persistent_option_frag(whole),
        owned == Some(AgreementRA::Agree(value)),
    ensures
        whole == Some(value),
{
}

pub proof fn persistent_option_insert_frame<V>(
    owned: PersistentOptionFragment<V>,
    frame: PersistentOptionFragment<V>,
    whole: Option<V>,
    value: V,
)
    requires
        PersistentOptionFragment::op(owned, frame) == persistent_option_frag(whole),
        whole is Some ==> whole == Some(value),
    ensures
        PersistentOptionFragment::op(Some(AgreementRA::Agree(value)), frame)
            == persistent_option_frag(Some(value)),
{
}

pub proof fn persistent_option_idempotent<V>(value: Option<V>)
    ensures
        PersistentOptionFragment::op(persistent_option_frag(value), persistent_option_frag(value))
            == persistent_option_frag(value),
{
}

// General optional operands, including the neutral None operand.
pub open spec fn option_contains_operand<V>(owned: OptionFragment<V>, operand: Option<V>) -> bool {
    match operand { None => true, Some(value) => owned == Some(ExclusiveRA::Exclusive(value)) }
}
pub open spec fn option_remove_operand<V>(owned: OptionFragment<V>, operand: Option<V>) -> OptionFragment<V> {
    match operand { None => owned, Some(_) => None }
}
pub open spec fn option_union<V>(whole: Option<V>, added: Option<V>) -> Option<V> {
    if added is Some { added } else { whole }
}
pub open spec fn option_subtract<V>(whole: Option<V>, removed: Option<V>) -> Option<V> {
    if removed is Some { None } else { whole }
}

pub proof fn option_have_general_frame<V>(owned: OptionFragment<V>, frame: OptionFragment<V>,
    whole: Option<V>, operand: Option<V>)
    requires OptionFragment::op(owned, frame) == option_frag(whole),
        option_contains_operand(owned, operand),
    ensures operand is Some ==> whole == operand,
{
    match operand {
        None => {},
        Some(value) => option_owned_frame(owned, frame, whole, value),
    }
}

pub proof fn option_add_general_frame<V>(owned: OptionFragment<V>, frame: OptionFragment<V>,
    whole: Option<V>, operand: Option<V>)
    requires OptionFragment::op(owned, frame) == option_frag(whole),
        whole is None || operand is None,
    ensures OptionFragment::op(OptionFragment::op(owned, option_frag(operand)), frame)
        == option_frag(option_union(whole, operand)),
        operand is None ==> OptionFragment::op(owned, option_frag(operand)) == owned,
        operand is Some ==> owned is None && frame is None,
{
    match operand {
        None => OptionFragment::op_unit(owned),
        Some(value) => option_add_frame(owned, frame, whole, value),
    }
}

pub proof fn option_remove_general_frame<V>(owned: OptionFragment<V>, frame: OptionFragment<V>,
    whole: Option<V>, operand: Option<V>)
    requires OptionFragment::op(owned, frame) == option_frag(whole),
        option_contains_operand(owned, operand),
    ensures OptionFragment::op(option_remove_operand(owned, operand), frame)
        == option_frag(option_subtract(whole, operand)),
        operand is None ==> option_remove_operand(owned, operand) == owned,
        operand is Some ==> whole == operand && frame is None,
{
    match operand {
        None => {},
        Some(value) => option_remove_frame(owned, frame, whole, value),
    }
}

pub open spec fn persistent_option_contains_operand<V>(owned: PersistentOptionFragment<V>, operand: Option<V>) -> bool {
    match operand { None => true, Some(value) => owned == Some(AgreementRA::Agree(value)) }
}
pub proof fn persistent_option_have_general_frame<V>(owned: PersistentOptionFragment<V>,
    frame: PersistentOptionFragment<V>, whole: Option<V>, operand: Option<V>)
    requires PersistentOptionFragment::op(owned, frame) == persistent_option_frag(whole),
        persistent_option_contains_operand(owned, operand),
    ensures operand is Some ==> whole == operand,
{
    match operand {
        None => {},
        Some(value) => persistent_option_owned_frame(owned, frame, whole, value),
    }
}
pub proof fn persistent_option_union_general_frame<V>(owned: PersistentOptionFragment<V>,
    frame: PersistentOptionFragment<V>, whole: Option<V>, operand: Option<V>)
    requires PersistentOptionFragment::op(owned, frame) == persistent_option_frag(whole),
        whole is None || operand is None || whole == operand,
    ensures PersistentOptionFragment::op(
        PersistentOptionFragment::op(owned, persistent_option_frag(operand)), frame)
        == persistent_option_frag(option_union(whole, operand)),
        operand is None ==> PersistentOptionFragment::op(owned, persistent_option_frag(operand)) == owned,
{
    match operand {
        None => PersistentOptionFragment::op_unit(owned),
        Some(value) => {
            persistent_option_insert_frame(owned, frame, whole, value);
            assert(PersistentOptionFragment::op(owned, persistent_option_frag(operand))
                == Some(AgreementRA::Agree(value)));
        }
    }
}


pub open spec fn map_frag<K, V>(map: IMap<K, V>) -> MapFragment<K, V> {
    Pointwise {
        values: |key: K| if map.dom().contains(key) {
            Some(ExclusiveRA::Exclusive(map[key]))
        } else {
            None
        },
    }
}

pub open spec fn persistent_map_frag<K, V>(map: IMap<K, V>) -> PersistentMapFragment<K, V> {
    Pointwise {
        values: |key: K| if map.dom().contains(key) {
            Some(AgreementRA::Agree(map[key]))
        } else {
            None
        },
    }
}

pub open spec fn set_frag<K>(set: ISet<K>) -> SetFragment<K> {
    Pointwise {
        values: |key: K| if set.contains(key) { Some(ExclusiveRA::Exclusive(())) } else { None },
    }
}

pub open spec fn persistent_set_frag<K>(set: ISet<K>) -> PersistentSetFragment<K> {
    Pointwise {
        values: |key: K| if set.contains(key) { Some(AgreementRA::Agree(())) } else { None },
    }
}

pub open spec fn multiset_frag<V>(multiset: Multiset<V>) -> MultisetFragment<V> {
    Pointwise { values: |value: V| CountRA { count: multiset.count(value) } }
}

pub open spec fn replace_at<K, P: PCM>(fragment: Pointwise<K, P>, key: K, value: P)
    -> Pointwise<K, P>
{
    Pointwise { values: |other: K| if other == key { value } else { fragment.at(other) } }
}

/// Disjoint submaps compose into ownership of their union.
pub proof fn map_join<K, V>(left: IMap<K, V>, right: IMap<K, V>)
    requires
        left.dom().disjoint(right.dom()),
    ensures
        MapFragment::op(map_frag(left), map_frag(right))
            == map_frag(left.union_prefer_right(right)),
{
    let combined = MapFragment::op(map_frag(left), map_frag(right));
    let whole = map_frag(left.union_prefer_right(right));
    assert forall|key: K| #[trigger] combined.at(key) == whole.at(key) by {};
    Pointwise::extensionality(combined, whole);
}

pub proof fn map_frag_valid<K, V>(map: IMap<K, V>)
    ensures
        map_frag(map).valid(),
{
}

/// A local map token determines its full state's entry and excludes a second
/// owner of the same key in the untouched frame.
pub proof fn map_owned_frame<K, V>(
    owned: MapFragment<K, V>,
    frame: MapFragment<K, V>,
    map: IMap<K, V>,
    key: K,
    value: V,
)
    requires
        MapFragment::op(owned, frame) == map_frag(map),
        owned.at(key) == Some(ExclusiveRA::Exclusive(value)),
    ensures
        map.dom().contains(key),
        map[key] == value,
        frame.at(key) is None,
{
    assert(MapFragment::op(owned, frame).at(key) == map_frag(map).at(key));
}

/// Replace an owned entry while every other key, including all keys in the
/// frame, remains unchanged.
pub proof fn map_replace_frame<K, V>(
    owned: MapFragment<K, V>,
    frame: MapFragment<K, V>,
    map: IMap<K, V>,
    key: K,
    old_value: V,
    new_value: V,
)
    requires
        MapFragment::op(owned, frame) == map_frag(map),
        owned.at(key) == Some(ExclusiveRA::Exclusive(old_value)),
    ensures
        MapFragment::op(replace_at(owned, key, Some(ExclusiveRA::Exclusive(new_value))), frame)
            == map_frag(map.insert(key, new_value)),
{
    map_owned_frame(owned, frame, map, key, old_value);
    let combined = MapFragment::op(
        replace_at(owned, key, Some(ExclusiveRA::Exclusive(new_value))),
        frame,
    );
    let whole = map_frag(map.insert(key, new_value));
    assert forall|other: K| #[trigger] combined.at(other) == whole.at(other) by {
        assert(MapFragment::op(owned, frame).at(other) == map_frag(map).at(other));
    };
    Pointwise::extensionality(combined, whole);
}

/// Consume an owned entry, removing it from the full state's map.
pub proof fn map_remove_frame<K, V>(
    owned: MapFragment<K, V>,
    frame: MapFragment<K, V>,
    map: IMap<K, V>,
    key: K,
    value: V,
)
    requires
        MapFragment::op(owned, frame) == map_frag(map),
        owned.at(key) == Some(ExclusiveRA::Exclusive(value)),
    ensures
        MapFragment::op(replace_at(owned, key, None), frame) == map_frag(map.remove(key)),
{
    map_owned_frame(owned, frame, map, key, value);
    let combined = MapFragment::op(replace_at(owned, key, None), frame);
    let whole = map_frag(map.remove(key));
    assert forall|other: K| #[trigger] combined.at(other) == whole.at(other) by {
        assert(MapFragment::op(owned, frame).at(other) == map_frag(map).at(other));
    };
    Pointwise::extensionality(combined, whole);
}

/// Adding an entry requires absence from the full state. Absence from the
/// caller's own fragment alone does not exclude ownership in a frame.
pub proof fn map_add_frame<K, V>(
    owned: MapFragment<K, V>,
    frame: MapFragment<K, V>,
    map: IMap<K, V>,
    key: K,
    value: V,
)
    requires
        MapFragment::op(owned, frame) == map_frag(map),
        !map.dom().contains(key),
    ensures
        owned.at(key) is None,
        frame.at(key) is None,
        MapFragment::op(replace_at(owned, key, Some(ExclusiveRA::Exclusive(value))), frame)
            == map_frag(map.insert(key, value)),
{
    assert(MapFragment::op(owned, frame).at(key) == map_frag(map).at(key));
    let combined = MapFragment::op(
        replace_at(owned, key, Some(ExclusiveRA::Exclusive(value))),
        frame,
    );
    let whole = map_frag(map.insert(key, value));
    assert forall|other: K| #[trigger] combined.at(other) == whole.at(other) by {
        assert(MapFragment::op(owned, frame).at(other) == map_frag(map).at(other));
    };
    Pointwise::extensionality(combined, whole);
}

/// Persistent entries combine whenever overlapping entries agree.
pub proof fn persistent_map_join<K, V>(left: IMap<K, V>, right: IMap<K, V>)
    requires
        forall|key: K| left.dom().contains(key) && right.dom().contains(key)
            ==> left[key] == right[key],
    ensures
        PersistentMapFragment::op(persistent_map_frag(left), persistent_map_frag(right))
            == persistent_map_frag(left.union_prefer_right(right)),
{
    let combined = PersistentMapFragment::op(persistent_map_frag(left), persistent_map_frag(right));
    let whole = persistent_map_frag(left.union_prefer_right(right));
    assert forall|key: K| #[trigger] combined.at(key) == whole.at(key) by {};
    Pointwise::extensionality(combined, whole);
}

pub proof fn persistent_map_idempotent<K, V>(map: IMap<K, V>)
    ensures
        PersistentMapFragment::op(persistent_map_frag(map), persistent_map_frag(map))
            == persistent_map_frag(map),
{
    persistent_map_join(map, map);
    assert(map.union_prefer_right(map) =~= map);
}

/// A persistent observation agrees with the complete map, even when its entry
/// is also present in the frame.
pub proof fn persistent_map_owned_frame<K, V>(
    owned: PersistentMapFragment<K, V>,
    frame: PersistentMapFragment<K, V>,
    map: IMap<K, V>,
    key: K,
    value: V,
)
    requires
        PersistentMapFragment::op(owned, frame) == persistent_map_frag(map),
        owned.at(key) == Some(AgreementRA::Agree(value)),
    ensures
        map.dom().contains(key),
        map[key] == value,
{
    assert(PersistentMapFragment::op(owned, frame).at(key) == persistent_map_frag(map).at(key));
}

/// Persistent insertion can add a fresh entry or another observation of an
/// existing entry. It cannot change an existing value, including a frame's.
pub proof fn persistent_map_insert_frame<K, V>(
    owned: PersistentMapFragment<K, V>,
    frame: PersistentMapFragment<K, V>,
    map: IMap<K, V>,
    key: K,
    value: V,
)
    requires
        PersistentMapFragment::op(owned, frame) == persistent_map_frag(map),
        map.dom().contains(key) ==> map[key] == value,
    ensures
        PersistentMapFragment::op(
            replace_at(owned, key, Some(AgreementRA::Agree(value))), frame,
        ) == persistent_map_frag(map.insert(key, value)),
{
    assert(PersistentMapFragment::op(owned, frame).at(key) == persistent_map_frag(map).at(key));
    let combined = PersistentMapFragment::op(
        replace_at(owned, key, Some(AgreementRA::Agree(value))), frame,
    );
    let whole = persistent_map_frag(map.insert(key, value));
    assert forall|other: K| #[trigger] combined.at(other) == whole.at(other) by {
        assert(PersistentMapFragment::op(owned, frame).at(other)
            == persistent_map_frag(map).at(other));
    };
    Pointwise::extensionality(combined, whole);
}

pub open spec fn map_remove_many<K, V>(owned: MapFragment<K, V>, keys: ISet<K>)
    -> MapFragment<K, V>
{
    Pointwise { values: |key: K| if keys.contains(key) { None } else { owned.at(key) } }
}

pub proof fn map_remove_many_frame<K, V>(
    owned: MapFragment<K, V>, frame: MapFragment<K, V>,
    map: IMap<K, V>, removed: IMap<K, V>,
)
    requires
        MapFragment::op(owned, frame) == map_frag(map),
        forall|key: K| removed.contains_key(key)
            ==> #[trigger] owned.at(key) == Some(ExclusiveRA::Exclusive(removed[key])),
    ensures
        removed.submap_of(map),
        MapFragment::op(map_remove_many(owned, removed.dom()), frame)
            == map_frag(map.remove_keys(removed.dom())),
{
    assert forall|key: K| #[trigger] removed.dom().contains(key) implies
        #[trigger] map.dom().contains(key) && removed[key] == map[key] by {
        map_owned_frame(owned, frame, map, key, removed[key]);
    };
    let combined = MapFragment::op(map_remove_many(owned, removed.dom()), frame);
    let whole = map_frag(map.remove_keys(removed.dom()));
    assert forall|key: K| #[trigger] combined.at(key) == whole.at(key) by {
        if removed.contains_key(key) {
            map_owned_frame(owned, frame, map, key, removed[key]);
        } else {
            assert(MapFragment::op(owned, frame).at(key) == map_frag(map).at(key));
        }
    };
    Pointwise::extensionality(combined, whole);
}

pub proof fn map_add_many_frame<K, V>(
    owned: MapFragment<K, V>, frame: MapFragment<K, V>,
    map: IMap<K, V>, added: IMap<K, V>,
)
    requires
        MapFragment::op(owned, frame) == map_frag(map),
        map.dom().disjoint(added.dom()),
    ensures
        MapFragment::op(MapFragment::op(owned, map_frag(added)), frame)
            == map_frag(map.union_prefer_right(added)),
{
    MapFragment::associative(owned, map_frag(added), frame);
    MapFragment::commutative(map_frag(added), frame);
    MapFragment::associative(owned, frame, map_frag(added));
    map_join(map, added);
}

pub proof fn map_have_many_frame<K, V>(
    owned: MapFragment<K, V>, frame: MapFragment<K, V>,
    map: IMap<K, V>, observed: IMap<K, V>,
)
    requires
        MapFragment::op(owned, frame) == map_frag(map),
        forall|key: K| observed.contains_key(key)
            ==> #[trigger] owned.at(key) == Some(ExclusiveRA::Exclusive(observed[key])),
    ensures
        observed.submap_of(map),
{
    map_remove_many_frame(owned, frame, map, observed);
}

/// Bulk persistent union permits overlap only when the complete map agrees.
pub proof fn persistent_map_union_frame<K, V>(
    owned: PersistentMapFragment<K, V>, frame: PersistentMapFragment<K, V>,
    map: IMap<K, V>, added: IMap<K, V>,
)
    requires
        PersistentMapFragment::op(owned, frame) == persistent_map_frag(map),
        map.agrees(added),
    ensures
        PersistentMapFragment::op(
            PersistentMapFragment::op(owned, persistent_map_frag(added)), frame,
        ) == persistent_map_frag(map.union_prefer_right(added)),
{
    PersistentMapFragment::associative(owned, persistent_map_frag(added), frame);
    PersistentMapFragment::commutative(persistent_map_frag(added), frame);
    PersistentMapFragment::associative(owned, frame, persistent_map_frag(added));
    persistent_map_join(map, added);
}

pub proof fn persistent_map_have_many_frame<K, V>(
    owned: PersistentMapFragment<K, V>, frame: PersistentMapFragment<K, V>,
    map: IMap<K, V>, observed: IMap<K, V>,
)
    requires
        PersistentMapFragment::op(owned, frame) == persistent_map_frag(map),
        forall|key: K| observed.contains_key(key)
            ==> #[trigger] owned.at(key) == Some(AgreementRA::Agree(observed[key])),
    ensures
        observed.submap_of(map),
{
    assert forall|key: K| #[trigger] observed.dom().contains(key) implies
        #[trigger] map.dom().contains(key) && observed[key] == map[key] by {
        persistent_map_owned_frame(owned, frame, map, key, observed[key]);
    };
}

pub proof fn set_join<K>(left: ISet<K>, right: ISet<K>)
    requires
        left.disjoint(right),
    ensures
        SetFragment::op(set_frag(left), set_frag(right)) == set_frag(left.union(right)),
{
    let combined = SetFragment::op(set_frag(left), set_frag(right));
    let whole = set_frag(left.union(right));
    assert forall|key: K| #[trigger] combined.at(key) == whole.at(key) by {};
    Pointwise::extensionality(combined, whole);
}

pub proof fn set_owned_frame<K>(
    owned: SetFragment<K>, frame: SetFragment<K>, set: ISet<K>, key: K,
)
    requires
        SetFragment::op(owned, frame) == set_frag(set),
        owned.at(key) == Some(ExclusiveRA::Exclusive(())),
    ensures
        set.contains(key),
        frame.at(key) is None,
{
    assert(SetFragment::op(owned, frame).at(key) == set_frag(set).at(key));
}


/// A token's exclusive map entry stays exact in any included upper fragment.
pub proof fn map_included_owned_at<K, V>(
    owned: MapFragment<K, V>, rest: MapFragment<K, V>, frame: MapFragment<K, V>,
    map: IMap<K, V>, key: K, value: V,
)
    requires
        MapFragment::op(MapFragment::op(owned, rest), frame) == map_frag(map),
        owned.at(key) == Some(ExclusiveRA::Exclusive(value)),
    ensures
        MapFragment::op(owned, rest).at(key) == Some(ExclusiveRA::Exclusive(value)),
        map.contains_key(key),
        map[key] == value,
{
    assert(MapFragment::op(MapFragment::op(owned, rest), frame).at(key) == map_frag(map).at(key));
}

/// A token's exclusive set element stays exact in any included upper fragment.
pub proof fn set_included_owned_at<K>(
    owned: SetFragment<K>, rest: SetFragment<K>, frame: SetFragment<K>, set: ISet<K>, key: K,
)
    requires
        SetFragment::op(SetFragment::op(owned, rest), frame) == set_frag(set),
        owned.at(key) == Some(ExclusiveRA::Exclusive(())),
    ensures
        SetFragment::op(owned, rest).at(key) == Some(ExclusiveRA::Exclusive(())),
        set.contains(key),
{
    assert(SetFragment::op(SetFragment::op(owned, rest), frame).at(key) == set_frag(set).at(key));
}

/// A token's agreed persistent value stays exact in any included upper fragment.
pub proof fn persistent_option_included_owned<V>(
    owned: PersistentOptionFragment<V>, rest: PersistentOptionFragment<V>,
    frame: PersistentOptionFragment<V>, whole: Option<V>, value: V,
)
    requires
        PersistentOptionFragment::op(PersistentOptionFragment::op(owned, rest), frame)
            == persistent_option_frag(whole),
        owned == Some(AgreementRA::Agree(value)),
    ensures
        PersistentOptionFragment::op(owned, rest) == Some(AgreementRA::Agree(value)),
        whole == Some(value),
{
}

/// The same for a map whose entries a collection token owns.
pub proof fn map_included_owned_many<K, V>(
    owned: MapFragment<K, V>, rest: MapFragment<K, V>, frame: MapFragment<K, V>,
    map: IMap<K, V>, observed: IMap<K, V>,
)
    requires
        MapFragment::op(MapFragment::op(owned, rest), frame) == map_frag(map),
        forall|key: K| observed.contains_key(key)
            ==> #[trigger] owned.at(key) == Some(ExclusiveRA::Exclusive(observed[key])),
    ensures
        forall|key: K| observed.contains_key(key)
            ==> #[trigger] MapFragment::op(owned, rest).at(key) == Some(ExclusiveRA::Exclusive(observed[key])),
        observed.submap_of(map),
{
    assert forall|key: K| observed.contains_key(key)
        implies #[trigger] MapFragment::op(owned, rest).at(key) == Some(ExclusiveRA::Exclusive(observed[key]))
            && map.contains_key(key) && map[key] == observed[key] by {
        map_included_owned_at(owned, rest, frame, map, key, observed[key]);
    }
    MapFragment::associative(owned, rest, frame);
    map_have_many_frame(owned, MapFragment::op(rest, frame), map, observed);
}

/// The same for a set whose elements a collection token owns.
pub proof fn set_included_owned_many<K>(
    owned: SetFragment<K>, rest: SetFragment<K>, frame: SetFragment<K>, set: ISet<K>, observed: ISet<K>,
)
    requires
        SetFragment::op(SetFragment::op(owned, rest), frame) == set_frag(set),
        forall|key: K| observed.contains(key) ==> #[trigger] owned.at(key) == Some(ExclusiveRA::Exclusive(())),
    ensures
        forall|key: K| observed.contains(key)
            ==> #[trigger] SetFragment::op(owned, rest).at(key) == Some(ExclusiveRA::Exclusive(())),
        observed.subset_of(set),
{
    assert forall|key: K| observed.contains(key)
        implies #[trigger] SetFragment::op(owned, rest).at(key) == Some(ExclusiveRA::Exclusive(()))
            && set.contains(key) by {
        set_included_owned_at(owned, rest, frame, set, key);
    }
    SetFragment::associative(owned, rest, frame);
    set_have_many_frame(owned, SetFragment::op(rest, frame), set, observed);
}

/// The owned and the shared part of a valid map fragment hold exclusive
/// entries, and never the same key. Operations that observe a map field again
/// after removing from it rely on this to separate the operands.
pub proof fn map_parts_exclusive<K, V>(
    owned: MapFragment<K, V>, shared: MapFragment<K, V>, frame: MapFragment<K, V>, map: IMap<K, V>,
)
    requires
        MapFragment::op(MapFragment::op(owned, shared), frame) == map_frag(map),
    ensures
        forall|key: K| #![trigger owned.at(key)] #![trigger shared.at(key)]
            (owned.at(key) is None || shared.at(key) is None)
            && (owned.at(key) is Some ==> owned.at(key)->Some_0 is Exclusive)
            && (shared.at(key) is Some ==> shared.at(key)->Some_0 is Exclusive),
{
    assert forall|key: K| #![trigger owned.at(key)] #![trigger shared.at(key)]
        (owned.at(key) is None || shared.at(key) is None)
        && (owned.at(key) is Some ==> owned.at(key)->Some_0 is Exclusive)
        && (shared.at(key) is Some ==> shared.at(key)->Some_0 is Exclusive) by {
        assert(MapFragment::op(MapFragment::op(owned, shared), frame).at(key) == map_frag(map).at(key));
    }
}

/// A map token collection included in the shared part `shared` of a valid
/// fragment: its entries are exact in `shared` and absent from the owned part.
pub proof fn map_shared_included_many<K, V>(
    tok: MapFragment<K, V>, rest: MapFragment<K, V>, owned: MapFragment<K, V>,
    shared: MapFragment<K, V>, frame: MapFragment<K, V>, map: IMap<K, V>, observed: IMap<K, V>,
)
    requires
        shared == MapFragment::op(tok, rest),
        MapFragment::op(MapFragment::op(owned, shared), frame) == map_frag(map),
        forall|key: K| observed.contains_key(key)
            ==> #[trigger] tok.at(key) == Some(ExclusiveRA::Exclusive(observed[key])),
    ensures
        forall|key: K| #![trigger shared.at(key)] #![trigger owned.at(key)]
            #![trigger observed.contains_key(key)] observed.contains_key(key)
            ==> shared.at(key) == Some(ExclusiveRA::Exclusive(observed[key])) && owned.at(key) is None,
{
    assert forall|key: K| #![trigger shared.at(key)] #![trigger owned.at(key)]
        #![trigger observed.contains_key(key)] observed.contains_key(key)
        implies shared.at(key) == Some(ExclusiveRA::Exclusive(observed[key])) && owned.at(key) is None by {
        assert(tok.at(key) == Some(ExclusiveRA::Exclusive(observed[key])));
        assert(MapFragment::op(MapFragment::op(owned, shared), frame).at(key) == map_frag(map).at(key));
    }
}

/// `map_parts_exclusive` for a set fragment.
pub proof fn set_parts_exclusive<K>(
    owned: SetFragment<K>, shared: SetFragment<K>, frame: SetFragment<K>, set: ISet<K>,
)
    requires
        SetFragment::op(SetFragment::op(owned, shared), frame) == set_frag(set),
    ensures
        forall|key: K| #![trigger owned.at(key)] #![trigger shared.at(key)]
            (owned.at(key) is None || shared.at(key) is None)
            && (owned.at(key) is Some ==> owned.at(key)->Some_0 is Exclusive)
            && (shared.at(key) is Some ==> shared.at(key)->Some_0 is Exclusive),
{
    assert forall|key: K| #![trigger owned.at(key)] #![trigger shared.at(key)]
        (owned.at(key) is None || shared.at(key) is None)
        && (owned.at(key) is Some ==> owned.at(key)->Some_0 is Exclusive)
        && (shared.at(key) is Some ==> shared.at(key)->Some_0 is Exclusive) by {
        assert(SetFragment::op(SetFragment::op(owned, shared), frame).at(key) == set_frag(set).at(key));
    }
}

/// `map_shared_included_many` for a set token collection.
pub proof fn set_shared_included_many<K>(
    tok: SetFragment<K>, rest: SetFragment<K>, owned: SetFragment<K>,
    shared: SetFragment<K>, frame: SetFragment<K>, set: ISet<K>, observed: ISet<K>,
)
    requires
        shared == SetFragment::op(tok, rest),
        SetFragment::op(SetFragment::op(owned, shared), frame) == set_frag(set),
        forall|key: K| observed.contains(key) ==> #[trigger] tok.at(key) == Some(ExclusiveRA::Exclusive(())),
    ensures
        forall|key: K| #![trigger shared.at(key)] #![trigger owned.at(key)]
            #![trigger observed.contains(key)] observed.contains(key)
            ==> shared.at(key) == Some(ExclusiveRA::Exclusive(())) && owned.at(key) is None,
{
    assert forall|key: K| #![trigger shared.at(key)] #![trigger owned.at(key)]
        #![trigger observed.contains(key)] observed.contains(key)
        implies shared.at(key) == Some(ExclusiveRA::Exclusive(())) && owned.at(key) is None by {
        assert(tok.at(key) == Some(ExclusiveRA::Exclusive(())));
        assert(SetFragment::op(SetFragment::op(owned, shared), frame).at(key) == set_frag(set).at(key));
    }
}

/// A whole exclusive observation justifies a general set Have operand.
pub proof fn set_have_many_frame<K>(
    owned: SetFragment<K>,
    frame: SetFragment<K>,
    set: ISet<K>,
    observed: ISet<K>,
)
    requires
        SetFragment::op(owned, frame) == set_frag(set),
        forall|key: K|
            observed.contains(key) ==> #[trigger] owned.at(key) == Some(ExclusiveRA::Exclusive(())),
    ensures
        observed.subset_of(set),
{
    assert forall|key: K| observed.contains(key) implies set.contains(key) by {
        set_owned_frame(owned, frame, set, key);
    };
}

pub proof fn set_remove_frame<K>(
    owned: SetFragment<K>, frame: SetFragment<K>, set: ISet<K>, key: K,
)
    requires
        SetFragment::op(owned, frame) == set_frag(set),
        owned.at(key) == Some(ExclusiveRA::Exclusive(())),
    ensures
        SetFragment::op(replace_at(owned, key, None), frame) == set_frag(set.remove(key)),
{
    set_owned_frame(owned, frame, set, key);
    let combined = SetFragment::op(replace_at(owned, key, None), frame);
    let whole = set_frag(set.remove(key));
    assert forall|other: K| #[trigger] combined.at(other) == whole.at(other) by {
        assert(SetFragment::op(owned, frame).at(other) == set_frag(set).at(other));
    };
    Pointwise::extensionality(combined, whole);
}

pub proof fn set_add_frame<K>(
    owned: SetFragment<K>, frame: SetFragment<K>, set: ISet<K>, key: K,
)
    requires
        SetFragment::op(owned, frame) == set_frag(set),
        !set.contains(key),
    ensures
        owned.at(key) is None,
        frame.at(key) is None,
        SetFragment::op(
            replace_at(owned, key, Some(ExclusiveRA::Exclusive(()))), frame,
        ) == set_frag(set.insert(key)),
{
    assert(SetFragment::op(owned, frame).at(key) == set_frag(set).at(key));
    let combined = SetFragment::op(
        replace_at(owned, key, Some(ExclusiveRA::Exclusive(()))), frame,
    );
    let whole = set_frag(set.insert(key));
    assert forall|other: K| #[trigger] combined.at(other) == whole.at(other) by {
        assert(SetFragment::op(owned, frame).at(other) == set_frag(set).at(other));
    };
    Pointwise::extensionality(combined, whole);
}

pub open spec fn set_remove_many<K>(owned: SetFragment<K>, removed: ISet<K>)
    -> SetFragment<K>
{
    Pointwise { values: |key: K| if removed.contains(key) { None } else { owned.at(key) } }
}

/// Bulk removal consumes local ownership of every removed member.
pub proof fn set_remove_many_frame<K>(
    owned: SetFragment<K>, frame: SetFragment<K>, set: ISet<K>, removed: ISet<K>,
)
    requires
        SetFragment::op(owned, frame) == set_frag(set),
        forall|key: K| removed.contains(key)
            ==> #[trigger] owned.at(key) == Some(ExclusiveRA::Exclusive(())),
    ensures
        removed.subset_of(set),
        SetFragment::op(set_remove_many(owned, removed), frame)
            == set_frag(set.difference(removed)),
{
    assert forall|key: K| removed.contains(key) implies set.contains(key) by {
        set_owned_frame(owned, frame, set, key);
    };
    let combined = SetFragment::op(set_remove_many(owned, removed), frame);
    let whole = set_frag(set.difference(removed));
    assert forall|key: K| #[trigger] combined.at(key) == whole.at(key) by {
        if removed.contains(key) {
            set_owned_frame(owned, frame, set, key);
        } else {
            assert(SetFragment::op(owned, frame).at(key) == set_frag(set).at(key));
        }
    };
    Pointwise::extensionality(combined, whole);
}

/// Bulk addition requires absence from the entire state, including its frame.
pub proof fn set_add_many_frame<K>(
    owned: SetFragment<K>, frame: SetFragment<K>, set: ISet<K>, added: ISet<K>,
)
    requires
        SetFragment::op(owned, frame) == set_frag(set),
        set.disjoint(added),
    ensures
        SetFragment::op(SetFragment::op(owned, set_frag(added)), frame)
            == set_frag(set.union(added)),
{
    SetFragment::associative(owned, set_frag(added), frame);
    SetFragment::commutative(set_frag(added), frame);
    SetFragment::associative(owned, frame, set_frag(added));
    set_join(set, added);
}

/// A whole persistent observation can justify a general set Have operand.
pub proof fn persistent_set_have_many_frame<K>(
    owned: PersistentSetFragment<K>, frame: PersistentSetFragment<K>,
    set: ISet<K>, observed: ISet<K>,
)
    requires
        PersistentSetFragment::op(owned, frame) == persistent_set_frag(set),
        forall|key: K| observed.contains(key)
            ==> #[trigger] owned.at(key) == Some(AgreementRA::Agree(())),
    ensures
        observed.subset_of(set),
{
    assert forall|key: K| observed.contains(key) implies set.contains(key) by {
        persistent_set_owned_frame(owned, frame, set, key);
    };
}

pub proof fn persistent_set_join<K>(left: ISet<K>, right: ISet<K>)
    ensures
        PersistentSetFragment::op(persistent_set_frag(left), persistent_set_frag(right))
            == persistent_set_frag(left.union(right)),
{
    let combined = PersistentSetFragment::op(persistent_set_frag(left), persistent_set_frag(right));
    let whole = persistent_set_frag(left.union(right));
    assert forall|key: K| #[trigger] combined.at(key) == whole.at(key) by {};
    Pointwise::extensionality(combined, whole);
}

pub proof fn persistent_set_idempotent<K>(set: ISet<K>)
    ensures
        PersistentSetFragment::op(persistent_set_frag(set), persistent_set_frag(set))
            == persistent_set_frag(set),
{
    persistent_set_join(set, set);
    assert(set.union(set) =~= set);
}

pub proof fn persistent_set_owned_frame<K>(
    owned: PersistentSetFragment<K>, frame: PersistentSetFragment<K>, set: ISet<K>, key: K,
)
    requires
        PersistentSetFragment::op(owned, frame) == persistent_set_frag(set),
        owned.at(key) == Some(AgreementRA::Agree(())),
    ensures
        set.contains(key),
{
    assert(PersistentSetFragment::op(owned, frame).at(key) == persistent_set_frag(set).at(key));
}

/// The caller retains a persistent observation of the whole added set; every
/// borrowed observation in the frame survives this union.
pub proof fn persistent_set_union_frame<K>(
    owned: PersistentSetFragment<K>, frame: PersistentSetFragment<K>, set: ISet<K>, added: ISet<K>,
)
    requires
        PersistentSetFragment::op(owned, frame) == persistent_set_frag(set),
    ensures
        PersistentSetFragment::op(
            PersistentSetFragment::op(owned, persistent_set_frag(added)), frame,
        ) == persistent_set_frag(set.union(added)),
{
    PersistentSetFragment::associative(owned, persistent_set_frag(added), frame);
    PersistentSetFragment::commutative(persistent_set_frag(added), frame);
    PersistentSetFragment::associative(owned, frame, persistent_set_frag(added));
    persistent_set_join(set, added);
}

} // verus!
